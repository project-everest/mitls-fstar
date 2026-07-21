module TLS13.Impl.Client.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module CL = TLS13.ConnectionLog
module CPI = Common.ProtocolImplementation
module CP = TLS13.Impl.Client.CanonicalProtocol
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Spec.Endpoint.Wire
module CChannel = TLS13.Impl.Client.ChannelImplementation
module DC = TLS13.Impl.Client.Driver.Connect
module DClose = TLS13.Impl.Client.Driver.Close
module DNew = TLS13.Impl.Client.Driver.New
module DR = TLS13.Impl.Client.Driver.Receive
module DS = TLS13.Impl.Client.Driver.State
module DSend = TLS13.Impl.Client.Driver.Send
module EAPI = TLS13.Spec.Endpoint.API
module L = TLS13.Impl.Messages
module SZ = FStar.SizeT
module TChannel = TLS13.Impl.Channel
module U16 = FStar.UInt16
module U8 = FStar.UInt8

fn new_client
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_hostname_len /\
                 SZ.v trust_anchors_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_trust_anchors_len)
  returns result: client_driver
  ensures pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          DS.client_driver_live
            result
            (CR.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds) **
          pure (CT.client_state_correct
            (CR.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds) /\
                CT.client_end_to_end_invariant
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds))
{
  DNew.new_client
    server_name
    server_name_len
    trust_anchors
    trust_anchors_len
    validation_time_seconds
}

fn connect
  (d:client_driver)
  (connect_host:array U8.t)
  (connect_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires DS.client_driver_live d 'st0 **
           pts_to connect_host 'connect_host_bytes **
           pure (B.length 'connect_host_bytes == SZ.v connect_host_len)
  returns status:driver_workflow_status
  ensures pts_to connect_host 'connect_host_bytes **
          (match status with
           | DS.DriverWorkflowOk ->
             exists* raw_received raw_sent app_log.
               DS.client_channel_inv d raw_received raw_sent app_log
           | _ ->
             exists* st1. DS.client_driver_closed d st1)
{
  let status =
    DC.run d connect_host connect_host_len port local_fuel fuel;
  match status {
    DS.DriverWorkflowOk -> {
      with st1 received sent.
        assert (DS.client_driver_connected d st1 received sent);
      CChannel.pack_connected_channel
        d
        (Ghost.hide st1)
        (Ghost.hide received)
        (Ghost.hide sent);
      DS.DriverWorkflowOk
    }
    DS.DriverWorkflowNeedMoreInput -> { DS.DriverWorkflowNeedMoreInput }
    DS.DriverWorkflowStepFailed -> { DS.DriverWorkflowStepFailed }
    DS.DriverWorkflowExhausted -> { DS.DriverWorkflowExhausted }
    DS.DriverWorkflowClosed -> { DS.DriverWorkflowClosed }
    DS.DriverWorkflowPayloadTooLarge -> { DS.DriverWorkflowPayloadTooLarge }
    DS.DriverWorkflowOutputBufferTooSmall -> {
      DS.DriverWorkflowOutputBufferTooSmall
    }
  }
}

fn send
  (d:client_driver)
  (raw_received0:Ghost.erased B.bytes)
  (raw_sent0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (payload:array U8.t)
  (payload_bytes:Ghost.erased B.bytes)
  (payload_len:SZ.t)
  requires DS.client_channel_inv
             d
             (Ghost.reveal raw_received0)
             (Ghost.reveal raw_sent0)
             (Ghost.reveal app_log0) **
           pts_to payload (Ghost.reveal payload_bytes) **
           pure (B.length (Ghost.reveal payload_bytes) == SZ.v payload_len)
  returns status:driver_workflow_status
  ensures exists* raw_received1 raw_sent1 app_log1.
          DS.client_channel_inv d raw_received1 raw_sent1 app_log1 **
          pts_to payload (Ghost.reveal payload_bytes) **
          pure (
            CI.send_transition
              channel_message_of_bytes
              channel_send_succeeded
              status
              (Ghost.reveal payload_bytes)
              (Ghost.reveal raw_received0)
              (Ghost.reveal raw_sent0)
              (Ghost.reveal app_log0)
              raw_received1
              raw_sent1
              app_log1)
{
  CChannel.take_channel_snapshot
    d raw_received0 raw_sent0 app_log0;
  CChannel.open_channel_invariant
    d raw_received0 raw_sent0 app_log0;
  with st0 transport_received0 transport_sent0.
    assert (DS.client_driver_connected
      d st0 transport_received0 transport_sent0);
  let status = DSend.run d payload payload_len;
  with st1 transport_received1 transport_sent1.
    assert (DS.client_driver_connected
      d st1 transport_received1 transport_sent1 **
      pts_to payload (Ghost.reveal payload_bytes));
  assert (pure (DS.client_driver_send_correct
    st0
    st1
    status
    (Ghost.reveal payload_bytes)
    transport_sent0
    transport_sent1));
  CChannel.lemma_driver_send_application_log
    st0
    st1
    status
    (Ghost.reveal payload_bytes)
    transport_sent0
    transport_sent1;
  CChannel.pack_connected_channel_invariant
    d
    (Ghost.hide st1)
    (Ghost.hide transport_received1)
    (Ghost.hide transport_sent1);
  CChannel.recall_channel_snapshot
    d
    raw_received0
    raw_sent0
    app_log0
    (Ghost.hide st1.CS.cs_wire_log.CL.raw_received)
    (Ghost.hide st1.CS.cs_wire_log.CL.raw_sent)
    (Ghost.hide (TChannel.application_log st1));
  drop_ (DS.client_channel_snapshot
    d
    (Ghost.reveal raw_received0)
    (Ghost.reveal raw_sent0)
    (Ghost.reveal app_log0));
  assert (
    DS.client_channel_inv
      d
      st1.CS.cs_wire_log.CL.raw_received
      st1.CS.cs_wire_log.CL.raw_sent
      (TChannel.application_log st1) **
    pts_to payload (Ghost.reveal payload_bytes) **
    pure (CI.send_transition
      channel_message_of_bytes
      channel_send_succeeded
      status
      (Ghost.reveal payload_bytes)
      (Ghost.reveal raw_received0)
      (Ghost.reveal raw_sent0)
      (Ghost.reveal app_log0)
      st1.CS.cs_wire_log.CL.raw_received
      st1.CS.cs_wire_log.CL.raw_sent
      (TChannel.application_log st1)));
  status
}

fn receive
  (d:client_driver)
  (raw_received0:Ghost.erased B.bytes)
  (raw_sent0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (out:array U8.t)
  (old_output:Ghost.erased B.bytes)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires DS.client_channel_inv
             d
             (Ghost.reveal raw_received0)
             (Ghost.reveal raw_sent0)
             (Ghost.reveal app_log0) **
           pts_to out (Ghost.reveal old_output) **
           pure (B.length (Ghost.reveal old_output) == SZ.v out_len)
  returns result:client_receive_result
  ensures exists* raw_received1 raw_sent1 app_log1 output.
          DS.client_channel_inv d raw_received1 raw_sent1 app_log1 **
          pts_to out output **
          pure (
            B.length output == SZ.v out_len /\
            SZ.v result.DS.client_receive_len <= SZ.v out_len /\
            CI.receive_transition
              channel_message_of_bytes
              channel_receive_succeeded
              channel_receive_length
              result
              output
              (Ghost.reveal raw_received0)
              (Ghost.reveal raw_sent0)
              (Ghost.reveal app_log0)
              raw_received1
              raw_sent1
              app_log1)
{
  let output_fits = SZ.lte DS.driver_app_out_capacity out_len;
  if output_fits {
    CChannel.take_channel_snapshot
      d raw_received0 raw_sent0 app_log0;
    CChannel.open_channel_invariant
      d raw_received0 raw_sent0 app_log0;
    with st0 transport_received0 transport_sent0.
      assert (DS.client_driver_connected
        d st0 transport_received0 transport_sent0);
    assert (pure (
      L.max_record_fragment_len <= SZ.v DS.driver_app_out_capacity));
    assert (pure (L.max_record_fragment_len <= SZ.v out_len));
    let result = DR.run d out out_len local_fuel fuel;
    with st1 transport_received1 transport_sent1 output.
      assert (DS.client_driver_connected
                d st1 transport_received1 transport_sent1 **
              pts_to out output);
    assert (pure (TChannel.application_log st1 ==
      (if result.client_receive_status == DS.DriverWorkflowOk
       then
         CI.append_received
           (TChannel.application_log st0)
           (FStar.Seq.slice output 0 (SZ.v result.client_receive_len))
       else TChannel.application_log st0)));
    CChannel.pack_connected_channel_invariant
      d
      (Ghost.hide st1)
      (Ghost.hide transport_received1)
      (Ghost.hide transport_sent1);
    CChannel.recall_channel_snapshot
      d
      raw_received0
      raw_sent0
      app_log0
      (Ghost.hide st1.CS.cs_wire_log.CL.raw_received)
      (Ghost.hide st1.CS.cs_wire_log.CL.raw_sent)
      (Ghost.hide (TChannel.application_log st1));
    drop_ (DS.client_channel_snapshot
      d
      (Ghost.reveal raw_received0)
      (Ghost.reveal raw_sent0)
      (Ghost.reveal app_log0));
    assert (
      DS.client_channel_inv
        d
        st1.CS.cs_wire_log.CL.raw_received
        st1.CS.cs_wire_log.CL.raw_sent
        (TChannel.application_log st1) **
      pts_to out output **
      pure (
        CI.receive_transition
          channel_message_of_bytes
          channel_receive_succeeded
          channel_receive_length
          result
          output
          (Ghost.reveal raw_received0)
          (Ghost.reveal raw_sent0)
          (Ghost.reveal app_log0)
          st1.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_sent
          (TChannel.application_log st1)));
    result
  } else {
    let result = {
      DS.client_receive_status = DS.DriverWorkflowOutputBufferTooSmall;
      DS.client_receive_len = 0sz;
    };
    assert (pure (CPI.histories_ahead
      (Ghost.reveal raw_received0)
      (Ghost.reveal raw_sent0)
      (Ghost.reveal raw_received0)
      (Ghost.reveal raw_sent0)));
    assert (
      DS.client_channel_inv
        d
        (Ghost.reveal raw_received0)
        (Ghost.reveal raw_sent0)
        (Ghost.reveal app_log0) **
      pts_to out (Ghost.reveal old_output) **
      pure (
        CI.receive_transition
          channel_message_of_bytes
          channel_receive_succeeded
          channel_receive_length
          result
          (Ghost.reveal old_output)
          (Ghost.reveal raw_received0)
          (Ghost.reveal raw_sent0)
          (Ghost.reveal app_log0)
          (Ghost.reveal raw_received0)
          (Ghost.reveal raw_sent0)
          (Ghost.reveal app_log0)));
    result
  }
}

fn close
  (d:client_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (wait_for_peer:bool)
  (fuel:SZ.t)
  requires DS.client_channel_inv
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log)
  returns status:driver_workflow_status
  ensures exists* st1.
          DS.client_driver_closed d st1 **
          pure (exists st0 st_close_notify.
            st1.CS.cs_model.CS.model_config ==
              st0.CS.cs_model.CS.model_config /\
            DS.client_driver_close_correct
              st0
              st_close_notify
              status
              wait_for_peer)
{
  CChannel.open_channel_invariant
    d raw_received raw_sent app_log;
  DClose.run d wait_for_peer fuel
}

fn abort
  (d:client_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires DS.client_channel_inv
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log)
  ensures exists* st. DS.client_driver_closed d st
{
  CChannel.open_channel_invariant
    d raw_received raw_sent app_log;
  DClose.abort d
}

fn free (d:client_driver)
  requires DS.client_driver_closed d 'st
  ensures client_driver_released d 'st
{
  unfold (DS.client_driver_closed d 'st);
  rewrite (TLS13.Impl.Client.connection_exactly
    d.DS.client_driver_client
    'st)
    as (CR.connection_exactly d.DS.client_driver_client 'st);
  CR.free_connection d.DS.client_driver_client;
  fold (client_driver_released d 'st);
}

noextract
let client_channel_implementation
  : CI.channel_implementation
      DS.client_driver
      CP.canonical_client
      CS.connection_state
      CW.wire_message
      CTypes.client_local_event
      EAPI.local_output
      B.bytes
      DS.driver_workflow_status
      DS.client_receive_result
      CP.client_protocol_implementation
  =
  {
    CI.ci_protocol_impl = DS.client_driver_canonical;
    CI.ci_project = TChannel.application_log;
    CI.ci_message_of_bytes = channel_message_of_bytes;
    CI.ci_channel_inv = DS.client_channel_inv;
    CI.ci_snapshot = DS.client_channel_snapshot;
    CI.ci_send_succeeded = channel_send_succeeded;
    CI.ci_receive_succeeded = channel_receive_succeeded;
    CI.ci_receive_length = channel_receive_length;
    CI.ci_invariant_valid = CChannel.channel_invariant_valid;
    CI.ci_take_snapshot = CChannel.take_channel_snapshot;
    CI.ci_recall_snapshot = CChannel.recall_channel_snapshot;
    CI.ci_send = send;
    CI.ci_receive = receive;
  }
