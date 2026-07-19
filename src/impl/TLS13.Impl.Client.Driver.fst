module TLS13.Impl.Client.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module CL = TLS13.ConnectionLog
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module CChannel = TLS13.Impl.Client.ChannelImplementation
module DC = TLS13.Impl.Client.Driver.Connect
module DClose = TLS13.Impl.Client.Driver.Close
module DNew = TLS13.Impl.Client.Driver.New
module DR = TLS13.Impl.Client.Driver.Receive
module DS = TLS13.Impl.Client.Driver.State
module DSend = TLS13.Impl.Client.Driver.Send
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
  ensures exists* st1.
          pts_to connect_host 'connect_host_bytes **
          (match status with
           | DS.DriverWorkflowOk ->
             exists* received sent.
               DS.client_driver_connected d st1 received sent **
               pure (DS.client_driver_application_ready st1 /\
                     st1.CS.cs_model.CS.model_config ==
                       'st0.CS.cs_model.CS.model_config /\
                     DS.client_driver_sent_log_exact st1 sent /\
                     DS.client_driver_received_log_accounted st1 received /\
                     DS.client_driver_received_log_exact_prefix st1 received /\
                     DS.client_driver_received_no_read_ahead st1 received)
           | _ ->
             DS.client_driver_closed d st1)
{
  DC.run d connect_host connect_host_len port local_fuel fuel
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
  CChannel.pack_connected_after_send
    d
    status
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
  (out:array U8.t)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires DS.client_driver_connected d 'st0 'received0 'sent0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns result:client_receive_result
  ensures exists* st1 received1 sent1 out_bytes.
          DS.client_driver_connected d st1 received1 sent1 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v result.DS.client_receive_len <= SZ.v out_len /\
                st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config /\
                DS.client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0) /\
                DS.client_driver_received_log_accounted
                  'st0
                  (Ghost.reveal 'received0) /\
                DS.client_driver_sent_log_exact st1 sent1 /\
                DS.client_driver_received_log_accounted st1 received1 /\
                (exists obs app_out.
                  DS.client_driver_receive_correct
                    'st0
                    st1
                    result
                    obs
                    app_out
                    out_bytes))
{
  DR.run d out out_len local_fuel fuel
}

fn close
  (d:client_driver)
  (wait_for_peer:bool)
  (fuel:SZ.t)
  requires DS.client_driver_connected d 'st0 'received0 'sent0
  returns status:driver_workflow_status
  ensures exists* st1.
          DS.client_driver_closed d st1 **
          pure (st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config /\
                DS.client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0) /\
                DS.client_driver_received_log_accounted
                  'st0
                  (Ghost.reveal 'received0) /\
                (exists st_close_notify.
                  DS.client_driver_close_correct
                    'st0
                    st_close_notify
                    status
                    wait_for_peer))
{
  DClose.run d wait_for_peer fuel
}

fn abort
  (d:client_driver)
  requires DS.client_driver_connected d 'st0 'received0 'sent0
  ensures DS.client_driver_closed d 'st0
{
  DClose.abort d
}
