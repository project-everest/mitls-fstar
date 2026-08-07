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
module O = TLS13.OpenSSL
module SZ = FStar.SizeT
module TChannel = TLS13.Impl.Channel
module U16 = FStar.UInt16
module U8 = FStar.UInt8

fn new_auth_config
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len)
  returns config: client_auth_config
  ensures pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          O.is_auth_config
            config
            (Ghost.reveal 'server_name_bytes)
            (Ghost.reveal 'trust_anchors_bytes)
            validation_time_seconds
{
  O.auth_config_new
    server_name
    server_name_len
    trust_anchors
    trust_anchors_len
    validation_time_seconds
}

fn free_auth_config (config:client_auth_config)
  requires O.is_auth_config
    config
    'server_name_bytes
    'trust_anchors_bytes
    'validation_time_seconds
  ensures emp
{
  O.auth_config_free config
}

fn new_client_with_auth_config
  (config:client_auth_config)
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires O.is_auth_config
             config
             (Ghost.reveal 'server_name_bytes)
             (Ghost.reveal 'trust_anchors_bytes)
             validation_time_seconds **
           pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_hostname_len /\
                 SZ.v trust_anchors_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_trust_anchors_len)
  returns result: client_driver
  ensures O.is_auth_config
            config
            (Ghost.reveal 'server_name_bytes)
            (Ghost.reveal 'trust_anchors_bytes)
            validation_time_seconds **
          pts_to server_name 'server_name_bytes **
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
  DNew.new_client_with_auth_config
    config
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
             exists* wire_received wire_sent pending app_log.
               DS.client_channel_inv d wire_received wire_sent pending app_log
           | _ ->
             exists* st1. DS.client_driver_closed d st1)
{
  let status =
    DC.run d connect_host connect_host_len port local_fuel fuel;
  match status {
    DS.DriverWorkflowOk -> {
      with st1 received sent.
        assert (DS.client_driver_connected d st1 received sent);
      assert (pure (DS.client_driver_application_ready st1));
      assert (pure (st1.CS.cs_model.CS.model_control ==
        CS.ControlApplicationData));
      assert (pure (CT.connection_control_not_failed st1));
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

inline_for_extraction
let channel_send_reusable_runtime
  (status:driver_workflow_status)
  : bool =
  match status with
  | DS.DriverWorkflowOk -> true
  | DS.DriverWorkflowPayloadTooLarge -> true
  | _ -> false

inline_for_extraction
let channel_receive_reusable_runtime
  (result:client_receive_result)
  : bool =
  match result.DS.client_receive_status with
  | DS.DriverWorkflowOk -> true
  | DS.DriverWorkflowNeedMoreInput -> true
  | DS.DriverWorkflowExhausted -> true
  | DS.DriverWorkflowOutputBufferTooSmall -> true
  | _ -> false

(* Flush an outstanding mandated KeyUpdate reply (RFC 8446 4.6.3).

   The peer's [update_requested] sets [app_key_update_response_pending] during a
   receive, but `BN.drive` -- the connected-receive path -- does not run local
   actions, so the scheduler's [LocalSendKeyUpdate] arm can never fire while the
   connection is at [ControlApplicationData].  This is the direct path that
   discharges the obligation instead; it is run at the *head* of a receive, so
   that a send failure leaves the application log untouched and the caller can
   report the failure without violating [CI.receive_transition]'s log equation.

   The application log is preserved on both branches: a KeyUpdate event has
   empty application sent/received deltas, and so does the [LocalFail] event of
   a failed step. *)
fn flush_key_update_response
  (d:client_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  requires DS.client_channel_inv
             d
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal pending0)
             (Ghost.reveal app_log0)
  returns status:driver_workflow_status
  ensures exists* wire_received1 wire_sent1 pending1.
          (if channel_send_reusable status
           then
             DS.client_channel_inv
               d wire_received1 wire_sent1 pending1 (Ghost.reveal app_log0)
           else
             DS.client_channel_terminal
               d wire_received1 wire_sent1 (Ghost.reveal app_log0)) **
          pure (
            CPI.histories_ahead
              (Ghost.reveal wire_received0)
              (Ghost.reveal wire_sent0)
              wire_received1
              wire_sent1)
{
  CChannel.take_channel_snapshot
    d wire_received0 wire_sent0 pending0 app_log0;
  CChannel.open_channel_invariant
    d wire_received0 wire_sent0 pending0 app_log0;
  with st0.
    assert (DS.client_driver_connected
      d st0 (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0));
  assert (pure (CT.connection_control_not_failed st0));
  assert (pure ((Ghost.reveal app_log0) == TChannel.application_log st0));
  let pending = DSend.query_key_update_response_pending d;
  if pending {
    let status = DSend.run_key_update d false;
    with st1 transport_received1 transport_sent1.
      assert (DS.client_driver_connected
        d st1 transport_received1 transport_sent1);
    DS.lemma_client_driver_key_update_preserves_app_log
      st0
      st1
      status
      CT.LocalSendKeyUpdate
      (Ghost.reveal wire_sent0)
      transport_sent1;
    assert (pure (TChannel.application_log st1 == Ghost.reveal app_log0));
    CChannel.recall_tcp_history
      d
      wire_received0
      wire_sent0
      app_log0
      (Ghost.hide st1)
      (Ghost.hide transport_received1)
      (Ghost.hide transport_sent1);
    drop_ (DS.client_channel_snapshot
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal app_log0));
    let reusable = channel_send_reusable_runtime status;
    assert (pure (reusable == channel_send_reusable status));
    if reusable {
      assert (pure (status == DS.DriverWorkflowOk \/
                    status == DS.DriverWorkflowPayloadTooLarge));
      assert (pure (CT.connection_control_not_failed st1));
      CChannel.pack_connected_channel_invariant
        d
        (Ghost.hide st1)
        (Ghost.hide transport_received1)
        (Ghost.hide transport_sent1);
      with pending1.
        assert (DS.client_channel_inv
          d transport_received1 transport_sent1 pending1
          (TChannel.application_log st1));
      rewrite (DS.client_channel_inv
        d transport_received1 transport_sent1 pending1
        (TChannel.application_log st1))
        as (if channel_send_reusable status
            then DS.client_channel_inv
              d transport_received1 transport_sent1 pending1
              (Ghost.reveal app_log0)
            else DS.client_channel_terminal
              d transport_received1 transport_sent1
              (Ghost.reveal app_log0));
      status
    } else {
      CChannel.pack_connected_channel_terminal
        d
        (Ghost.hide st1)
        (Ghost.hide transport_received1)
        (Ghost.hide transport_sent1);
      rewrite (DS.client_channel_terminal
        d transport_received1 transport_sent1
        (TChannel.application_log st1))
        as (if channel_send_reusable status
            then DS.client_channel_inv
              d transport_received1 transport_sent1 transport_received1
              (Ghost.reveal app_log0)
            else DS.client_channel_terminal
              d transport_received1 transport_sent1
              (Ghost.reveal app_log0));
      status
    }
  } else {
    CChannel.pack_connected_channel_invariant
      d
      (Ghost.hide st0)
      (Ghost.hide (Ghost.reveal wire_received0))
      (Ghost.hide (Ghost.reveal wire_sent0));
    drop_ (DS.client_channel_snapshot
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal app_log0));
    CPI.lemma_bytes_extends_refl (Ghost.reveal wire_received0);
    CPI.lemma_bytes_extends_refl (Ghost.reveal wire_sent0);
    with pending1.
      assert (DS.client_channel_inv
        d
        (Ghost.reveal wire_received0)
        (Ghost.reveal wire_sent0)
        pending1
        (TChannel.application_log st0));
    rewrite (DS.client_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      pending1
      (TChannel.application_log st0))
      as (if channel_send_reusable DS.DriverWorkflowOk
          then DS.client_channel_inv
            d
            (Ghost.reveal wire_received0)
            (Ghost.reveal wire_sent0)
            pending1
            (Ghost.reveal app_log0)
          else DS.client_channel_terminal
            d
            (Ghost.reveal wire_received0)
            (Ghost.reveal wire_sent0)
            (Ghost.reveal app_log0));
    DS.DriverWorkflowOk
  }
}

fn channel_send_core
  (d:client_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (payload:array U8.t)
  (payload_bytes:Ghost.erased B.bytes)
  (payload_len:SZ.t)
  requires DS.client_channel_inv
             d
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal pending0)
             (Ghost.reveal app_log0) **
           pts_to payload (Ghost.reveal payload_bytes) **
           pure (B.length (Ghost.reveal payload_bytes) == SZ.v payload_len)
  returns status:driver_workflow_status
  ensures exists* wire_received1 wire_sent1 pending1 app_log1.
          (if channel_send_reusable status
           then
             DS.client_channel_inv d wire_received1 wire_sent1 pending1 app_log1
           else
             DS.client_channel_terminal d wire_received1 wire_sent1 app_log1) **
          pts_to payload (Ghost.reveal payload_bytes) **
          pure (
            CI.send_transition
              channel_message_of_bytes
              channel_send_succeeded
              status
              (Ghost.reveal payload_bytes)
              (Ghost.reveal wire_received0)
              (Ghost.reveal wire_sent0)
              (Ghost.reveal app_log0)
              wire_received1
              wire_sent1
              app_log1)
{
  CChannel.take_channel_snapshot
    d wire_received0 wire_sent0 pending0 app_log0;
  CChannel.open_channel_invariant
    d wire_received0 wire_sent0 pending0 app_log0;
  with st0.
    assert (DS.client_driver_connected
      d st0 (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0));
  assert (pure (CT.connection_control_not_failed st0));
  assert (pure ((Ghost.reveal app_log0) == TChannel.application_log st0));
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
    (Ghost.reveal wire_sent0)
    transport_sent1));
  CChannel.recall_tcp_history
    d
    wire_received0
    wire_sent0
    app_log0
    (Ghost.hide st1)
    (Ghost.hide transport_received1)
    (Ghost.hide transport_sent1);
  drop_ (DS.client_channel_snapshot
    d
    (Ghost.reveal wire_received0)
    (Ghost.reveal wire_sent0)
    (Ghost.reveal app_log0));
  CChannel.lemma_driver_send_application_log
    st0
    st1
    status
    (Ghost.reveal payload_bytes)
    (Ghost.reveal wire_sent0)
    transport_sent1;
  let reusable = channel_send_reusable_runtime status;
  assert (pure (reusable == channel_send_reusable status));
  if reusable {
    assert (pure (status == DS.DriverWorkflowOk \/
                  status == DS.DriverWorkflowPayloadTooLarge));
    assert (pure (CT.connection_control_not_failed st1));
    CChannel.pack_connected_channel_invariant
      d
      (Ghost.hide st1)
      (Ghost.hide transport_received1)
      (Ghost.hide transport_sent1);
    with pending1.
      assert (DS.client_channel_inv
        d transport_received1 transport_sent1 pending1
        (TChannel.application_log st1));
    assert (pure (CI.send_transition
      channel_message_of_bytes
      channel_send_succeeded
      status
      (Ghost.reveal payload_bytes)
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal app_log0)
      transport_received1
      transport_sent1
      (TChannel.application_log st1)));
    rewrite (DS.client_channel_inv
      d transport_received1 transport_sent1 pending1
      (TChannel.application_log st1))
      as (if channel_send_reusable status
          then DS.client_channel_inv
            d transport_received1 transport_sent1 pending1
            (TChannel.application_log st1)
          else DS.client_channel_terminal
            d transport_received1 transport_sent1
            (TChannel.application_log st1));
    status
  } else {
    CChannel.pack_connected_channel_terminal
      d
      (Ghost.hide st1)
      (Ghost.hide transport_received1)
      (Ghost.hide transport_sent1);
    assert (pure (CI.send_transition
      channel_message_of_bytes
      channel_send_succeeded
      status
      (Ghost.reveal payload_bytes)
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal app_log0)
      transport_received1
      transport_sent1
      (TChannel.application_log st1)));
    rewrite (DS.client_channel_terminal
      d transport_received1 transport_sent1
      (TChannel.application_log st1))
      as (if channel_send_reusable status
          then DS.client_channel_inv
            d transport_received1 transport_sent1 transport_received1
            (TChannel.application_log st1)
          else DS.client_channel_terminal
            d transport_received1 transport_sent1
            (TChannel.application_log st1));
    status
  }
}

(* Send with the mandated KeyUpdate reply flushed first.

   RFC 8446 4.6.3 requires an endpoint that received [update_requested] to send
   its own KeyUpdate *before* its next application-data record, so this -- not
   the receive path -- is the obligation's real deadline.  Composition with
   [CI.send_transition] works for the same reason as on the receive side: the
   inserted record only extends the wire history, and a KeyUpdate leaves the
   application log alone, so a failed flush can be reported as a failed send
   with the log unchanged. *)
fn channel_send
  (d:client_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (payload:array U8.t)
  (payload_bytes:Ghost.erased B.bytes)
  (payload_len:SZ.t)
  requires DS.client_channel_inv
             d
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal pending0)
             (Ghost.reveal app_log0) **
           pts_to payload (Ghost.reveal payload_bytes) **
           pure (B.length (Ghost.reveal payload_bytes) == SZ.v payload_len)
  returns status:driver_workflow_status
  ensures exists* wire_received1 wire_sent1 pending1 app_log1.
          (if channel_send_reusable status
           then
             DS.client_channel_inv d wire_received1 wire_sent1 pending1 app_log1
           else
             DS.client_channel_terminal d wire_received1 wire_sent1 app_log1) **
          pts_to payload (Ghost.reveal payload_bytes) **
          pure (
            CI.send_transition
              channel_message_of_bytes
              channel_send_succeeded
              status
              (Ghost.reveal payload_bytes)
              (Ghost.reveal wire_received0)
              (Ghost.reveal wire_sent0)
              (Ghost.reveal app_log0)
              wire_received1
              wire_sent1
              app_log1)
{
  let flush_status =
    flush_key_update_response d wire_received0 wire_sent0 pending0 app_log0;
  with wire_received1 wire_sent1 pending1.
    assert (if channel_send_reusable flush_status
            then
              DS.client_channel_inv
                d wire_received1 wire_sent1 pending1 (Ghost.reveal app_log0)
            else
              DS.client_channel_terminal
                d wire_received1 wire_sent1 (Ghost.reveal app_log0));
  let flushed = channel_send_reusable_runtime flush_status;
  assert (pure (flushed == channel_send_reusable flush_status));
  if flushed {
    rewrite (if channel_send_reusable flush_status
             then
               DS.client_channel_inv
                 d wire_received1 wire_sent1 pending1 (Ghost.reveal app_log0)
             else
               DS.client_channel_terminal
                 d wire_received1 wire_sent1 (Ghost.reveal app_log0))
      as (DS.client_channel_inv
            d wire_received1 wire_sent1 pending1 (Ghost.reveal app_log0));
    let status =
      channel_send_core
        d
        (Ghost.hide wire_received1)
        (Ghost.hide wire_sent1)
        (Ghost.hide pending1)
        app_log0
        payload
        payload_bytes
        payload_len;
    with wire_received2 wire_sent2 pending2 app_log2.
      assert ((if channel_send_reusable status
               then
                 DS.client_channel_inv
                   d wire_received2 wire_sent2 pending2 app_log2
               else
                 DS.client_channel_terminal
                   d wire_received2 wire_sent2 app_log2) **
              pts_to payload (Ghost.reveal payload_bytes));
    CPI.lemma_bytes_extends_trans
      (Ghost.reveal wire_received0) wire_received1 wire_received2;
    CPI.lemma_bytes_extends_trans
      (Ghost.reveal wire_sent0) wire_sent1 wire_sent2;
    assert (pure (CI.send_transition
      channel_message_of_bytes
      channel_send_succeeded
      status
      (Ghost.reveal payload_bytes)
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal app_log0)
      wire_received2
      wire_sent2
      app_log2));
    status
  } else {
    rewrite (if channel_send_reusable flush_status
             then
               DS.client_channel_inv
                 d wire_received1 wire_sent1 pending1 (Ghost.reveal app_log0)
             else
               DS.client_channel_terminal
                 d wire_received1 wire_sent1 (Ghost.reveal app_log0))
      as (DS.client_channel_terminal
            d wire_received1 wire_sent1 (Ghost.reveal app_log0));
    assert (pure (CI.send_transition
      channel_message_of_bytes
      channel_send_succeeded
      flush_status
      (Ghost.reveal payload_bytes)
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal app_log0)
      wire_received1
      wire_sent1
      (Ghost.reveal app_log0)));
    rewrite (DS.client_channel_terminal
      d wire_received1 wire_sent1 (Ghost.reveal app_log0))
      as (if channel_send_reusable flush_status
          then DS.client_channel_inv
            d wire_received1 wire_sent1 pending1 (Ghost.reveal app_log0)
          else DS.client_channel_terminal
            d wire_received1 wire_sent1 (Ghost.reveal app_log0));
    flush_status
  }
}

fn channel_receive_core
  (d:client_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (out:array U8.t)
  (old_output:Ghost.erased B.bytes)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires DS.client_channel_inv
             d
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal pending0)
             (Ghost.reveal app_log0) **
           pts_to out (Ghost.reveal old_output) **
           pure (B.length (Ghost.reveal old_output) == SZ.v out_len)
  returns result:client_receive_result
  ensures exists* wire_received1 wire_sent1 pending1 app_log1 output.
          (if channel_receive_reusable result
           then
             DS.client_channel_inv d wire_received1 wire_sent1 pending1 app_log1
           else
             DS.client_channel_terminal d wire_received1 wire_sent1 app_log1) **
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
              (Ghost.reveal wire_received0)
              (Ghost.reveal wire_sent0)
              (Ghost.reveal app_log0)
              wire_received1
              wire_sent1
              app_log1)
{
  let output_fits = SZ.lte DS.driver_app_out_capacity out_len;
  if output_fits {
    CChannel.take_channel_snapshot
      d wire_received0 wire_sent0 pending0 app_log0;
    CChannel.open_channel_invariant
      d wire_received0 wire_sent0 pending0 app_log0;
    with st0.
      assert (DS.client_driver_connected
        d st0 (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0));
    assert (pure (CT.connection_control_not_failed st0));
    assert (pure ((Ghost.reveal app_log0) == TChannel.application_log st0));
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
    CChannel.recall_tcp_history
      d
      wire_received0
      wire_sent0
      app_log0
      (Ghost.hide st1)
      (Ghost.hide transport_received1)
      (Ghost.hide transport_sent1);
    drop_ (DS.client_channel_snapshot
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal app_log0));
    let reusable = channel_receive_reusable_runtime result;
    assert (pure (reusable == channel_receive_reusable result));
    if reusable {
      assert (pure (result.DS.client_receive_status <> DS.DriverWorkflowStepFailed /\
                    result.DS.client_receive_status <> DS.DriverWorkflowClosed));
      assert (pure (CT.connection_control_not_failed st1));
      CChannel.pack_connected_channel_invariant
        d
        (Ghost.hide st1)
        (Ghost.hide transport_received1)
        (Ghost.hide transport_sent1);
      with pending1.
        assert (DS.client_channel_inv
          d transport_received1 transport_sent1 pending1
          (TChannel.application_log st1));
      assert (pure (CI.receive_transition
        channel_message_of_bytes
        channel_receive_succeeded
        channel_receive_length
        result
        output
        (Ghost.reveal wire_received0)
        (Ghost.reveal wire_sent0)
        (Ghost.reveal app_log0)
        transport_received1
        transport_sent1
        (TChannel.application_log st1)));
      rewrite (DS.client_channel_inv
        d transport_received1 transport_sent1 pending1
        (TChannel.application_log st1))
        as (if channel_receive_reusable result
            then DS.client_channel_inv
              d transport_received1 transport_sent1 pending1
              (TChannel.application_log st1)
            else DS.client_channel_terminal
              d transport_received1 transport_sent1
              (TChannel.application_log st1));
      result
    } else {
      CChannel.pack_connected_channel_terminal
        d
        (Ghost.hide st1)
        (Ghost.hide transport_received1)
        (Ghost.hide transport_sent1);
      assert (pure (CI.receive_transition
        channel_message_of_bytes
        channel_receive_succeeded
        channel_receive_length
        result
        output
        (Ghost.reveal wire_received0)
        (Ghost.reveal wire_sent0)
        (Ghost.reveal app_log0)
        transport_received1
        transport_sent1
        (TChannel.application_log st1)));
      rewrite (DS.client_channel_terminal
        d transport_received1 transport_sent1
        (TChannel.application_log st1))
        as (if channel_receive_reusable result
            then DS.client_channel_inv
              d transport_received1 transport_sent1 transport_received1
              (TChannel.application_log st1)
            else DS.client_channel_terminal
              d transport_received1 transport_sent1
              (TChannel.application_log st1));
      result
    }
  } else {
    let result = {
      DS.client_receive_status = DS.DriverWorkflowOutputBufferTooSmall;
      DS.client_receive_len = 0sz;
    };
    CPI.lemma_bytes_extends_refl (Ghost.reveal wire_received0);
    CPI.lemma_bytes_extends_refl (Ghost.reveal wire_sent0);
    assert (pure (CPI.histories_ahead
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)));
    assert (
      DS.client_channel_inv
        d
        (Ghost.reveal wire_received0)
        (Ghost.reveal wire_sent0)
        (Ghost.reveal pending0)
        (Ghost.reveal app_log0) **
      pts_to out (Ghost.reveal old_output) **
      pure (
        CI.receive_transition
          channel_message_of_bytes
          channel_receive_succeeded
          channel_receive_length
          result
          (Ghost.reveal old_output)
          (Ghost.reveal wire_received0)
          (Ghost.reveal wire_sent0)
          (Ghost.reveal app_log0)
          (Ghost.reveal wire_received0)
          (Ghost.reveal wire_sent0)
          (Ghost.reveal app_log0)));
    rewrite (DS.client_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0))
      as (if channel_receive_reusable result
          then DS.client_channel_inv
            d
            (Ghost.reveal wire_received0)
            (Ghost.reveal wire_sent0)
            (Ghost.reveal pending0)
            (Ghost.reveal app_log0)
          else DS.client_channel_terminal
            d
            (Ghost.reveal wire_received0)
            (Ghost.reveal wire_sent0)
            (Ghost.reveal app_log0));
    result
  }
}

(* Receive with the mandated KeyUpdate reply flushed first.

   Composition is legal because [CI.receive_transition] constrains only the
   *application* log and asks for a prefix relation on the wire histories: the
   extra KeyUpdate record extends [wire_sent] (absorbed by
   [histories_ahead] transitivity) and leaves the application log alone.  A
   failed flush short-circuits with a failed receive result and an unchanged
   application log, which is exactly what the log equation demands of an
   unsuccessful receive. *)
fn channel_receive
  (d:client_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (out:array U8.t)
  (old_output:Ghost.erased B.bytes)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires DS.client_channel_inv
             d
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal pending0)
             (Ghost.reveal app_log0) **
           pts_to out (Ghost.reveal old_output) **
           pure (B.length (Ghost.reveal old_output) == SZ.v out_len)
  returns result:client_receive_result
  ensures exists* wire_received1 wire_sent1 pending1 app_log1 output.
          (if channel_receive_reusable result
           then
             DS.client_channel_inv d wire_received1 wire_sent1 pending1 app_log1
           else
             DS.client_channel_terminal d wire_received1 wire_sent1 app_log1) **
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
              (Ghost.reveal wire_received0)
              (Ghost.reveal wire_sent0)
              (Ghost.reveal app_log0)
              wire_received1
              wire_sent1
              app_log1)
{
  let flush_status =
    flush_key_update_response d wire_received0 wire_sent0 pending0 app_log0;
  with wire_received1 wire_sent1 pending1.
    assert (if channel_send_reusable flush_status
            then
              DS.client_channel_inv
                d wire_received1 wire_sent1 pending1 (Ghost.reveal app_log0)
            else
              DS.client_channel_terminal
                d wire_received1 wire_sent1 (Ghost.reveal app_log0));
  let flushed = channel_send_reusable_runtime flush_status;
  assert (pure (flushed == channel_send_reusable flush_status));
  if flushed {
    rewrite (if channel_send_reusable flush_status
             then
               DS.client_channel_inv
                 d wire_received1 wire_sent1 pending1 (Ghost.reveal app_log0)
             else
               DS.client_channel_terminal
                 d wire_received1 wire_sent1 (Ghost.reveal app_log0))
      as (DS.client_channel_inv
            d wire_received1 wire_sent1 pending1 (Ghost.reveal app_log0));
    let result =
      channel_receive_core
        d
        (Ghost.hide wire_received1)
        (Ghost.hide wire_sent1)
        (Ghost.hide pending1)
        app_log0
        out
        old_output
        out_len
        local_fuel
        fuel;
    with wire_received2 wire_sent2 pending2 app_log2 output.
      assert ((if channel_receive_reusable result
               then
                 DS.client_channel_inv
                   d wire_received2 wire_sent2 pending2 app_log2
               else
                 DS.client_channel_terminal
                   d wire_received2 wire_sent2 app_log2) **
              pts_to out output);
    CPI.lemma_bytes_extends_trans
      (Ghost.reveal wire_received0) wire_received1 wire_received2;
    CPI.lemma_bytes_extends_trans
      (Ghost.reveal wire_sent0) wire_sent1 wire_sent2;
    assert (pure (CI.receive_transition
      channel_message_of_bytes
      channel_receive_succeeded
      channel_receive_length
      result
      output
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal app_log0)
      wire_received2
      wire_sent2
      app_log2));
    result
  } else {
    rewrite (if channel_send_reusable flush_status
             then
               DS.client_channel_inv
                 d wire_received1 wire_sent1 pending1 (Ghost.reveal app_log0)
             else
               DS.client_channel_terminal
                 d wire_received1 wire_sent1 (Ghost.reveal app_log0))
      as (DS.client_channel_terminal
            d wire_received1 wire_sent1 (Ghost.reveal app_log0));
    let result = {
      DS.client_receive_status = DS.DriverWorkflowStepFailed;
      DS.client_receive_len = 0sz;
    };
    assert (pure (CI.receive_transition
      channel_message_of_bytes
      channel_receive_succeeded
      channel_receive_length
      result
      (Ghost.reveal old_output)
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal app_log0)
      wire_received1
      wire_sent1
      (Ghost.reveal app_log0)));
    rewrite (DS.client_channel_terminal
      d wire_received1 wire_sent1 (Ghost.reveal app_log0))
      as (if channel_receive_reusable result
          then DS.client_channel_inv
            d wire_received1 wire_sent1 wire_received1 (Ghost.reveal app_log0)
          else DS.client_channel_terminal
            d wire_received1 wire_sent1 (Ghost.reveal app_log0));
    result
  }
}

(* Channel-level client-initiated KeyUpdate.  Mirrors [channel_send] but with
   an empty payload and no application-log transition: a KeyUpdate carries no
   application message, so the only obligation is that the channel invariant is
   re-established on success and the driver is aborted on failure. *)
fn channel_send_key_update
  (d:client_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (request:bool)
  requires DS.client_channel_inv
             d
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal pending0)
             (Ghost.reveal app_log0)
  returns status:driver_workflow_status
  ensures exists* wire_received1 wire_sent1 pending1 app_log1.
          (if channel_send_reusable status
           then
             DS.client_channel_inv d wire_received1 wire_sent1 pending1 app_log1
           else
             DS.client_channel_terminal d wire_received1 wire_sent1 app_log1)
{
  CChannel.take_channel_snapshot
    d wire_received0 wire_sent0 pending0 app_log0;
  CChannel.open_channel_invariant
    d wire_received0 wire_sent0 pending0 app_log0;
  with st0.
    assert (DS.client_driver_connected
      d st0 (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0));
  assert (pure (CT.connection_control_not_failed st0));
  let status = DSend.run_key_update d request;
  with st1 transport_received1 transport_sent1.
    assert (DS.client_driver_connected
      d st1 transport_received1 transport_sent1);
  CChannel.recall_tcp_history
    d
    wire_received0
    wire_sent0
    app_log0
    (Ghost.hide st1)
    (Ghost.hide transport_received1)
    (Ghost.hide transport_sent1);
  drop_ (DS.client_channel_snapshot
    d
    (Ghost.reveal wire_received0)
    (Ghost.reveal wire_sent0)
    (Ghost.reveal app_log0));
  let reusable = channel_send_reusable_runtime status;
  assert (pure (reusable == channel_send_reusable status));
  if reusable {
    assert (pure (status == DS.DriverWorkflowOk \/
                  status == DS.DriverWorkflowPayloadTooLarge));
    assert (pure (CT.connection_control_not_failed st1));
    CChannel.pack_connected_channel_invariant
      d
      (Ghost.hide st1)
      (Ghost.hide transport_received1)
      (Ghost.hide transport_sent1);
    with pending1.
      assert (DS.client_channel_inv
        d transport_received1 transport_sent1 pending1
        (TChannel.application_log st1));
    rewrite (DS.client_channel_inv
      d transport_received1 transport_sent1 pending1
      (TChannel.application_log st1))
      as (if channel_send_reusable status
          then DS.client_channel_inv
            d transport_received1 transport_sent1 pending1
            (TChannel.application_log st1)
          else DS.client_channel_terminal
            d transport_received1 transport_sent1
            (TChannel.application_log st1));
    status
  } else {
    CChannel.pack_connected_channel_terminal
      d
      (Ghost.hide st1)
      (Ghost.hide transport_received1)
      (Ghost.hide transport_sent1);
    rewrite (DS.client_channel_terminal
      d transport_received1 transport_sent1
      (TChannel.application_log st1))
      as (if channel_send_reusable status
          then DS.client_channel_inv
            d transport_received1 transport_sent1 transport_received1
            (TChannel.application_log st1)
          else DS.client_channel_terminal
            d transport_received1 transport_sent1
            (TChannel.application_log st1));
    status
  }
}

(* Client-initiated KeyUpdate (RFC 8446 4.6.3).  [request] selects the request
   form: [true] sends [update_requested], asking the peer to rotate its own
   sending key in reply; [false] sends [update_not_requested], rotating only our
   write key. *)
fn send_key_update
  (d:client_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (request:bool)
  requires DS.client_channel_inv
             d
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal pending0)
             (Ghost.reveal app_log0)
  returns status:driver_workflow_status
  ensures exists* wire_received1 wire_sent1 pending1 app_log1.
          client_channel_after_operation
            d
            (channel_send_reusable status)
            wire_received1
            wire_sent1
            pending1
            app_log1
{
  let status =
    channel_send_key_update
      d wire_received0 wire_sent0 pending0 app_log0
      request;
  with wire_received1 wire_sent1 pending1 app_log1.
    assert (
      (if channel_send_reusable status
       then
         DS.client_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
       else
         DS.client_channel_terminal
           d wire_received1 wire_sent1 app_log1));
  let reusable = channel_send_reusable_runtime status;
  assert (pure (reusable == channel_send_reusable status));
  if reusable {
    assert (pure (channel_send_reusable status == true));
    rewrite
      (if channel_send_reusable status
       then
         DS.client_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
       else
         DS.client_channel_terminal
           d wire_received1 wire_sent1 app_log1)
      as
      (DS.client_channel_inv
        d wire_received1 wire_sent1 pending1 app_log1);
    rewrite
      (DS.client_channel_inv
        d wire_received1 wire_sent1 pending1 app_log1)
      as
      (client_channel_after_operation
        d
        (channel_send_reusable status)
        wire_received1
        wire_sent1
        pending1
        app_log1);
    status
  } else {
    assert (pure (channel_send_reusable status == false));
    rewrite
      (if channel_send_reusable status
       then
         DS.client_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
       else
         DS.client_channel_terminal
           d wire_received1 wire_sent1 app_log1)
      as
      (DS.client_channel_terminal
        d wire_received1 wire_sent1 app_log1);
    CChannel.open_terminal
      d
      (Ghost.hide wire_received1)
      (Ghost.hide wire_sent1)
      (Ghost.hide app_log1);
    DClose.abort d;
    with st1. assert (DS.client_driver_closed d st1);
    rewrite
      (DS.client_driver_closed d st1)
      as
      (client_driver_closed d st1);
    fold (client_driver_is_closed d);
    rewrite
      (client_driver_is_closed d)
      as
      (client_channel_after_operation
        d
        (channel_send_reusable status)
        wire_received1
        wire_sent1
        pending1
        app_log1);
    status
  }
}

fn send
  (d:client_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (payload:array U8.t)
  (payload_bytes:Ghost.erased B.bytes)
  (payload_len:SZ.t)
  requires DS.client_channel_inv
             d
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal pending0)
             (Ghost.reveal app_log0) **
           pts_to payload (Ghost.reveal payload_bytes) **
           pure (B.length (Ghost.reveal payload_bytes) == SZ.v payload_len)
  returns status:driver_workflow_status
  ensures exists* wire_received1 wire_sent1 pending1 app_log1.
          client_channel_after_operation
            d
            (channel_send_reusable status)
            wire_received1
            wire_sent1
            pending1
            app_log1 **
          pts_to payload (Ghost.reveal payload_bytes) **
          pure (
            CI.send_transition
              channel_message_of_bytes
              channel_send_succeeded
              status
              (Ghost.reveal payload_bytes)
              (Ghost.reveal wire_received0)
              (Ghost.reveal wire_sent0)
              (Ghost.reveal app_log0)
              wire_received1
              wire_sent1
              app_log1)
{
  let status =
    channel_send
      d wire_received0 wire_sent0 pending0 app_log0
      payload payload_bytes payload_len;
  with wire_received1 wire_sent1 pending1 app_log1.
    assert (
      (if channel_send_reusable status
       then
         DS.client_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
       else
         DS.client_channel_terminal
           d wire_received1 wire_sent1 app_log1) **
      pts_to payload (Ghost.reveal payload_bytes) **
      pure (
        CI.send_transition
          channel_message_of_bytes
          channel_send_succeeded
          status
          (Ghost.reveal payload_bytes)
          (Ghost.reveal wire_received0)
          (Ghost.reveal wire_sent0)
          (Ghost.reveal app_log0)
          wire_received1
          wire_sent1
          app_log1));
  let reusable = channel_send_reusable_runtime status;
  assert (pure (reusable == channel_send_reusable status));
  if reusable {
    assert (pure (channel_send_reusable status == true));
    rewrite
      (if channel_send_reusable status
       then
         DS.client_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
       else
         DS.client_channel_terminal
           d wire_received1 wire_sent1 app_log1)
      as
      (DS.client_channel_inv
        d wire_received1 wire_sent1 pending1 app_log1);
    rewrite
      (DS.client_channel_inv
        d wire_received1 wire_sent1 pending1 app_log1)
      as
      (client_channel_after_operation
        d
        (channel_send_reusable status)
        wire_received1
        wire_sent1
        pending1
        app_log1);
    status
  } else {
    assert (pure (channel_send_reusable status == false));
    rewrite
      (if channel_send_reusable status
       then
         DS.client_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
       else
         DS.client_channel_terminal
           d wire_received1 wire_sent1 app_log1)
      as
      (DS.client_channel_terminal
        d wire_received1 wire_sent1 app_log1);
    CChannel.open_terminal
      d
      (Ghost.hide wire_received1)
      (Ghost.hide wire_sent1)
      (Ghost.hide app_log1);
    DClose.abort d;
    with st1. assert (DS.client_driver_closed d st1);
    rewrite
      (DS.client_driver_closed d st1)
      as
      (client_driver_closed d st1);
    fold (client_driver_is_closed d);
    rewrite
      (client_driver_is_closed d)
      as
      (client_channel_after_operation
        d
        (channel_send_reusable status)
        wire_received1
        wire_sent1
        pending1
        app_log1);
    status
  }
}

fn receive
  (d:client_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (out:array U8.t)
  (old_output:Ghost.erased B.bytes)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires DS.client_channel_inv
             d
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal pending0)
             (Ghost.reveal app_log0) **
           pts_to out (Ghost.reveal old_output) **
           pure (B.length (Ghost.reveal old_output) == SZ.v out_len)
  returns result:client_receive_result
  ensures exists* wire_received1 wire_sent1 pending1 app_log1 output.
          client_channel_after_operation
            d
            (channel_receive_reusable result)
            wire_received1
            wire_sent1
            pending1
            app_log1 **
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
              (Ghost.reveal wire_received0)
              (Ghost.reveal wire_sent0)
              (Ghost.reveal app_log0)
              wire_received1
              wire_sent1
              app_log1)
{
  let result =
    channel_receive
      d wire_received0 wire_sent0 pending0 app_log0
      out old_output out_len local_fuel fuel;
  with wire_received1 wire_sent1 pending1 app_log1 output.
    assert (
      (if channel_receive_reusable result
       then
         DS.client_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
       else
         DS.client_channel_terminal
           d wire_received1 wire_sent1 app_log1) **
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
          (Ghost.reveal wire_received0)
          (Ghost.reveal wire_sent0)
          (Ghost.reveal app_log0)
          wire_received1
          wire_sent1
          app_log1));
  let reusable = channel_receive_reusable_runtime result;
  assert (pure (reusable == channel_receive_reusable result));
  if reusable {
    assert (pure (channel_receive_reusable result == true));
    rewrite
      (if channel_receive_reusable result
       then
         DS.client_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
       else
         DS.client_channel_terminal
           d wire_received1 wire_sent1 app_log1)
      as
      (DS.client_channel_inv
        d wire_received1 wire_sent1 pending1 app_log1);
    rewrite
      (DS.client_channel_inv
        d wire_received1 wire_sent1 pending1 app_log1)
      as
      (client_channel_after_operation
        d
        (channel_receive_reusable result)
        wire_received1
        wire_sent1
        pending1
        app_log1);
    result
  } else {
    assert (pure (channel_receive_reusable result == false));
    rewrite
      (if channel_receive_reusable result
       then
         DS.client_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
       else
         DS.client_channel_terminal
           d wire_received1 wire_sent1 app_log1)
      as
      (DS.client_channel_terminal
        d wire_received1 wire_sent1 app_log1);
    CChannel.open_terminal
      d
      (Ghost.hide wire_received1)
      (Ghost.hide wire_sent1)
      (Ghost.hide app_log1);
    DClose.abort d;
    with st1. assert (DS.client_driver_closed d st1);
    rewrite
      (DS.client_driver_closed d st1)
      as
      (client_driver_closed d st1);
    fold (client_driver_is_closed d);
    rewrite
      (client_driver_is_closed d)
      as
      (client_channel_after_operation
        d
        (channel_receive_reusable result)
        wire_received1
        wire_sent1
        pending1
        app_log1);
    result
  }
}

fn close
  (d:client_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (wait_for_peer:bool)
  (fuel:SZ.t)
  requires DS.client_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
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
    d wire_received wire_sent pending app_log;
  DClose.run d wait_for_peer fuel
}

fn abort
  (d:client_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires DS.client_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log)
  ensures exists* st. DS.client_driver_closed d st
{
  CChannel.open_channel_invariant
    d wire_received wire_sent pending app_log;
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
    CI.ci_terminal_inv = DS.client_channel_terminal;
    CI.ci_io_frame = DS.client_channel_io_frame;
    CI.ci_snapshot = DS.client_channel_snapshot;
    CI.ci_send_succeeded = channel_send_succeeded;
    CI.ci_send_usable = channel_send_reusable;
    CI.ci_receive_succeeded = channel_receive_succeeded;
    CI.ci_receive_usable = channel_receive_reusable;
    CI.ci_receive_length = channel_receive_length;
    CI.ci_open_io_channel = CChannel.open_io_channel;
    CI.ci_close_io_channel = CChannel.close_io_channel;
    CI.ci_invariant_valid = CChannel.channel_invariant_valid;
    CI.ci_take_snapshot = CChannel.take_channel_snapshot;
    CI.ci_recall_snapshot = CChannel.recall_channel_snapshot;
    CI.ci_send = channel_send;
    CI.ci_receive = channel_receive;
  }
