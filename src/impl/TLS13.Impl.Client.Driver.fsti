module TLS13.Impl.Client.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Impl.Client
module CL = TLS13.ConnectionLog
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.Spec.StateMachine.ClientTrace
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

val client_driver : Type0

noextract
val client_driver_wire_logs_match
  (st:TLS13.Spec.StateMachine.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : prop

noextract
val client_driver_live
  (d:client_driver)
  (st:TLS13.Spec.StateMachine.connection_state)
  : slprop

noextract
(**
  Owns a connected driver together with the actual TCP byte histories tracked by
  Common.TCP. The protocol-level processed wire log is in st.cs_wire_log; received
  may also include bytes retained in the driver's input buffer. The predicate
  includes client_driver_wire_logs_match for the hidden retained bytes, making
  the public API relation between transport byte contents and protocol wire-log
  contents explicit.
**)
val client_driver_connected
  (d:client_driver)
  (st:TLS13.Spec.StateMachine.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  : slprop

noextract
val client_driver_closed
  (d:client_driver)
  (st:TLS13.Spec.StateMachine.connection_state)
  : slprop

noextract
let client_driver_application_ready
  (st:CS.connection_state)
  : prop =
  CT.client_end_to_end_invariant st /\
  st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
  CS.application_record_keys_installed_for_role CS.ClientEndpoint st.CS.cs_model

noextract
let client_driver_sent_log_exact
  (st:CS.connection_state)
  (sent:B.bytes)
  : prop =
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent

noextract
let client_driver_received_log_accounted
  (st:CS.connection_state)
  (received:B.bytes)
  : prop =
  B.length st.CS.cs_wire_log.CL.raw_received <= B.length received /\
  (forall b.
    SeqP.count b st.CS.cs_wire_log.CL.raw_received <=
    SeqP.count b received)

noextract
let client_driver_received_log_exact_prefix
  (st:CS.connection_state)
  (received:B.bytes)
  : prop =
  exists retained.
    Seq.equal received
      (B.append st.CS.cs_wire_log.CL.raw_received retained)

noextract
let client_driver_received_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  : prop =
  B.length received == B.length st.CS.cs_wire_log.CL.raw_received

val lemma_client_driver_wire_logs_match_received_exact_prefix
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        client_driver_wire_logs_match st received sent buffered buffered_len /\
        CT.connection_control_not_failed st)
      (ensures client_driver_received_log_exact_prefix st received)

val lemma_client_driver_wire_logs_match_received_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        client_driver_wire_logs_match st received sent buffered buffered_len /\
        CT.connection_control_not_failed st /\
        buffered_len == 0sz)
      (ensures client_driver_received_no_read_ahead st received)

noextract
let client_driver_local_write_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:CT.client_response)
  (kind:CT.local_event_kind)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop =
  exists network_out_bytes app_out_bytes.
    CT.local_event_end_to_end_correct
      st0
      st1
      resp
      kind
      payload
      network_out_bytes
      app_out_bytes /\
    Seq.equal
      sent'
      (B.append sent (CT.response_network_out resp network_out_bytes))

type driver_workflow_status =
  | DriverWorkflowOk
  | DriverWorkflowNeedMoreInput
  | DriverWorkflowStepFailed
  | DriverWorkflowExhausted
  | DriverWorkflowClosed
  | DriverWorkflowPayloadTooLarge

noextract
let client_driver_send_status_correct
  (status:driver_workflow_status)
  (resp:CT.client_response)
  : prop =
  if resp.CT.status == CT.StepOk
  then status == DriverWorkflowOk
  else status == DriverWorkflowStepFailed

(**
  TLS 1.3 bounds a single application-data record's plaintext at
  [SM.max_application_data_fragment_len] (2^14 = 16384) bytes.  [send]
  performs this authoritative length test itself, so any caller-supplied
  payload longer than the bound is unambiguously rejected up front without
  attempting to process it.
**)
noextract
let client_driver_payload_too_large
  (payload:B.bytes)
  : prop =
  B.length payload > SM.max_application_data_fragment_len

noextract
let client_driver_send_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (status:driver_workflow_status)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop =
  if status == DriverWorkflowPayloadTooLarge
  then
    st1 == st0 /\
    Seq.equal sent' sent /\
    client_driver_payload_too_large payload
  else
    exists resp.
      client_driver_local_write_correct
        st0
        st1
        resp
        CT.LocalSendApplicationData
        payload
        sent
        sent' /\
      client_driver_send_status_correct status resp

noextract
let client_driver_close_status_correct
  (wait_for_peer:bool)
  (status:driver_workflow_status)
  (resp:CT.client_response)
  : prop =
  (resp.CT.status <> CT.StepOk ==> status == DriverWorkflowStepFailed) /\
  (resp.CT.status == CT.StepOk /\ wait_for_peer == false ==>
    status == DriverWorkflowClosed)

noextract
let client_driver_close_correct
  (st0:CS.connection_state)
  (st_close_notify:CS.connection_state)
  (status:driver_workflow_status)
  (wait_for_peer:bool)
  : prop =
  exists resp.
    client_driver_local_write_correct
      st0
      st_close_notify
      resp
      CT.LocalSendCloseNotify
      B.empty
      st0.CS.cs_wire_log.CL.raw_sent
      st_close_notify.CS.cs_wire_log.CL.raw_sent /\
    client_driver_close_status_correct wait_for_peer status resp

type client_receive_result = {
  client_receive_status: driver_workflow_status;
  client_receive_len: SZ.t;
}

noextract
noeq
type client_receive_observation = {
  client_receive_observed_status: driver_workflow_status;
  client_receive_observed_response: CT.client_buffer_response;
}

noextract
let client_receive_observation_network_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (obs:client_receive_observation)
  (app_out:B.bytes)
  : prop =
  obs.client_receive_observed_status <> DriverWorkflowExhausted ==>
    exists st_network st_before input old_network_out network_out old_app_out observed_app_out.
      CT.network_bytes_end_to_end_correct
        st_before
        st_network
        obs.client_receive_observed_response
        input
        old_network_out
        network_out
        old_app_out
        observed_app_out /\
      (obs.client_receive_observed_status == DriverWorkflowOk ==>
        st_network == st1 /\ Seq.equal observed_app_out app_out) /\
      (**
        A peer close_notify is detected as a StepOk network step that both
        produces zero application bytes and drives the connection to
        [CS.ControlClosed]. When [receive] reports [DriverWorkflowClosed], the
        final connection state is exactly that closed state and no
        application bytes were produced by this step, so callers can safely
        stop retrying and release the transport (e.g. via [abort]) instead of
        looping until fuel is exhausted.
      **)
      (obs.client_receive_observed_status == DriverWorkflowClosed ==>
        st_network == st1 /\
        st1.CS.cs_model.CS.model_control == CS.ControlClosed /\
        obs.client_receive_observed_response.CT.response.CT.app_out_len == 0sz)

noextract
let client_driver_receive_status_correct
  (result:client_receive_result)
  (obs:client_receive_observation)
  (app_out:B.bytes)
  (out_bytes:B.bytes)
  : prop =
  let resp = obs.client_receive_observed_response.CT.response in
  if obs.client_receive_observed_status == DriverWorkflowOk then
    if SZ.v resp.CT.app_out_len <= B.length out_bytes /\
       SZ.v resp.CT.app_out_len <= B.length app_out
    then
      result.client_receive_status == DriverWorkflowOk /\
      result.client_receive_len == resp.CT.app_out_len
    else
      result.client_receive_status == DriverWorkflowStepFailed /\
      result.client_receive_len == 0sz
  else
    result.client_receive_status == obs.client_receive_observed_status /\
    result.client_receive_len == 0sz

noextract
let client_driver_receive_copyout_correct
  (result:client_receive_result)
  (resp:CT.client_response)
  (app_out:B.bytes)
  (out_bytes:B.bytes)
  : prop =
  if result.client_receive_status == DriverWorkflowOk then
    SZ.v result.client_receive_len <= B.length out_bytes /\
    result.client_receive_len == resp.CT.app_out_len /\
    (if SZ.v result.client_receive_len <= B.length out_bytes then
      Seq.equal
        (Seq.slice out_bytes 0 (SZ.v result.client_receive_len))
        (CT.response_app_out resp app_out)
     else False)
  else
    True

noextract
let client_driver_receive_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (result:client_receive_result)
  (obs:client_receive_observation)
  (app_out:B.bytes)
  (out_bytes:B.bytes)
  : prop =
  client_driver_receive_status_correct
    result
    obs
    app_out
    out_bytes /\
  client_receive_observation_network_correct st0 st1 obs app_out /\
  SZ.v result.client_receive_len <= B.length out_bytes /\
  (result.client_receive_status == DriverWorkflowOk ==>
    client_driver_receive_copyout_correct
      result
      obs.client_receive_observed_response.CT.response
      app_out
      out_bytes)

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
          client_driver_live
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

fn connect
  (d:client_driver)
  (connect_host:array U8.t)
  (connect_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires client_driver_live d 'st0 **
           pts_to connect_host 'connect_host_bytes **
           pure (B.length 'connect_host_bytes == SZ.v connect_host_len)
  returns status:driver_workflow_status
  ensures exists* st1.
          pts_to connect_host 'connect_host_bytes **
          (match status with
           | DriverWorkflowOk ->
             exists* received sent.
               client_driver_connected d st1 received sent **
               pure (client_driver_application_ready st1 /\
                     st1.CS.cs_model.CS.model_config ==
                       'st0.CS.cs_model.CS.model_config /\
                     client_driver_sent_log_exact st1 sent /\
                     client_driver_received_log_accounted st1 received /\
                     client_driver_received_log_exact_prefix st1 received /\
                     client_driver_received_no_read_ahead st1 received)
           | _ ->
             client_driver_closed d st1)

(**
  Sends [payload] as application data over the connection.  This function is
  total for any [payload_len]: the only preconditions are ownership of the
  payload array (with a matching length) and an application-ready connected
  driver.  A payload whose length exceeds the single-record limit
  ([SM.max_application_data_fragment_len] = 16384 bytes) is rejected with
  [DriverWorkflowPayloadTooLarge] without being sent, leaving the connection
  state, sent log, and received accounting exactly as they were -- see
  [client_driver_send_correct].
**)
fn send
  (d:client_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires client_driver_connected d 'st0 'received0 'sent0 **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len)
  returns status:driver_workflow_status
  ensures exists* st1 received1 sent1.
          pts_to payload 'payload_bytes **
          client_driver_connected d st1 received1 sent1 **
          pure (client_driver_send_correct
                 'st0
                 st1
                 status
                 (Ghost.reveal 'payload_bytes)
                 (Ghost.reveal 'sent0)
                 sent1 /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0) /\
                 client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0) /\
                 client_driver_sent_log_exact st1 sent1 /\
                 client_driver_received_log_accounted st1 received1)

fn receive
  (d:client_driver)
  (out:array U8.t)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires client_driver_connected d 'st0 'received0 'sent0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns result:client_receive_result
  ensures exists* st1 received1 sent1 out_bytes.
          client_driver_connected d st1 received1 sent1 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v result.client_receive_len <= SZ.v out_len /\
          st1.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config /\
          client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0) /\
          client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0) /\
                client_driver_sent_log_exact st1 sent1 /\
                client_driver_received_log_accounted st1 received1 /\
                (exists obs app_out.
                  client_driver_receive_correct
                   'st0
                   st1
                    result
                    obs
                    app_out
                    out_bytes))

fn close
  (d:client_driver)
  (wait_for_peer:bool)
  (fuel:SZ.t)
  requires client_driver_connected d 'st0 'received0 'sent0
  returns status:driver_workflow_status
  ensures exists* st1.
          client_driver_closed d st1 **
          pure (st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config /\
                client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0) /\
                client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0) /\
                (exists st_close_notify.
            client_driver_close_correct
              'st0
              st_close_notify
              status
              wait_for_peer))

(**
  Safely disposes a connected transport after a workflow failure.  Unlike
  [close], this does not require the protocol state to remain
  application-ready and does not attempt to send close_notify.
**)
fn abort
  (d:client_driver)
  requires client_driver_connected d 'st0 'received0 'sent0
  ensures client_driver_closed d 'st0
