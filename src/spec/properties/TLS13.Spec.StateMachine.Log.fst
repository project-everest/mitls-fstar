module TLS13.Spec.StateMachine.Log

(**
  Auxiliary: wire/log helper functions and per-component consistency
  (conn-event deltas, sent/received message and transcript/app logs, the
  projected record layer, abstract-state and connection-log projections).
  Builds on TLS13.Spec.StateMachine.
**)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module M = TLS13.Messages
module R = TLS13.Record.Spec
module S = TLS13.Spec.StateMachine.ClientTrace
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec

open FStar.List.Tot

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.KeyMaterial

let conn_event_sent_tls_delta (ev:conn_event) : list M.tls_message =
  match ev with
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction with
     | CL.Sent -> [msg.CL.message_value]
     | CL.Received -> [])
  | ConnLocalEvent _ -> []
let conn_event_received_tls_delta (ev:conn_event) : list M.tls_message =
  match ev with
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction with
     | CL.Sent -> []
     | CL.Received -> [msg.CL.message_value])
  | ConnLocalEvent _ -> []
let conn_event_app_sent_delta (ev:conn_event) : list B.bytes =
  match ev with
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Sent, M.TlsApplicationData bytes -> [bytes]
     | _, _ -> [])
  | ConnLocalEvent _ -> []
let conn_event_app_received_delta (ev:conn_event) : list B.bytes =
  match ev with
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Received, M.TlsApplicationData bytes -> [bytes]
     | _, _ -> [])
  | ConnLocalEvent local ->
    (match local with
     | LocalDeliverApplicationData bytes -> [bytes]
     | _ -> [])
let state_event_of_conn_event (ev:conn_event) : GTot (option S.event) =
  match ev with
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Sent, M.TlsHandshake (M.ClientHello ch) -> Some (S.SendClientHello ch)
     | CL.Received, M.TlsHandshake (M.ServerHello sh) -> Some (S.RecvServerHello sh)
     | CL.Received, M.TlsHandshake (M.EncryptedExtensions ee) -> Some (S.RecvEncryptedExtensions ee)
     | CL.Received, M.TlsHandshake (M.Certificate cert) -> Some (S.RecvCertificate cert)
     | CL.Received, M.TlsHandshake (M.CertificateVerify cv) -> Some (S.RecvCertificateVerify cv)
     | CL.Received, M.TlsHandshake (M.Finished fin) -> Some (S.RecvServerFinished fin)
     | CL.Sent, M.TlsHandshake (M.Finished fin) -> Some (S.SendClientFinished fin)
     | CL.Sent, M.TlsApplicationData bytes -> Some (S.SendApplicationData bytes)
     | CL.Received, M.TlsApplicationData bytes -> Some (S.RecvApplicationData bytes)
     | CL.Sent, M.TlsAlert T.Close_notify -> Some S.SendCloseNotify
     | CL.Received, M.TlsAlert T.Close_notify -> Some S.RecvCloseNotify
     | _, M.TlsAlert alert -> Some (S.Fail (T.AlertError alert))
     | _, M.TlsChangeCipherSpec -> None
     | _, _ -> None)
  | ConnLocalEvent local ->
    (match local with
     | LocalValidateCertificate peer -> Some (S.ValidateCertificate peer)
     | LocalFail err -> Some (S.Fail err)
     | _ -> None)
let state_event_delta_of_conn_event (ev:conn_event) : GTot (list S.event) =
  match state_event_of_conn_event ev with
  | Some state_ev -> [state_ev]
  | None -> []
let rec sent_tls_messages (events:list conn_event)
  : GTot (list M.tls_message)
        (decreases events)
  =
  match events with
  | [] -> []
  | ev :: rest -> conn_event_sent_tls_delta ev @ sent_tls_messages rest
let rec received_tls_messages (events:list conn_event)
  : GTot (list M.tls_message)
        (decreases events)
  =
  match events with
  | [] -> []
  | ev :: rest -> conn_event_received_tls_delta ev @ received_tls_messages rest
let rec state_machine_events (events:list conn_event)
  : GTot (list S.event)
        (decreases events)
  =
  match events with
  | [] -> []
  | ev :: rest -> state_event_delta_of_conn_event ev @ state_machine_events rest
let conn_event_transcript_delta (ev:conn_event) : GTot B.bytes =
  match ev with
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Sent, M.TlsHandshake (M.ClientHello ch) ->
       W.serialize_handshake (M.ClientHello ch)
     | CL.Received, M.TlsHandshake (M.ClientHello ch) ->
       W.serialize_handshake (M.ClientHello ch)
     | CL.Received, M.TlsHandshake (M.ServerHello sh) ->
       W.serialize_handshake (M.ServerHello sh)
     | CL.Sent, M.TlsHandshake (M.ServerHello sh) ->
       W.serialize_handshake (M.ServerHello sh)
     | CL.Sent, M.TlsHandshake (M.EncryptedExtensions ee) ->
       W.serialize_handshake (M.EncryptedExtensions ee)
     | CL.Received, M.TlsHandshake (M.EncryptedExtensions ee) ->
       W.serialize_handshake (M.EncryptedExtensions ee)
     | CL.Sent, M.TlsHandshake (M.Certificate cert) ->
       W.serialize_handshake (M.Certificate cert)
     | CL.Received, M.TlsHandshake (M.Certificate cert) ->
       W.serialize_handshake (M.Certificate cert)
     | CL.Sent, M.TlsHandshake (M.CertificateVerify cv) ->
       W.serialize_handshake (M.CertificateVerify cv)
     | CL.Received, M.TlsHandshake (M.CertificateVerify cv) ->
       W.serialize_handshake (M.CertificateVerify cv)
     | CL.Sent, M.TlsHandshake (M.Finished fin) ->
       W.serialize_handshake (M.Finished fin)
     | _, _ -> B.empty)
  | ConnLocalEvent local ->
    (match local with
     | LocalVerifyFinished fin -> W.serialize_handshake (M.Finished fin)
     | LocalVerifyClientFinished fin -> W.serialize_handshake (M.Finished fin)
     | _ -> B.empty)
let rec transcript_bytes_of_conn_events (events:list conn_event)
  : GTot B.bytes
        (decreases events)
=
  match events with
  | [] -> B.empty
  | ev :: rest ->
    B.append (conn_event_transcript_delta ev) (transcript_bytes_of_conn_events rest)
let rec app_sent_messages (events:list conn_event)
  : GTot (list B.bytes)
        (decreases events)
=
  match events with
  | [] -> []
  | ev :: rest -> conn_event_app_sent_delta ev @ app_sent_messages rest
let rec app_received_messages (events:list conn_event)
  : GTot (list B.bytes)
        (decreases events)
  =
  match events with
  | [] -> []
  | ev :: rest -> conn_event_app_received_delta ev @ app_received_messages rest
let app_log_of_conn_events (events:list conn_event) : GTot CL.app_log = {
  CL.app_sent = app_sent_messages events;
  CL.app_received = app_received_messages events;
}
let key_update_response_pending_step
  (pending:bool)
  (ev:conn_event)
  : bool =
  match ev with
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Received, M.TlsKeyUpdate M.UpdateRequested -> true
     | CL.Sent, M.TlsKeyUpdate M.UpdateNotRequested -> false
     | _, _ -> pending)
  | ConnLocalEvent _ ->
    pending
let rec key_update_response_pending_after_events_from
  (pending:bool)
  (events:list conn_event)
  : Tot bool
        (decreases events)
=
  match events with
  | [] -> pending
  | ev :: rest ->
    key_update_response_pending_after_events_from
      (key_update_response_pending_step pending ev)
      rest
let key_update_response_pending_of_conn_events
  (events:list conn_event)
  : Tot bool =
  key_update_response_pending_after_events_from false events
type projected_direction_state = {
  projected_epoch: R.epoch;
  projected_seq: nat;
}
type projected_record_layer_state = {
  projected_read: projected_direction_state;
  projected_write: projected_direction_state;
}
let projected_direction_state_of_record
  (st:R.direction_state)
  : projected_direction_state =
  {
    projected_epoch = st.R.epoch;
    projected_seq = st.R.seq;
  }
let projected_record_layer_state_of_record
  (record:record_layer_state)
  : projected_record_layer_state =
  {
    projected_read = projected_direction_state_of_record record.record_read;
    projected_write = projected_direction_state_of_record record.record_write;
  }
let initial_projected_direction_state : projected_direction_state = {
  projected_epoch = R.Initial;
  projected_seq = 0;
}
let initial_projected_record_layer_state : projected_record_layer_state = {
  projected_read = initial_projected_direction_state;
  projected_write = initial_projected_direction_state;
}
let projected_next_seq
  (st:projected_direction_state)
  : projected_direction_state =
  { st with projected_seq = st.projected_seq + 1 }
let projected_install_keys
  (epoch:R.epoch)
  : projected_direction_state =
  { projected_epoch = epoch; projected_seq = 0 }
let rec projected_advance_records
  (st:projected_direction_state)
  (n:nat)
  : Tot projected_direction_state
        (decreases n)
=
  if n = 0 then st
  else projected_next_seq (projected_advance_records st (n - 1))
let projected_install_record_keys
  (record:projected_record_layer_state)
  (install:traffic_key_install)
  : projected_record_layer_state =
  let epoch = traffic_record_epoch install.install_epoch in
  match install.install_epoch, install.install_direction with
  | TrafficApplication, TrafficWrite ->
    record
  | _, TrafficWrite ->
    { record with projected_write = projected_install_keys epoch }
  | _, TrafficRead ->
    { record with projected_read = projected_install_keys epoch }
let projected_install_record_keys_for_role
  (role:endpoint_role)
  (record:projected_record_layer_state)
  (install:traffic_key_install)
  : projected_record_layer_state =
  match role, install.install_epoch, install.install_direction with
  | ServerEndpoint, TrafficApplication, TrafficWrite ->
    { record with projected_write = projected_install_keys R.Application }
  | _, _, _ ->
    projected_install_record_keys record install
let projected_client_application_write_after_finished
  (record:projected_record_layer_state)
  : projected_record_layer_state =
  { record with projected_write = projected_install_keys R.Application }
let projected_server_finished_write
  (record:projected_record_layer_state)
  : projected_record_layer_state =
  { record with projected_write = projected_next_seq record.projected_write }
let projected_record_layer_step_for_role
  (role:endpoint_role)
  (record:projected_record_layer_state)
  (ev:conn_event)
  : projected_record_layer_state =
  match ev with
  | ConnLocalEvent local ->
    (match local with
     | LocalInstallTrafficKeys install -> projected_install_record_keys record install
     | LocalInstallTrafficKeysForRole role_install ->
       projected_install_record_keys_for_role
         role_install.install_role
         record
         role_install.install_payload
     | _ -> record)
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Received, M.TlsHandshake (M.EncryptedExtensions _)
     | CL.Received, M.TlsHandshake (M.Certificate _)
     | CL.Received, M.TlsHandshake (M.CertificateVerify _)
     | CL.Received, M.TlsHandshake (M.Finished _)
     | CL.Received, M.TlsApplicationData _
     | CL.Received, M.TlsIgnoredPostHandshake _
     | CL.Received, M.TlsAlert T.Close_notify ->
       { record with projected_read = projected_next_seq record.projected_read }
     | CL.Sent, M.TlsHandshake (M.EncryptedExtensions _)
     | CL.Sent, M.TlsHandshake (M.Certificate _)
     | CL.Sent, M.TlsHandshake (M.CertificateVerify _) ->
       { record with projected_write = projected_next_seq record.projected_write }
     | CL.Sent, M.TlsHandshake (M.Finished _) ->
       (match role with
        | ClientEndpoint -> projected_client_application_write_after_finished record
        | ServerEndpoint -> projected_server_finished_write record)
     | CL.Sent, M.TlsApplicationData bytes ->
       { record with
           projected_write =
             projected_advance_records
               record.projected_write
               (S.application_data_record_count bytes) }
     | CL.Received, M.TlsKeyUpdate _ ->
       { record with projected_read = projected_install_keys R.Application }
     | CL.Sent, M.TlsKeyUpdate M.UpdateNotRequested ->
       { record with projected_write = projected_install_keys R.Application }
     | CL.Sent, M.TlsAlert T.Close_notify ->
       { record with projected_write = projected_next_seq record.projected_write }
     | _, _ ->
       record)
let projected_record_layer_step
  (record:projected_record_layer_state)
  (ev:conn_event)
  : projected_record_layer_state =
  projected_record_layer_step_for_role ClientEndpoint record ev
let rec projected_record_layer_after_events_from_for_role
  (role:endpoint_role)
  (record:projected_record_layer_state)
  (events:list conn_event)
  : Tot projected_record_layer_state
       (decreases events)
=
  match events with
  | [] -> record
  | ev :: rest ->
    projected_record_layer_after_events_from_for_role
     role
     (projected_record_layer_step_for_role role record ev)
     rest
let projected_record_layer_after_events_from
  (record:projected_record_layer_state)
  (events:list conn_event)
  : Tot projected_record_layer_state =
  projected_record_layer_after_events_from_for_role ClientEndpoint record events
let projected_record_layer_of_conn_events_for_role
  (role:endpoint_role)
  (events:list conn_event)
  : Tot projected_record_layer_state =
  projected_record_layer_after_events_from_for_role
    role
    initial_projected_record_layer_state
    events
let projected_record_layer_of_conn_events
  (events:list conn_event)
  : Tot projected_record_layer_state =
  projected_record_layer_of_conn_events_for_role ClientEndpoint events
let connection_state_app_log_consistent
  (st:connection_state)
  : prop =
  st.cs_model.model_application.app_log.CL.app_sent ==
    (app_log_of_conn_events st.cs_event_log).CL.app_sent /\
  st.cs_model.model_application.app_log.CL.app_received ==
    (app_log_of_conn_events st.cs_event_log).CL.app_received
let connection_state_pending_application_consistent
  (st:connection_state)
  : prop =
  pending_application_consistent st.cs_model.model_application
let connection_state_transcript_consistent
  (st:connection_state)
  : prop =
  Seq.equal
    st.cs_model.model_handshake.hs_transcript
    (transcript_bytes_of_conn_events st.cs_event_log)
let connection_state_event_log_consistent_with
  (cfg:connection_config)
  (st:connection_state)
  : prop =
  step_model_many (initial_model cfg) st.cs_event_log == Some st.cs_model
let connection_state_event_log_consistent
  (st:connection_state)
  : prop =
  connection_state_event_log_consistent_with st.cs_model.model_config st
let connection_state_key_update_pending_consistent
  (st:connection_state)
  : prop =
  st.cs_model.model_application.app_key_update_response_pending ==
    key_update_response_pending_of_conn_events st.cs_event_log
let connection_state_record_layer_consistent_for_role
  (role:endpoint_role)
  (st:connection_state)
  : prop =
  match st.cs_model.model_control with
  | ControlFailed _ -> True
  | _ ->
    projected_record_layer_state_of_record st.cs_model.model_record ==
      projected_record_layer_of_conn_events_for_role role st.cs_event_log
let connection_state_record_layer_consistent_for_config_role
  (st:connection_state)
  : prop =
  connection_state_record_layer_consistent_for_role
    st.cs_model.model_config.config_role
    st
let connection_state_record_layer_consistent
  (st:connection_state)
  : prop =
  connection_state_record_layer_consistent_for_config_role st
let connection_state_record_keys_consistent_for_role
  (role:endpoint_role)
  (st:connection_state)
  : prop =
  model_record_keys_consistent_for_role role st.cs_model
let connection_state_record_keys_consistent_for_config_role
  (st:connection_state)
  : prop =
  connection_state_record_keys_consistent_for_role
    st.cs_model.model_config.config_role
    st
let connection_state_record_keys_consistent
  (st:connection_state)
  : prop =
  st.cs_model.model_config.config_role == ClientEndpoint /\
  connection_state_record_keys_consistent_for_role ClientEndpoint st
let connection_state_layered_log_consistent_for_role
  (role:endpoint_role)
  (st:connection_state)
  : prop =
  connection_state_event_log_consistent st /\
  connection_state_transcript_consistent st /\
  connection_state_key_update_pending_consistent st /\
  connection_state_record_layer_consistent_for_role role st /\
  connection_state_record_keys_consistent_for_role role st /\
  connection_state_pending_application_consistent st /\
  connection_state_app_log_consistent st
let connection_state_layered_log_consistent_for_config_role
  (st:connection_state)
  : prop =
  connection_state_layered_log_consistent_for_role
    st.cs_model.model_config.config_role
    st
let connection_state_layered_log_consistent
  (st:connection_state)
  : prop =
  st.cs_model.model_config.config_role == ClientEndpoint /\
  connection_state_layered_log_consistent_for_role ClientEndpoint st
let model_key_update_pending_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : prop =
  model1.model_application.app_key_update_response_pending ==
    key_update_response_pending_step
      model0.model_application.app_key_update_response_pending
      ev
let model_record_layer_delta_for_role
  (role:endpoint_role)
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : prop =
  match model1.model_control with
  | ControlFailed _ -> True
  | _ ->
    projected_record_layer_state_of_record model1.model_record ==
      projected_record_layer_step_for_role
        role
        (projected_record_layer_state_of_record model0.model_record)
        ev
let model_record_layer_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : prop =
  model_record_layer_delta_for_role model0.model_config.config_role model0 ev model1
let model_pending_application_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : prop =
  pending_application_consistent model0.model_application ==>
    pending_application_consistent model1.model_application
let model_transcript_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : prop =
  Seq.equal
    model1.model_handshake.hs_transcript
    (B.append
      model0.model_handshake.hs_transcript
      (conn_event_transcript_delta ev))
let model_app_log_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : prop =
  model1.model_application.app_log.CL.app_sent ==
    model0.model_application.app_log.CL.app_sent @ conn_event_app_sent_delta ev /\
  model1.model_application.app_log.CL.app_received ==
    model0.model_application.app_log.CL.app_received @ conn_event_app_received_delta ev
let connection_log_event_of_conn_event (ev:conn_event) : option CL.host_event =
  match ev with
  | ConnNetworkEvent msg -> Some (CL.NetworkEvent msg)
  | ConnLocalEvent local ->
    (match local with
     | LocalValidateCertificate peer -> Some (CL.LocalEvent (CL.LocalValidateCertificate peer))
     | LocalDeliverApplicationData bytes -> Some (CL.LocalEvent (CL.LocalDeliverApplicationData bytes))
     | LocalFail err -> Some (CL.LocalEvent (CL.LocalFail err))
     | _ -> None)
let rec connection_log_trace_of_conn_events (events:list conn_event)
  : GTot (list CL.host_event)
        (decreases events)
  =
  match events with
  | [] -> []
  | ev :: rest ->
    (match connection_log_event_of_conn_event ev with
     | Some host_ev -> host_ev :: connection_log_trace_of_conn_events rest
     | None -> connection_log_trace_of_conn_events rest)
let phase_of_handshake_stage (stage:handshake_stage) : S.phase =
  match stage with
  | HsNotStarted -> S.Start
  | HsStarted -> S.Start
  | HsClientHelloSent -> S.ClientHelloSent
  | HsServerHelloReceived -> S.ServerHelloReceived
  | HsEncryptedExtensionsReceived -> S.EncryptedExtensionsReceived
  | HsCertificateReceived -> S.CertificateReceived
  | HsCertificateValidated -> S.CertificateValidated
  | HsCertificateVerifyReceived -> S.CertificateValidated
  | HsCertificateVerifyVerified -> S.CertificateVerified
  | HsServerFinishedReceived -> S.CertificateVerified
  | HsServerFinishedVerified -> S.ServerFinishedVerified
  | HsClientFinishedSent -> S.ApplicationData
  // Server-only stages need a role-parametric trace automaton in a later slice.
  | HsAwaitingClientHello
  | HsClientHelloReceived
  | HsServerHelloSent
  | HsServerEncryptedFlightSent
  | HsServerFinishedSent
  | HsClientFinishedReceived
  | HsClientFinishedVerified -> S.Start
let phase_of_control_state (control:connection_control_state) : S.phase =
  match control with
  | ControlNew -> S.Start
  | ControlHandshaking stage -> phase_of_handshake_stage stage
  | ControlApplicationData -> S.ApplicationData
  | ControlClosing -> S.Closing
  | ControlClosed -> S.Closed
  | ControlFailed _ -> S.Failed
let failure_of_model (model:connection_model) : option T.tls_error =
  match model.model_control with
  | ControlFailed err -> Some err
  | _ -> model.model_failure
let abstract_state_of_model (model:connection_model) : S.conn_state =
  {
    S.role = S.Client;
    S.phase = phase_of_control_state model.model_control;
    S.transcript = model.model_handshake.hs_transcript;
    S.read_state = model.model_record.record_read;
    S.write_state = model.model_record.record_write;
    S.peer = model.model_handshake.hs_validated_peer;
    S.failure = failure_of_model model;
  }
let connection_log_view_of_state (st:connection_state) : GTot CL.connection_view =
  let raw = st.cs_wire_log in
  let app = st.cs_model.model_application in
  {
    CL.raw_log = raw;
    CL.sent_records = CL.parse_record_prefix raw.CL.raw_sent;
    CL.received_records = CL.parse_record_prefix raw.CL.raw_received;
    CL.sent_tls = CL.raw_stream_view raw.CL.raw_sent (sent_tls_messages st.cs_event_log);
    CL.received_tls = CL.raw_stream_view raw.CL.raw_received (received_tls_messages st.cs_event_log);
    CL.host_trace = connection_log_trace_of_conn_events st.cs_event_log;
    CL.state = abstract_state_of_model st.cs_model;
    CL.app_view = app.app_log;
    CL.pending_app = app.app_pending_plaintext;
    CL.pending_app_record = app.app_pending_source_record;
    CL.pending_app_offset = app.app_pending_source_offset;
    CL.pending_received_raw = app.app_pending_received_raw;
  }
let connection_state_connection_log_view_consistent
  (st:connection_state)
  : prop =
  let view = connection_log_view_of_state st in
  CL.connection_view_raw_stream_shaped view /\
  CL.connection_view_record_stream_shaped view /\
  view.CL.sent_tls.CL.values == CL.sent_tls_of_host_trace view.CL.host_trace /\
  view.CL.received_tls.CL.values == CL.received_tls_of_host_trace view.CL.host_trace /\
  CL.state_events_of_host_trace view.CL.host_trace == state_machine_events st.cs_event_log /\
  CL.app_log_of_host_trace view.CL.host_trace == view.CL.app_view /\
  CL.pending_app_source_consistent view
