module TLS13.Spec.ConnectionState

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module K = TLS13.Keys
module M = TLS13.Messages
module R = TLS13.Record.Spec
module RTC = FStar.ReflexiveTransitiveClosure
module S = TLS13.StateMachine
module Seq = FStar.Seq
module T = TLS13.Types
module Tr = TLS13.Transcript
module X = TLS13.X509.Spec

open FStar.List.Tot

type wire_log = CL.raw_io_log
type direction = CL.direction
type directed_message (a:Type0) = CL.directed_message a

let empty_wire_log : wire_log = CL.empty_raw_io_log

type endpoint_role =
  | ClientEndpoint

type connection_config = {
  config_role: endpoint_role;
  config_server_name: T.hostname;
  config_trust_store: X.trust_store;
  config_validation_time: X.validation_time;
  config_cipher_suites: list T.cipher_suite;
  config_signature_schemes: list T.signature_scheme;
}

type handshake_stage =
  | HsNotStarted
  | HsStarted
  | HsClientHelloSent
  | HsServerHelloReceived
  | HsEncryptedExtensionsReceived
  | HsCertificateReceived
  | HsCertificateValidated
  | HsCertificateVerifyReceived
  | HsCertificateVerifyVerified
  | HsServerFinishedReceived
  | HsServerFinishedVerified
  | HsClientFinishedSent

type connection_control_state =
  | ControlNew
  | ControlHandshaking of handshake_stage
  | ControlApplicationData
  | ControlClosing
  | ControlClosed
  | ControlFailed of T.tls_error

type handshake_start = {
  start_server_name: T.hostname;
  start_client_random: B.bytes_of_len 32;
  start_client_key_share_private: option C.x25519_private;
  start_client_key_share_public: C.x25519_public;
  start_cipher_suites: list T.cipher_suite;
  start_signature_schemes: list T.signature_scheme;
}

type traffic_key_material = {
  traffic_secret: K.traffic_secret;
  traffic_key: C.aead_key;
  traffic_iv: C.aead_nonce;
}

type key_schedule_state = {
  ks_early_secret: option C.secret;
  ks_shared_secret: option C.x25519_shared_secret;
  ks_handshake_secret: option C.secret;
  ks_master_secret: option C.secret;
  ks_client_handshake_traffic: option traffic_key_material;
  ks_server_handshake_traffic: option traffic_key_material;
  ks_client_application_traffic: option traffic_key_material;
  ks_server_application_traffic: option traffic_key_material;
  ks_exporter_master_secret: option C.secret;
  ks_resumption_master_secret: option C.secret;
}

let empty_key_schedule_state : key_schedule_state = {
  ks_early_secret = None;
  ks_shared_secret = None;
  ks_handshake_secret = None;
  ks_master_secret = None;
  ks_client_handshake_traffic = None;
  ks_server_handshake_traffic = None;
  ks_client_application_traffic = None;
  ks_server_application_traffic = None;
  ks_exporter_master_secret = None;
  ks_resumption_master_secret = None;
}

type handshake_buffer_state = {
  hb_client_hello_bytes: B.bytes;
  hb_server_hello_bytes: B.bytes;
  hb_encrypted_server_handshake_bytes: B.bytes;
  hb_encrypted_server_handshake_parsed: nat;
  hb_certificate_leaf_der: option B.bytes;
  hb_certificate_verify_input: option B.bytes;
}

let empty_handshake_buffer_state : handshake_buffer_state = {
  hb_client_hello_bytes = B.empty;
  hb_server_hello_bytes = B.empty;
  hb_encrypted_server_handshake_bytes = B.empty;
  hb_encrypted_server_handshake_parsed = 0;
  hb_certificate_leaf_der = None;
  hb_certificate_verify_input = None;
}

type handshake_state = {
  hs_start: option handshake_start;
  hs_client_hello: option M.client_hello;
  hs_server_hello: option M.server_hello;
  hs_encrypted_extensions: option M.encrypted_extensions;
  hs_certificate: option M.certificate_msg;
  hs_validated_peer: option X.peer_identity;
  hs_certificate_verify: option M.certificate_verify;
  hs_certificate_verify_verified: bool;
  hs_server_finished: option M.finished;
  hs_server_finished_verified: bool;
  hs_client_finished: option M.finished;
  hs_transcript: Tr.transcript;
  hs_buffers: handshake_buffer_state;
  hs_keys: key_schedule_state;
}

let empty_handshake_state : handshake_state = {
  hs_start = None;
  hs_client_hello = None;
  hs_server_hello = None;
  hs_encrypted_extensions = None;
  hs_certificate = None;
  hs_validated_peer = None;
  hs_certificate_verify = None;
  hs_certificate_verify_verified = false;
  hs_server_finished = None;
  hs_server_finished_verified = false;
  hs_client_finished = None;
  hs_transcript = Tr.empty;
  hs_buffers = empty_handshake_buffer_state;
  hs_keys = empty_key_schedule_state;
}

type record_layer_state = {
  record_read: R.direction_state;
  record_write: R.direction_state;
}

let initial_record_layer_state : record_layer_state = {
  record_read = R.initial_direction_state;
  record_write = R.initial_direction_state;
}

type application_state = {
  app_log: CL.app_log;
  app_pending_plaintext: B.bytes;
  app_pending_source_record: B.bytes;
  app_pending_source_offset: nat;
  app_pending_received_raw: B.bytes;
}

let empty_application_state : application_state = {
  app_log = CL.empty_app_log;
  app_pending_plaintext = B.empty;
  app_pending_source_record = B.empty;
  app_pending_source_offset = 0;
  app_pending_received_raw = B.empty;
}

let pending_application_consistent (app:application_state) : prop =
  app.app_pending_source_offset <= B.length app.app_pending_source_record /\
  Seq.equal app.app_pending_plaintext
    (CL.raw_slice
      app.app_pending_source_record
      app.app_pending_source_offset
      (B.length app.app_pending_source_record))

type connection_model = {
  model_config: connection_config;
  model_control: connection_control_state;
  model_record: record_layer_state;
  model_handshake: handshake_state;
  model_application: application_state;
  model_failure: option T.tls_error;
}

let initial_model (cfg:connection_config) : connection_model = {
  model_config = cfg;
  model_control = ControlNew;
  model_record = initial_record_layer_state;
  model_handshake = empty_handshake_state;
  model_application = empty_application_state;
  model_failure = None;
}

type traffic_epoch =
  | TrafficHandshake
  | TrafficApplication

type traffic_direction =
  | TrafficWrite
  | TrafficRead

type traffic_key_install = {
  install_epoch: traffic_epoch;
  install_direction: traffic_direction;
  install_material: traffic_key_material;
}

type local_event =
  | LocalStartHandshake of handshake_start
  | LocalDeriveSharedSecret of C.x25519_shared_secret
  | LocalInstallTrafficKeys of traffic_key_install
  | LocalValidateCertificate of X.peer_identity
  | LocalVerifyCertificateSignature of M.certificate_verify
  | LocalVerifyFinished of M.finished
  | LocalDeliverApplicationData of B.bytes
  | LocalFail of T.tls_error

type conn_event =
  | ConnNetworkEvent of directed_message M.tls_message
  | ConnLocalEvent of local_event

type connection_state = {
  cs_model: connection_model;
  cs_wire_log: wire_log;
  cs_event_log: list conn_event;
}

let initial (cfg:connection_config) : connection_state = {
  cs_model = initial_model cfg;
  cs_wire_log = empty_wire_log;
  cs_event_log = [];
}

let sent_tls_event (msg:M.tls_message) : conn_event =
  ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = msg }

let received_tls_event (msg:M.tls_message) : conn_event =
  ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = msg }

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
     | CL.Sent, M.TlsAlert T.CloseNotify -> Some S.SendCloseNotify
     | CL.Received, M.TlsAlert T.CloseNotify -> Some S.RecvCloseNotify
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

type raw_message_relation =
  wire_log -> list M.tls_message -> list M.tls_message -> prop

let connection_state_consistent_with
  (raw_messages:raw_message_relation)
  (st:connection_state)
  : prop =
  raw_messages st.cs_wire_log
    (sent_tls_messages st.cs_event_log)
    (received_tls_messages st.cs_event_log) /\
  st.cs_model.model_application.app_log == app_log_of_conn_events st.cs_event_log /\
  pending_application_consistent st.cs_model.model_application /\
  S.step_many S.initial (state_machine_events st.cs_event_log) ==
    Some (abstract_state_of_model st.cs_model)

let connection_state_consistent (st:connection_state) : prop =
  connection_state_consistent_with (fun _ _ _ -> True) st

type connection_delta = {
  delta_event: conn_event;
  delta_raw_sent: B.bytes;
  delta_raw_received: B.bytes;
  delta_next_model: connection_model;
}

let apply_delta (st:connection_state) (delta:connection_delta) : connection_state =
  {
    cs_model = delta.delta_next_model;
    cs_wire_log = {
      CL.raw_sent = B.append st.cs_wire_log.CL.raw_sent delta.delta_raw_sent;
      CL.raw_received = B.append st.cs_wire_log.CL.raw_received delta.delta_raw_received;
    };
    cs_event_log = st.cs_event_log @ [delta.delta_event];
  }

let connection_state_single_step : RTC.binrel connection_state =
  fun st0 st1 -> exists delta. st1 == apply_delta st0 delta

let connection_state_evolves : RTC.preorder connection_state =
  RTC.closure connection_state_single_step
