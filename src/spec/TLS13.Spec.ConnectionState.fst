module TLS13.Spec.ConnectionState

(**
  Audit-facing TLS connection-state specification.

  This module contains the core state, transition, log, and invariant
  definitions. Proof-only preservation and projection lemmas live in
  TLS13.ConnectionState.Lemmas so auditors can review the executable/spec model
  without wading through proof engineering.
**)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module H = TLS13.Handshake.Spec
module ID = FStar.IndefiniteDescription
module K = TLS13.Keys
module M = TLS13.Messages
module R = TLS13.Record.Spec
module RTC = FStar.ReflexiveTransitiveClosure
module S = TLS13.StateMachine
module Seq = FStar.Seq
module T = TLS13.Types
module Tr = TLS13.Transcript
module W = TLS13.Wire.Spec
module X = TLS13.X509.Spec

open FStar.List.Tot

type wire_log = CL.raw_io_log
type direction = CL.direction
type directed_message (a:Type0) = CL.directed_message a

let empty_wire_log : wire_log = CL.empty_raw_io_log

type endpoint_role =
  | ClientEndpoint
  | ServerEndpoint

type server_credential_identity = B.bytes

type server_config = {
  server_certificate_chain: B.bytes;
  server_credential_identity: server_credential_identity;
  server_allowed_signature_schemes: list T.signature_scheme;
  server_supported_cipher_suites: list T.cipher_suite;
  server_supported_groups: list T.named_group;
  server_sni_policy: option T.hostname;
}

type connection_config = {
  config_role: endpoint_role;
  config_server_name: T.hostname;
  config_trust_store: X.trust_store;
  config_validation_time: X.validation_time;
  config_cipher_suites: list T.cipher_suite;
  config_signature_schemes: list T.signature_scheme;
  config_server: option server_config;
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

let traffic_key_material_for_secret (secret:K.traffic_secret) : traffic_key_material =
  {
    traffic_secret = secret;
    traffic_key = K.derive_aead_key secret;
    traffic_iv = K.derive_aead_iv secret;
  }

let updated_traffic_key_material
  (old:traffic_key_material)
  : traffic_key_material =
  traffic_key_material_for_secret
    (K.application_traffic_secret_update old.traffic_secret)

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
  app_key_update_response_pending: bool;
}

let empty_application_state : application_state = {
  app_log = CL.empty_app_log;
  app_pending_plaintext = B.empty;
  app_pending_source_record = B.empty;
  app_pending_source_offset = 0;
  app_pending_received_raw = B.empty;
  app_key_update_response_pending = false;
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

type traffic_label =
  | ClientTraffic
  | ServerTraffic

type base_secret_id =
  | EarlySecret
  | HandshakeSecret
  | MasterSecret

type labeled_traffic_epoch = {
  traffic_id_epoch: traffic_epoch;
  traffic_id_label: traffic_label;
}

type traffic_update_id = {
  traffic_update_label: traffic_label;
  traffic_update_generation: nat;
}

type derived_key_id =
  | BaseSecret of base_secret_id
  | TrafficSecret of labeled_traffic_epoch
  | TrafficKey of labeled_traffic_epoch
  | TrafficIV of labeled_traffic_epoch
  | FinishedKey of traffic_label
  | TrafficUpdateSecret of traffic_update_id
  | ExporterMasterSecret
  | ResumptionMasterSecret

type key_derivation_checkpoint =
  | DeriveHandshakeTraffic
  | DeriveApplicationTraffic
  | DeriveTrafficUpdate of traffic_update_id

type traffic_direction =
  | TrafficWrite
  | TrafficRead

let traffic_label_for_endpoint_direction
  (role:endpoint_role)
  (dir:traffic_direction)
  : traffic_label =
  match role, dir with
  | ClientEndpoint, TrafficWrite -> ClientTraffic
  | ClientEndpoint, TrafficRead -> ServerTraffic
  | ServerEndpoint, TrafficWrite -> ServerTraffic
  | ServerEndpoint, TrafficRead -> ClientTraffic

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

let fail_model (model:connection_model) (err:T.tls_error) : connection_model =
  { model with model_control = ControlFailed err; model_failure = Some err }

let with_handshake_stage
  (model:connection_model)
  (hs:handshake_state)
  (stage:handshake_stage)
  : connection_model =
  { model with model_control = ControlHandshaking stage; model_handshake = hs }

let with_handshake_state
  (model:connection_model)
  (hs:handshake_state)
  : connection_model =
  { model with model_handshake = hs }

let append_handshake_to_transcript
  (hs:handshake_state)
  (msg:M.handshake_msg)
  : GTot handshake_state =
  { hs with hs_transcript = Tr.append hs.hs_transcript (W.serialize_handshake msg) }

let received_key_update_pending
  (app:application_state)
  (req:M.key_update_request)
  : application_state =
  match req with
  | M.UpdateRequested ->
    { app with app_key_update_response_pending = true }
  | M.UpdateNotRequested ->
    app

let rec advance_direction_records
  (st:R.direction_state)
  (n:nat)
  : Tot R.direction_state
        (decreases n)
  =
  if n = 0 then st
  else R.next_seq (advance_direction_records st (n - 1))

let install_client_application_write_after_finished
  (record:record_layer_state)
  (keys:key_schedule_state)
  : record_layer_state =
  match keys.ks_client_application_traffic with
  | Some material ->
    {
      record with
        record_write =
          R.install_keys
            (R.next_seq record.record_write)
            R.Application
            material.traffic_key
            material.traffic_iv;
    }
  | None ->
    {
      record with
        record_write = R.next_seq record.record_write;
    }

let traffic_record_epoch (epoch:traffic_epoch) : R.epoch =
  match epoch with
  | TrafficHandshake -> R.Handshake
  | TrafficApplication -> R.Application

let update_key_schedule_with_label
  (keys:key_schedule_state)
  (epoch:traffic_epoch)
  (label:traffic_label)
  (material:traffic_key_material)
  : key_schedule_state =
  match epoch, label with
  | TrafficHandshake, ClientTraffic ->
    { keys with ks_client_handshake_traffic = Some material }
  | TrafficHandshake, ServerTraffic ->
    { keys with ks_server_handshake_traffic = Some material }
  | TrafficApplication, ClientTraffic ->
    { keys with ks_client_application_traffic = Some material }
  | TrafficApplication, ServerTraffic ->
    { keys with ks_server_application_traffic = Some material }

let update_key_schedule_with_install_for_role
  (role:endpoint_role)
  (keys:key_schedule_state)
  (install:traffic_key_install)
  : key_schedule_state =
  update_key_schedule_with_label
    keys
    install.install_epoch
    (traffic_label_for_endpoint_direction role install.install_direction)
    install.install_material

let update_key_schedule_with_install
  (keys:key_schedule_state)
  (install:traffic_key_install)
  : key_schedule_state =
  update_key_schedule_with_install_for_role ClientEndpoint keys install

let install_record_keys
  (record:record_layer_state)
  (install:traffic_key_install)
  : record_layer_state =
  let material = install.install_material in
  let epoch = traffic_record_epoch install.install_epoch in
  match install.install_epoch, install.install_direction with
  | TrafficApplication, TrafficWrite ->
    record
  | _, TrafficWrite ->
    {
      record with
        record_write =
          R.install_keys record.record_write epoch material.traffic_key material.traffic_iv;
    }
  | _, TrafficRead ->
    {
      record with
        record_read =
          R.install_keys record.record_read epoch material.traffic_key material.traffic_iv;
    }

let traffic_material_matches_record_direction
  (material:traffic_key_material)
  (st:R.direction_state)
  : prop =
  st.R.key == Some material.traffic_key /\
  st.R.static_iv == Some material.traffic_iv

let traffic_material_option_matches_record_direction
  (material:option traffic_key_material)
  (st:R.direction_state)
  : prop =
  match material with
  | Some material -> traffic_material_matches_record_direction material st
  | None -> False

let traffic_material_for_label
  (keys:key_schedule_state)
  (epoch:traffic_epoch)
  (label:traffic_label)
  : option traffic_key_material =
  match epoch, label with
  | TrafficHandshake, ClientTraffic -> keys.ks_client_handshake_traffic
  | TrafficHandshake, ServerTraffic -> keys.ks_server_handshake_traffic
  | TrafficApplication, ClientTraffic -> keys.ks_client_application_traffic
  | TrafficApplication, ServerTraffic -> keys.ks_server_application_traffic

let record_keys_match_key_schedule_for_role
  (role:endpoint_role)
  (dir:traffic_direction)
  (control:connection_control_state)
  (keys:key_schedule_state)
  (st:R.direction_state)
  : prop =
  match st.R.epoch with
  | R.Initial ->
    st.R.key == None /\ st.R.static_iv == None
  | R.Handshake ->
    traffic_material_option_matches_record_direction
      (traffic_material_for_label
       keys
       TrafficHandshake
       (traffic_label_for_endpoint_direction role dir))
      st
  | R.Application ->
    (match dir, control with
     | TrafficWrite, ControlHandshaking _ ->
       True
     | _, _ ->
       traffic_material_option_matches_record_direction
        (traffic_material_for_label
          keys
          TrafficApplication
          (traffic_label_for_endpoint_direction role dir))
        st)

let record_read_keys_match_key_schedule
  (keys:key_schedule_state)
  (st:R.direction_state)
  : prop =
  record_keys_match_key_schedule_for_role
    ClientEndpoint
    TrafficRead
    ControlApplicationData
    keys
    st

let record_read_key_schedule_projection_for_role
  (role:endpoint_role)
  (model:connection_model)
  : prop =
  match model.model_control with
  | ControlFailed _ -> True
  | _ ->
    let keys = model.model_handshake.hs_keys in
    let st = model.model_record.record_read in
    match st.R.epoch with
    | R.Initial ->
      st.R.key == None /\ st.R.static_iv == None
    | R.Handshake ->
      exists material.
       traffic_material_for_label
         keys
         TrafficHandshake
         (traffic_label_for_endpoint_direction role TrafficRead) == Some material /\
       traffic_material_matches_record_direction material st
    | R.Application ->
      exists material.
       traffic_material_for_label
         keys
         TrafficApplication
         (traffic_label_for_endpoint_direction role TrafficRead) == Some material /\
       traffic_material_matches_record_direction material st

let record_read_key_schedule_projection
  (model:connection_model)
  : prop =
  record_read_key_schedule_projection_for_role ClientEndpoint model

let record_write_keys_match_key_schedule
  (control:connection_control_state)
  (keys:key_schedule_state)
  (st:R.direction_state)
  : prop =
  record_keys_match_key_schedule_for_role
    ClientEndpoint
    TrafficWrite
    control
    keys
    st

let record_write_key_schedule_projection_for_role
  (role:endpoint_role)
  (model:connection_model)
  : prop =
  match model.model_control with
  | ControlFailed _ -> True
  | _ ->
    let keys = model.model_handshake.hs_keys in
    let st = model.model_record.record_write in
    match st.R.epoch with
    | R.Initial ->
      st.R.key == None /\ st.R.static_iv == None
    | R.Handshake ->
      exists material.
        traffic_material_for_label
          keys
          TrafficHandshake
          (traffic_label_for_endpoint_direction role TrafficWrite) == Some material /\
        traffic_material_matches_record_direction material st
    | R.Application ->
      (match model.model_control with
       | ControlHandshaking _ ->
         True
       | _ ->
         exists material.
           traffic_material_for_label
             keys
             TrafficApplication
             (traffic_label_for_endpoint_direction role TrafficWrite) == Some material /\
           traffic_material_matches_record_direction material st)

let record_write_key_schedule_projection
  (model:connection_model)
  : prop =
  record_write_key_schedule_projection_for_role ClientEndpoint model

let model_record_keys_consistent
  (model:connection_model)
  : prop =
  match model.model_control with
  | ControlFailed _ -> True
  | _ ->
    let keys = model.model_handshake.hs_keys in
    record_read_keys_match_key_schedule keys model.model_record.record_read /\
    record_write_keys_match_key_schedule
      model.model_control
      keys
      model.model_record.record_write

let step_local_event (model:connection_model) (ev:local_event) : GTot (option connection_model) =
  let hs = model.model_handshake in
  match ev, model.model_control with
  | LocalStartHandshake start, ControlNew ->
    Some (with_handshake_stage model { hs with hs_start = Some start } HsStarted)
  | LocalDeriveSharedSecret shared, ControlHandshaking HsServerHelloReceived ->
    let early = K.early_secret B.empty in
    let handshake = K.handshake_secret early shared in
    let master = K.master_secret handshake in
    let keys = { hs.hs_keys with ks_shared_secret = Some shared } in
    Some (with_handshake_state
      model
      { hs with
          hs_keys =
            { keys with
                ks_early_secret = Some early;
                ks_handshake_secret = Some handshake;
                ks_master_secret = Some master;
            };
      })
  | LocalInstallTrafficKeys install, ControlHandshaking _ ->
    let keys = update_key_schedule_with_install hs.hs_keys install in
    Some {
      model with
        model_record = install_record_keys model.model_record install;
        model_handshake = { hs with hs_keys = keys };
    }
  | LocalValidateCertificate peer, ControlHandshaking HsCertificateReceived ->
    Some (with_handshake_stage model { hs with hs_validated_peer = Some peer } HsCertificateValidated)
  | LocalVerifyCertificateSignature cv, ControlHandshaking HsCertificateVerifyReceived ->
    Some (with_handshake_stage
      model
      { hs with
          hs_certificate_verify = Some cv;
          hs_certificate_verify_verified = true;
      }
      HsCertificateVerifyVerified)
  | LocalVerifyFinished fin, ControlHandshaking HsServerFinishedReceived ->
    Some (with_handshake_stage
      model
      (append_handshake_to_transcript
        { hs with
            hs_server_finished = Some fin;
            hs_server_finished_verified = true;
        }
        (M.Finished fin))
      HsServerFinishedVerified)
  | LocalDeliverApplicationData bytes, ControlApplicationData ->
    let app = model.model_application in
    Some {
      model with
        model_application =
          { app with app_log = CL.append_app_received app.app_log bytes };
    }
  | LocalFail err, _ ->
    Some (fail_model model err)
  | _, _ ->
    None

let step_handshake_message
  (model:connection_model)
  (dir:direction)
  (msg:M.handshake_msg)
  : GTot (option connection_model) =
  let hs = model.model_handshake in
  match dir, msg, model.model_control with
  | CL.Sent, M.ClientHello ch, ControlHandshaking HsStarted ->
    let hs' =
      append_handshake_to_transcript
        { hs with
            hs_client_hello = Some ch;
            hs_buffers =
              { hs.hs_buffers with hb_client_hello_bytes = W.serialize_handshake msg };
        }
        msg in
    Some (with_handshake_stage model hs' HsClientHelloSent)
  | CL.Received, M.ServerHello sh, ControlHandshaking HsClientHelloSent ->
    let hs' =
      append_handshake_to_transcript
        { hs with
            hs_server_hello = Some sh;
            hs_buffers =
              { hs.hs_buffers with hb_server_hello_bytes = W.serialize_handshake msg };
        }
        msg in
    Some (with_handshake_stage model hs' HsServerHelloReceived)
  | CL.Received, M.EncryptedExtensions ee, ControlHandshaking HsServerHelloReceived ->
    Some (with_handshake_stage
      { model with
          model_record =
            { model.model_record with
                record_read = R.next_seq model.model_record.record_read;
            };
      }
      (append_handshake_to_transcript { hs with hs_encrypted_extensions = Some ee } msg)
      HsEncryptedExtensionsReceived)
  | CL.Received, M.Certificate cert, ControlHandshaking HsEncryptedExtensionsReceived ->
    Some (with_handshake_stage
      { model with
          model_record =
            { model.model_record with
                record_read = R.next_seq model.model_record.record_read;
            };
      }
      (append_handshake_to_transcript
        { hs with
            hs_certificate = Some cert;
            hs_buffers =
            { hs.hs_buffers with
                hb_certificate_leaf_der =
                  (match cert.M.chain with
                   | leaf :: _ -> Some leaf
                   | [] -> None);
            };
        }
        msg)
      HsCertificateReceived)
  | CL.Received, M.CertificateVerify cv, ControlHandshaking HsCertificateValidated ->
    Some (with_handshake_stage
      { model with
          model_record =
            { model.model_record with
                record_read = R.next_seq model.model_record.record_read;
            };
      }
      (append_handshake_to_transcript
        { hs with
            hs_certificate_verify = Some cv;
            hs_buffers =
            { hs.hs_buffers with
                hb_certificate_verify_input =
                  Some (H.certificate_verify_input (Tr.hash hs.hs_transcript));
            };
        }
        msg)
      HsCertificateVerifyReceived)
  | CL.Received, M.Finished fin, ControlHandshaking HsCertificateVerifyVerified ->
    Some (with_handshake_stage
      { model with
          model_record =
            { model.model_record with
                record_read = R.next_seq model.model_record.record_read;
            };
      }
      { hs with hs_server_finished = Some fin }
      HsServerFinishedReceived)
  | CL.Sent, M.Finished fin, ControlHandshaking HsServerFinishedVerified ->
    Some {
      model with
        model_control = ControlApplicationData;
        model_record =
          install_client_application_write_after_finished
            model.model_record
            hs.hs_keys;
        model_handshake =
          append_handshake_to_transcript { hs with hs_client_finished = Some fin } msg;
    }
  | CL.Received, M.HelloRetryRequest, ControlHandshaking HsClientHelloSent ->
    Some (fail_model model T.HelloRetryRequestRejected)
  | _, _, _ ->
    None

let step_tls_message
  (model:connection_model)
  (dir:direction)
  (msg:M.tls_message)
  : GTot (option connection_model) =
  let hs = model.model_handshake in
  match msg, model.model_control with
  | M.TlsHandshake handshake_msg, _ -> step_handshake_message model dir handshake_msg
  | M.TlsApplicationData bytes, ControlApplicationData ->
    let app = model.model_application in
    (match dir with
     | CL.Sent ->
       Some {
         model with
           model_record = {
             model.model_record with
               record_write =
                 advance_direction_records
                   model.model_record.record_write
                   (S.application_data_record_count bytes);
           };
           model_application =
             { app with app_log = CL.append_app_sent app.app_log bytes };
       }
     | CL.Received ->
       Some {
         model with
           model_record = {
             model.model_record with
               record_read = R.next_seq model.model_record.record_read;
           };
           model_application =
             { app with app_log = CL.append_app_received app.app_log bytes };
       })
  | M.TlsIgnoredPostHandshake _, ControlApplicationData ->
    (match dir with
     | CL.Received ->
       Some {
        model with
          model_record = {
            model.model_record with
              record_read = R.next_seq model.model_record.record_read;
          };
       }
     | CL.Sent -> None)
  | M.TlsKeyUpdate req, ControlApplicationData ->
   (match dir, req with
    | CL.Received, _ ->
      (match hs.hs_keys.ks_server_application_traffic with
       | Some old_server_app ->
         let new_server_app = updated_traffic_key_material old_server_app in
         Some {
           model with
             model_record = {
               model.model_record with
                 record_read =
                   R.install_keys
                     (R.next_seq model.model_record.record_read)
                     R.Application
                     new_server_app.traffic_key
                     new_server_app.traffic_iv;
             };
             model_handshake = {
               hs with
                 hs_keys = {
                   hs.hs_keys with
                     ks_server_application_traffic = Some new_server_app;
                 };
             };
             model_application =
               received_key_update_pending model.model_application req;
         }
       | None -> None)
    | CL.Sent, M.UpdateNotRequested ->
      (match hs.hs_keys.ks_client_application_traffic with
       | Some old_client_app ->
         if model.model_application.app_key_update_response_pending then
           let new_client_app = updated_traffic_key_material old_client_app in
           Some {
             model with
               model_record = {
                 model.model_record with
                   record_write =
                     R.install_keys
                       (R.next_seq model.model_record.record_write)
                       R.Application
                       new_client_app.traffic_key
                       new_client_app.traffic_iv;
               };
               model_handshake = {
                 hs with
                   hs_keys = {
                     hs.hs_keys with
                       ks_client_application_traffic = Some new_client_app;
                   };
               };
               model_application = {
                 model.model_application with
                   app_key_update_response_pending = false;
               };
           }
         else None
       | None -> None)
    | CL.Sent, M.UpdateRequested ->
      None)
  | M.TlsAlert T.CloseNotify, ControlApplicationData ->
    (match dir with
     | CL.Sent ->
       Some {
         model with
           model_control = ControlClosing;
           model_record = {
             model.model_record with
               record_write = R.next_seq model.model_record.record_write;
           };
       }
     | CL.Received ->
       Some {
         model with
           model_control = ControlClosed;
           model_record = {
             model.model_record with
               record_read = R.next_seq model.model_record.record_read;
           };
       })
  | M.TlsAlert T.CloseNotify, ControlClosing ->
    (match dir with
     | CL.Received ->
       Some {
         model with
           model_control = ControlClosed;
           model_record = {
             model.model_record with
               record_read = R.next_seq model.model_record.record_read;
           };
       }
     | CL.Sent -> None)
  | M.TlsAlert alert, _ ->
    Some (fail_model model (T.AlertError alert))
  | M.TlsChangeCipherSpec, ControlHandshaking _ ->
    Some model
  | _, _ ->
    None

let step_model (model:connection_model) (ev:conn_event) : GTot (option connection_model) =
  match ev with
  | ConnNetworkEvent msg ->
    step_tls_message model msg.CL.message_direction msg.CL.message_value
  | ConnLocalEvent local ->
    step_local_event model local

let rec step_model_many
  (model:connection_model)
  (events:list conn_event)
  : GTot (option connection_model)
        (decreases events)
  =
  match events with
  | [] -> Some model
  | ev :: rest ->
    (match step_model model ev with
     | Some model' -> step_model_many model' rest
     | None -> None)

let model_after_events (cfg:connection_config) (events:list conn_event)
  : GTot (option connection_model) =
  step_model_many (initial_model cfg) events

let rec cipher_suite_offered (suites:list T.cipher_suite) (suite:T.cipher_suite)
  : Tot prop
        (decreases suites)
  =
  match suites with
  | [] -> False
  | offered :: rest -> offered == suite \/ cipher_suite_offered rest suite

let start_matches_config (cfg:connection_config) (start:handshake_start) : prop =
  Seq.equal start.start_server_name cfg.config_server_name /\
  start.start_cipher_suites == cfg.config_cipher_suites /\
  start.start_signature_schemes == cfg.config_signature_schemes

let handshake_start_key_share_consistent (start:handshake_start) : prop =
  match start.start_client_key_share_private with
  | Some sk ->
    Seq.equal
      start.start_client_key_share_public
      (C.x25519_public_from_private sk)
  | None ->
    True

let client_hello_matches_start (start:handshake_start) (ch:M.client_hello) : prop =
  Seq.equal ch.M.random start.start_client_random /\
  ch.M.server_name == Some start.start_server_name /\
  Seq.equal ch.M.key_share start.start_client_key_share_public /\
  ch.M.cipher_suites == start.start_cipher_suites /\
  ch.M.signature_schemes == start.start_signature_schemes

let traffic_secret_for_label
  (hs:handshake_state)
  (epoch:traffic_epoch)
  (label:traffic_label)
  : GTot (option K.traffic_secret) =
  match epoch, label with
  | TrafficHandshake, ClientTraffic ->
    (match hs.hs_keys.ks_handshake_secret with
     | Some secret -> Some (K.client_handshake_traffic_secret secret (Tr.hash hs.hs_transcript))
     | None -> None)
  | TrafficHandshake, ServerTraffic ->
    (match hs.hs_keys.ks_handshake_secret with
     | Some secret -> Some (K.server_handshake_traffic_secret secret (Tr.hash hs.hs_transcript))
     | None -> None)
  | TrafficApplication, ClientTraffic ->
    (match hs.hs_keys.ks_master_secret with
     | Some secret -> Some (K.client_application_traffic_secret secret (Tr.hash hs.hs_transcript))
     | None -> None)
  | TrafficApplication, ServerTraffic ->
    (match hs.hs_keys.ks_master_secret with
     | Some secret -> Some (K.server_application_traffic_secret secret (Tr.hash hs.hs_transcript))
     | None -> None)

let expected_traffic_secret_for_role
  (role:endpoint_role)
  (hs:handshake_state)
  (epoch:traffic_epoch)
  (dir:traffic_direction)
  : GTot (option K.traffic_secret) =
  traffic_secret_for_label hs epoch (traffic_label_for_endpoint_direction role dir)

let expected_traffic_secret
  (hs:handshake_state)
  (epoch:traffic_epoch)
  (dir:traffic_direction)
  : GTot (option K.traffic_secret) =
  expected_traffic_secret_for_role ClientEndpoint hs epoch dir

let traffic_install_matches_key_schedule
  (hs:handshake_state)
  (install:traffic_key_install)
  : GTot prop =
  match expected_traffic_secret hs install.install_epoch install.install_direction with
  | Some secret ->
    install.install_material == traffic_key_material_for_secret secret
  | None -> False

let traffic_install_allowed_at_stage
  (stage:handshake_stage)
  (install:traffic_key_install)
  : prop =
  match install.install_epoch with
  | TrafficHandshake -> stage == HsServerHelloReceived
  | TrafficApplication -> stage == HsServerFinishedVerified

let legal_local_event (model:connection_model) (ev:local_event) : GTot prop =
  let hs = model.model_handshake in
  match ev, model.model_control with
  | LocalStartHandshake start, ControlNew ->
    start_matches_config model.model_config start /\
    handshake_start_key_share_consistent start
  | LocalDeriveSharedSecret shared, ControlHandshaking HsServerHelloReceived ->
    (match hs.hs_start, hs.hs_server_hello with
     | Some start, Some sh ->
       handshake_start_key_share_consistent start /\
       (match start.start_client_key_share_private with
        | Some sk -> C.x25519_shared sk sh.M.key_share == Some shared
        | None -> False)
     | _, _ -> False)
  | LocalInstallTrafficKeys install, ControlHandshaking stage ->
    traffic_install_allowed_at_stage stage install /\
    traffic_install_matches_key_schedule hs install
  | LocalValidateCertificate peer, ControlHandshaking HsCertificateReceived ->
    (match hs.hs_certificate with
     | Some cert ->
       X.validate_chain
         model.model_config.config_server_name
         model.model_config.config_validation_time
         model.model_config.config_trust_store
         cert.M.chain == Some peer
     | None -> False)
  | LocalVerifyCertificateSignature cv, ControlHandshaking HsCertificateVerifyReceived ->
    (match hs.hs_validated_peer, hs.hs_certificate_verify, hs.hs_buffers.hb_certificate_verify_input with
     | Some peer, Some stored_cv, Some input ->
       stored_cv == cv /\
       C.verify_signature cv.M.scheme peer.X.leaf_public_key input cv.M.signature
     | _, _, _ -> False)
  | LocalVerifyFinished fin, ControlHandshaking HsServerFinishedReceived ->
    (match hs.hs_server_finished, hs.hs_keys.ks_server_handshake_traffic with
     | Some stored_fin, Some server_hs ->
       stored_fin == fin /\
       H.verify_finished server_hs.traffic_secret (Tr.hash hs.hs_transcript) fin
     | _, _ -> False)
  | LocalDeliverApplicationData bytes, ControlApplicationData ->
    exists pending.
      Seq.equal model.model_application.app_pending_plaintext (B.append bytes pending)
  | LocalFail _, _ ->
    True
  | _, _ ->
    False

let legal_handshake_message
  (model:connection_model)
  (dir:direction)
  (msg:M.handshake_msg)
  : GTot prop =
  let hs = model.model_handshake in
  match dir, msg, model.model_control with
  | CL.Sent, M.ClientHello ch, ControlHandshaking HsStarted ->
    (match hs.hs_start with
     | Some start -> client_hello_matches_start start ch
     | None -> False)
  | CL.Received, M.ServerHello sh, ControlHandshaking HsClientHelloSent ->
    H.is_supported_cipher_suite sh.M.cipher_suite /\
    (match hs.hs_start with
     | Some start -> cipher_suite_offered start.start_cipher_suites sh.M.cipher_suite
     | None -> False)
  | CL.Received, M.EncryptedExtensions _, ControlHandshaking HsServerHelloReceived ->
    Some? hs.hs_keys.ks_server_handshake_traffic
  | CL.Received, M.Certificate cert, ControlHandshaking HsEncryptedExtensionsReceived ->
    cert.M.chain <> []
  | CL.Received, M.CertificateVerify _, ControlHandshaking HsCertificateValidated ->
    Some? hs.hs_validated_peer
  | CL.Received, M.Finished _, ControlHandshaking HsCertificateVerifyVerified ->
    Some? hs.hs_keys.ks_server_handshake_traffic
  | CL.Sent, M.Finished _, ControlHandshaking HsServerFinishedVerified ->
    Some? hs.hs_keys.ks_client_handshake_traffic /\
    Some? hs.hs_keys.ks_client_application_traffic /\
    Some? hs.hs_keys.ks_server_application_traffic
  | CL.Received, M.HelloRetryRequest, ControlHandshaking HsClientHelloSent ->
    True
  | _, _, _ ->
    False

let legal_tls_message
  (model:connection_model)
  (dir:direction)
  (msg:M.tls_message)
  : GTot prop =
  let hs = model.model_handshake in
  match msg, model.model_control with
  | M.TlsHandshake handshake_msg, _ ->
    legal_handshake_message model dir handshake_msg
  | M.TlsApplicationData _, ControlApplicationData ->
    (match dir with
     | CL.Sent -> Some? hs.hs_keys.ks_client_application_traffic
     | CL.Received -> Some? hs.hs_keys.ks_server_application_traffic)
  | M.TlsIgnoredPostHandshake _, ControlApplicationData ->
    dir == CL.Received /\ Some? hs.hs_keys.ks_server_application_traffic
  | M.TlsKeyUpdate req, ControlApplicationData ->
    (match dir, req with
     | CL.Received, _ ->
       Some? hs.hs_keys.ks_server_application_traffic
     | CL.Sent, M.UpdateNotRequested ->
       Some? hs.hs_keys.ks_client_application_traffic /\
       model.model_application.app_key_update_response_pending
     | CL.Sent, M.UpdateRequested ->
       False)
  | M.TlsAlert T.CloseNotify, ControlApplicationData ->
    True
  | M.TlsAlert T.CloseNotify, ControlClosing ->
    dir == CL.Received
  | M.TlsAlert _, _ ->
    True
  | M.TlsChangeCipherSpec, ControlHandshaking _ ->
    True
  | _, _ ->
    False

let legal_event (model:connection_model) (ev:conn_event) : GTot prop =
  match ev with
  | ConnNetworkEvent msg ->
    legal_tls_message model msg.CL.message_direction msg.CL.message_value
  | ConnLocalEvent local ->
    legal_local_event model local

let rec model_events_legal
  (model:connection_model)
  (events:list conn_event)
  (final:connection_model)
  : GTot prop
        (decreases events)
  =
  match events with
  | [] -> final == model
  | ev :: rest ->
    legal_event model ev /\
    (match step_model model ev with
     | Some model' -> model_events_legal model' rest final
     | None -> False)

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

let conn_event_transcript_delta (ev:conn_event) : GTot B.bytes =
  match ev with
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Sent, M.TlsHandshake (M.ClientHello ch) ->
       W.serialize_handshake (M.ClientHello ch)
     | CL.Received, M.TlsHandshake (M.ServerHello sh) ->
       W.serialize_handshake (M.ServerHello sh)
     | CL.Received, M.TlsHandshake (M.EncryptedExtensions ee) ->
       W.serialize_handshake (M.EncryptedExtensions ee)
     | CL.Received, M.TlsHandshake (M.Certificate cert) ->
       W.serialize_handshake (M.Certificate cert)
     | CL.Received, M.TlsHandshake (M.CertificateVerify cv) ->
       W.serialize_handshake (M.CertificateVerify cv)
     | CL.Sent, M.TlsHandshake (M.Finished fin) ->
       W.serialize_handshake (M.Finished fin)
     | _, _ -> B.empty)
  | ConnLocalEvent local ->
    (match local with
     | LocalVerifyFinished fin -> W.serialize_handshake (M.Finished fin)
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

let projected_client_application_write_after_finished
  (record:projected_record_layer_state)
  : projected_record_layer_state =
  { record with projected_write = projected_install_keys R.Application }

let projected_record_layer_step
  (record:projected_record_layer_state)
  (ev:conn_event)
  : projected_record_layer_state =
  match ev with
  | ConnLocalEvent local ->
    (match local with
     | LocalInstallTrafficKeys install -> projected_install_record_keys record install
     | _ -> record)
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Received, M.TlsHandshake (M.EncryptedExtensions _)
     | CL.Received, M.TlsHandshake (M.Certificate _)
     | CL.Received, M.TlsHandshake (M.CertificateVerify _)
     | CL.Received, M.TlsHandshake (M.Finished _)
     | CL.Received, M.TlsApplicationData _
     | CL.Received, M.TlsIgnoredPostHandshake _
     | CL.Received, M.TlsAlert T.CloseNotify ->
       { record with projected_read = projected_next_seq record.projected_read }
     | CL.Sent, M.TlsHandshake (M.Finished _) ->
       projected_client_application_write_after_finished record
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
     | CL.Sent, M.TlsAlert T.CloseNotify ->
       { record with projected_write = projected_next_seq record.projected_write }
     | _, _ ->
       record)

let rec projected_record_layer_after_events_from
  (record:projected_record_layer_state)
  (events:list conn_event)
  : Tot projected_record_layer_state
        (decreases events)
=
  match events with
  | [] -> record
  | ev :: rest ->
    projected_record_layer_after_events_from
      (projected_record_layer_step record ev)
      rest

let projected_record_layer_of_conn_events
  (events:list conn_event)
  : Tot projected_record_layer_state =
  projected_record_layer_after_events_from initial_projected_record_layer_state events

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

let connection_state_record_layer_consistent
  (st:connection_state)
  : prop =
  match st.cs_model.model_control with
  | ControlFailed _ -> True
  | _ ->
    projected_record_layer_state_of_record st.cs_model.model_record ==
      projected_record_layer_of_conn_events st.cs_event_log

let connection_state_record_keys_consistent
  (st:connection_state)
  : prop =
  model_record_keys_consistent st.cs_model

let connection_state_layered_log_consistent
  (st:connection_state)
  : prop =
  connection_state_event_log_consistent st /\
  connection_state_transcript_consistent st /\
  connection_state_key_update_pending_consistent st /\
  connection_state_record_layer_consistent st /\
  connection_state_record_keys_consistent st /\
  connection_state_pending_application_consistent st /\
  connection_state_app_log_consistent st

let model_key_update_pending_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : prop =
  model1.model_application.app_key_update_response_pending ==
    key_update_response_pending_step
      model0.model_application.app_key_update_response_pending
      ev

let model_record_layer_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : prop =
  match model1.model_control with
  | ControlFailed _ -> True
  | _ ->
    projected_record_layer_state_of_record model1.model_record ==
      projected_record_layer_step
        (projected_record_layer_state_of_record model0.model_record)
        ev

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

let rec all_records_outer_type
  (outer:T.content_type)
  (records:list M.tls_record)
  : Tot prop
        (decreases records)
  =
  match records with
  | [] -> True
  | record :: rest ->
    record.M.record_outer_type == outer /\
    all_records_outer_type outer rest

let raw_records_exactly
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : GTot prop =
  let parsed = CL.parse_record_prefix raw in
  CL.record_stream_serializes raw parsed /\
  Seq.equal parsed.CL.residual B.empty /\
  length parsed.CL.values == count /\
  all_records_outer_type outer parsed.CL.values

let rec raw_records_segmented
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : Tot prop
        (decreases count)
  =
  if count == 0 then
    Seq.equal raw B.empty
  else
    exists fragment. exists (consumed:nat).
      W.parse_record raw == Some (outer, fragment, consumed) /\
      consumed > 0 /\
      consumed <= B.length raw /\
      raw_records_segmented
        (Seq.slice raw consumed (B.length raw))
        outer
        (count - 1)

let serialized_cleartext_tls_message (msg:M.tls_message) : GTot B.bytes =
  let (content_type, fragment) = W.serialize_tls_message msg in
  W.serialize_record content_type fragment

let record_header_aad (raw:B.bytes) : GTot B.bytes =
  if B.length raw >= 5
  then Seq.slice raw 0 5
  else B.empty

let application_data_record_header (fragment_len:nat) : GTot B.bytes =
  record_header_aad
    (W.serialize_record T.ApplicationData (Seq.create fragment_len 0uy))

let sent_tls_inner_plaintext_fragment (msg:M.tls_message) : GTot B.bytes =
  let (content_type, fragment) = W.serialize_tls_message msg in
  W.serialize_plaintext {
    M.content_type = content_type;
    M.fragment = fragment;
  }

let sent_single_protected_message_seal
  (model:connection_model)
  (msg:M.tls_message)
  (raw:B.bytes)
  : prop =
  exists ciphertext.
    W.parse_record raw == Some (T.ApplicationData, ciphertext, B.length raw) /\
    R.seal
      model.model_record.record_write
      (record_header_aad raw)
      {
        R.content_type = T.ApplicationData;
        R.fragment = sent_tls_inner_plaintext_fragment msg;
      } ==
      Some (ciphertext, R.next_seq model.model_record.record_write)

let cleartext_tls_message_raw (msg:M.tls_message) (raw:B.bytes) : GTot prop =
  match msg with
  | M.TlsHandshake M.HelloRetryRequest ->
    raw_records_exactly raw T.Handshake 1
  | _ ->
    Seq.equal raw (serialized_cleartext_tls_message msg)

let network_message_is_cleartext (dir:direction) (msg:M.tls_message) : bool =
  match dir, msg with
  | CL.Sent, M.TlsHandshake (M.ClientHello _) -> true
  | CL.Received, M.TlsHandshake (M.ServerHello _) -> true
  | CL.Received, M.TlsHandshake M.HelloRetryRequest -> true
  | _, M.TlsChangeCipherSpec -> true
  | _, _ -> false

let protected_record_count (dir:direction) (msg:M.tls_message) : nat =
  match dir, msg with
  | CL.Sent, M.TlsApplicationData bytes -> S.application_data_record_count bytes
  | _, _ -> 1

let sent_event_seal_projection
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  : prop =
  match ev with
  | ConnNetworkEvent msg ->
    if msg.CL.message_direction == CL.Sent &&
       network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false &&
       protected_record_count msg.CL.message_direction msg.CL.message_value == 1
    then sent_single_protected_message_seal model msg.CL.message_value raw_sent
    else True
  | ConnLocalEvent _ ->
    True

let sent_event_nonempty_seal_projection
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  : prop =
  B.length raw_sent == 0 \/
  sent_event_seal_projection model ev raw_sent

let received_record_opened
  (model:connection_model)
  (raw_received:B.bytes)
  (outer_fragment:B.bytes)
  (opened:B.bytes)
  : prop =
  exists read_state'.
    R.open_record
      model.model_record.record_read
      (record_header_aad raw_received)
      outer_fragment ==
      Some (opened, read_state')

let received_single_protected_message_decode
  (model:connection_model)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  : prop =
  exists outer_fragment opened plaintext.
    W.parse_record raw_received ==
      Some (T.ApplicationData, outer_fragment, B.length raw_received) /\
    received_record_opened model raw_received outer_fragment opened /\
    W.parse_plaintext opened == Some plaintext /\
    W.parse_tls_message plaintext.M.content_type plaintext.M.fragment == Some msg

let received_event_decode_projection
  (model:connection_model)
  (ev:conn_event)
  (raw_received:B.bytes)
  : prop =
  match ev with
  | ConnNetworkEvent msg ->
    if msg.CL.message_direction == CL.Received &&
       network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false &&
       protected_record_count msg.CL.message_direction msg.CL.message_value == 1
    then received_single_protected_message_decode model msg.CL.message_value raw_received
    else True
  | ConnLocalEvent _ ->
    True

let received_event_nonempty_decode_projection
  (model:connection_model)
  (ev:conn_event)
  (raw_received:B.bytes)
  : prop =
  B.length raw_received == 0 \/
  received_event_decode_projection model ev raw_received

let network_message_raw_delta_legal
  (model:connection_model)
  (msg:directed_message M.tls_message)
  (raw:B.bytes)
  : GTot prop =
  if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
  then cleartext_tls_message_raw msg.CL.message_value raw
  else
    raw_records_exactly
      raw
      T.ApplicationData
      (protected_record_count msg.CL.message_direction msg.CL.message_value)

let event_raw_delta_legal
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : GTot prop =
  match ev with
  | ConnLocalEvent _ ->
    Seq.equal raw_sent B.empty /\
    Seq.equal raw_received B.empty
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction with
     | CL.Sent ->
       network_message_raw_delta_legal model msg raw_sent /\
       Seq.equal raw_received B.empty
     | CL.Received ->
       Seq.equal raw_sent B.empty /\
       network_message_raw_delta_legal model msg raw_received)

let event_protected_single_raw_parse_success
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : GTot prop =
  match ev with
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then True
    else if protected_record_count msg.CL.message_direction msg.CL.message_value == 1
    then
      match msg.CL.message_direction with
      | CL.Sent ->
        exists fragment.
          W.parse_record raw_sent ==
            Some (T.ApplicationData, fragment, B.length raw_sent)
      | CL.Received ->
        exists fragment.
          W.parse_record raw_received ==
            Some (T.ApplicationData, fragment, B.length raw_received)
    else True
  | ConnLocalEvent _ -> True

let event_protected_raw_parse_prefix_success
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : GTot prop =
  match ev with
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then True
    else
      (match msg.CL.message_direction with
      | CL.Sent ->
        (exists fragment. exists (consumed:nat).
          W.parse_record raw_sent ==
            Some (T.ApplicationData, fragment, consumed) /\
          consumed > 0 /\
          consumed <= B.length raw_sent)
      | CL.Received ->
        (exists fragment. exists (consumed:nat).
          W.parse_record raw_received ==
            Some (T.ApplicationData, fragment, consumed) /\
          consumed > 0 /\
          consumed <= B.length raw_received))
  | ConnLocalEvent _ -> True

let event_protected_raw_decompose_prefix_success
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : GTot prop =
  match ev with
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then True
    else
      (match msg.CL.message_direction with
      | CL.Sent ->
        (exists fragment. exists (consumed:nat).
          W.parse_record raw_sent ==
            Some (T.ApplicationData, fragment, consumed) /\
          consumed > 0 /\
          consumed <= B.length raw_sent /\
          raw_records_exactly
            (Seq.slice raw_sent consumed (B.length raw_sent))
            T.ApplicationData
            (protected_record_count msg.CL.message_direction msg.CL.message_value - 1))
      | CL.Received ->
        (exists fragment. exists (consumed:nat).
          W.parse_record raw_received ==
            Some (T.ApplicationData, fragment, consumed) /\
          consumed > 0 /\
          consumed <= B.length raw_received /\
          raw_records_exactly
            (Seq.slice raw_received consumed (B.length raw_received))
            T.ApplicationData
            (protected_record_count msg.CL.message_direction msg.CL.message_value - 1)))
  | ConnLocalEvent _ -> True

let event_protected_raw_segmented_success
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : GTot prop =
  match ev with
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then True
    else
      (match msg.CL.message_direction with
      | CL.Sent ->
        raw_records_segmented
          raw_sent
          T.ApplicationData
          (protected_record_count msg.CL.message_direction msg.CL.message_value)
      | CL.Received ->
        raw_records_segmented
          raw_received
          T.ApplicationData
          (protected_record_count msg.CL.message_direction msg.CL.message_value))
  | ConnLocalEvent _ -> True

type connection_delta = {
  delta_event: conn_event;
  delta_raw_sent: B.bytes;
  delta_raw_received: B.bytes;
}

let legal_connection_delta
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : GTot prop =
  legal_event st0.cs_model delta.delta_event /\
  step_model st0.cs_model delta.delta_event == Some st1.cs_model /\
  event_raw_delta_legal
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received /\
  st1.cs_wire_log == {
    CL.raw_sent = B.append st0.cs_wire_log.CL.raw_sent delta.delta_raw_sent;
    CL.raw_received = B.append st0.cs_wire_log.CL.raw_received delta.delta_raw_received;
  } /\
  st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]

let rec conn_events_raw_replay
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Tot prop
        (decreases events)
  =
  match events with
  | [] ->
    Seq.equal raw_sent B.empty /\
    Seq.equal raw_received B.empty /\
    final_model == model
  | ev :: rest ->
    exists model1 delta_sent delta_received tail_sent tail_received.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_raw_replay model1 rest tail_sent tail_received final_model

let rec conn_events_protected_raw_segmented_replay
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Tot prop
        (decreases events)
  =
  match events with
  | [] ->
    Seq.equal raw_sent B.empty /\
    Seq.equal raw_received B.empty /\
    final_model == model
  | ev :: rest ->
    exists model1 delta_sent delta_received tail_sent tail_received.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      event_protected_raw_segmented_success ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_protected_raw_segmented_replay
        model1
        rest
        tail_sent
        tail_received
        final_model

let connection_state_raw_event_replay_consistent
  (st:connection_state)
  : prop =
  conn_events_raw_replay
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model

let connection_state_protected_raw_segmented_replay_consistent
  (st:connection_state)
  : prop =
  conn_events_protected_raw_segmented_replay
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model

let rec conn_events_sent_seal_replay
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Tot prop
        (decreases events)
  =
  match events with
  | [] ->
    Seq.equal raw_sent B.empty /\
    Seq.equal raw_received B.empty /\
    final_model == model
  | ev :: rest ->
    exists model1 delta_sent delta_received tail_sent tail_received.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_sent_seal_replay model1 rest tail_sent tail_received final_model

let rec conn_events_sent_seal_key_schedule_replay
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Tot prop
       (decreases events)
  =
  match events with
  | [] ->
    Seq.equal raw_sent B.empty /\
    Seq.equal raw_received B.empty /\
    final_model == model
  | ev :: rest ->
    exists model1 delta_sent delta_received tail_sent tail_received.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      record_write_key_schedule_projection model /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_sent_seal_key_schedule_replay
       model1
       rest
       tail_sent
       tail_received
       final_model

let rec conn_events_received_decode_replay
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Tot prop
        (decreases events)
  =
  match events with
  | [] ->
    Seq.equal raw_sent B.empty /\
    Seq.equal raw_received B.empty /\
    final_model == model
  | ev :: rest ->
    exists model1 delta_sent delta_received tail_sent tail_received.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_received_decode_replay model1 rest tail_sent tail_received final_model

let rec conn_events_received_decode_key_schedule_replay
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Tot prop
        (decreases events)
  =
  match events with
  | [] ->
    Seq.equal raw_sent B.empty /\
    Seq.equal raw_received B.empty /\
    final_model == model
  | ev :: rest ->
    exists model1 delta_sent delta_received tail_sent tail_received.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      record_read_key_schedule_projection model /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_received_decode_key_schedule_replay
        model1
        rest
        tail_sent
        tail_received
        final_model

let connection_state_sent_seal_replay_consistent
  (st:connection_state)
  : prop =
  conn_events_sent_seal_replay
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model

let connection_state_sent_seal_key_schedule_replay_consistent
  (st:connection_state)
  : prop =
  conn_events_sent_seal_key_schedule_replay
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model

let connection_state_received_decode_replay_consistent
  (st:connection_state)
  : prop =
  conn_events_received_decode_replay
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model

let connection_state_received_decode_key_schedule_replay_consistent
  (st:connection_state)
  : prop =
  conn_events_received_decode_key_schedule_replay
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model

let connection_state_raw_to_message_replay_consistent
  (st:connection_state)
  : prop =
  connection_state_raw_event_replay_consistent st /\
  connection_state_protected_raw_segmented_replay_consistent st /\
  connection_state_sent_seal_replay_consistent st /\
  connection_state_sent_seal_key_schedule_replay_consistent st /\
  connection_state_received_decode_replay_consistent st /\
  connection_state_received_decode_key_schedule_replay_consistent st

let connection_state_full_log_consistent
  (st:connection_state)
  : prop =
  connection_state_layered_log_consistent st /\
  connection_state_connection_log_view_consistent st /\
  connection_state_raw_event_replay_consistent st

let connection_state_single_step : RTC.binrel connection_state =
  fun st0 st1 -> exists delta. legal_connection_delta st0 delta st1

let connection_state_evolves : RTC.preorder connection_state =
  RTC.closure connection_state_single_step

let connection_state_consistent (st:connection_state) : GTot prop =
  connection_state_evolves (initial st.cs_model.model_config) st
