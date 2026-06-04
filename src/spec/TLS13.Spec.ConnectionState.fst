module TLS13.Spec.ConnectionState

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module H = TLS13.Handshake.Spec
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

let update_key_schedule_with_install
  (keys:key_schedule_state)
  (install:traffic_key_install)
  : key_schedule_state =
  let material = install.install_material in
  match install.install_epoch, install.install_direction with
  | TrafficHandshake, TrafficWrite ->
    { keys with ks_client_handshake_traffic = Some material }
  | TrafficHandshake, TrafficRead ->
    { keys with ks_server_handshake_traffic = Some material }
  | TrafficApplication, TrafficWrite ->
    { keys with ks_client_application_traffic = Some material }
  | TrafficApplication, TrafficRead ->
    { keys with ks_server_application_traffic = Some material }

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

let expected_traffic_secret
  (hs:handshake_state)
  (epoch:traffic_epoch)
  (dir:traffic_direction)
  : GTot (option K.traffic_secret) =
  match epoch, dir with
  | TrafficHandshake, TrafficWrite ->
    (match hs.hs_keys.ks_handshake_secret with
     | Some secret -> Some (K.client_handshake_traffic_secret secret (Tr.hash hs.hs_transcript))
     | None -> None)
  | TrafficHandshake, TrafficRead ->
    (match hs.hs_keys.ks_handshake_secret with
     | Some secret -> Some (K.server_handshake_traffic_secret secret (Tr.hash hs.hs_transcript))
     | None -> None)
  | TrafficApplication, TrafficWrite ->
    (match hs.hs_keys.ks_master_secret with
     | Some secret -> Some (K.client_application_traffic_secret secret (Tr.hash hs.hs_transcript))
     | None -> None)
  | TrafficApplication, TrafficRead ->
    (match hs.hs_keys.ks_master_secret with
     | Some secret -> Some (K.server_application_traffic_secret secret (Tr.hash hs.hs_transcript))
     | None -> None)

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

let lemma_raw_records_exactly_one_parse_record
  (raw:B.bytes)
  (outer:T.content_type)
  : Lemma
      (requires raw_records_exactly raw outer 1)
      (ensures exists fragment.
        W.parse_record raw == Some (outer, fragment, B.length raw))
=
  let parsed = CL.parse_record_prefix raw in
  assert (CL.record_stream_serializes raw parsed);
  assert (Seq.equal parsed.CL.residual B.empty);
  assert (length parsed.CL.values == 1);
  assert (all_records_outer_type outer parsed.CL.values);
  assert (parsed.CL.consumed <= B.length raw);
  assert (Seq.equal parsed.CL.residual
                    (Seq.slice raw parsed.CL.consumed (B.length raw)));
  Seq.lemma_eq_elim parsed.CL.residual B.empty;
  Seq.lemma_eq_elim
    parsed.CL.residual
    (Seq.slice raw parsed.CL.consumed (B.length raw));
  Seq.lemma_len_slice raw parsed.CL.consumed (B.length raw);
  assert (B.length (Seq.slice raw parsed.CL.consumed (B.length raw)) == 0);
  assert (parsed.CL.consumed == B.length raw);
  match W.parse_record raw with
  | None ->
    assert (B.length raw + 1 > 0);
    assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
    assert (parsed.CL.values == []);
    assert False
  | Some (content_type, fragment, consumed) ->
    W.lemma_parse_record_serializes raw;
    if consumed == 0 || consumed > B.length raw then (
      assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
      assert (parsed.CL.values == []);
      assert False
    ) else (
      let rest = Seq.slice raw consumed (B.length raw) in
      let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
      let record =
        { M.record_outer_type = content_type;
          M.record_fragment = fragment } in
      assert (CL.parse_record_prefix raw ==
        {
          CL.values = record :: tail.CL.values;
          CL.consumed = consumed + tail.CL.consumed;
          CL.residual = tail.CL.residual;
        });
      assert (parsed.CL.values == record :: tail.CL.values);
      assert (length tail.CL.values == 0);
      assert (all_records_outer_type outer (record :: tail.CL.values));
      assert (content_type == outer);
      CL.lemma_parse_record_prefix_fuel_serializes (B.length raw) rest;
      assert (CL.record_stream_serializes rest tail);
      assert (tail.CL.consumed == B.length (CL.serialize_tls_records tail.CL.values));
      match tail.CL.values with
      | [] ->
        assert (CL.serialize_tls_records tail.CL.values == B.empty);
        assert (tail.CL.consumed == 0);
        assert (parsed.CL.consumed == consumed + tail.CL.consumed);
        assert (consumed == parsed.CL.consumed);
        assert (consumed == B.length raw);
        assert (W.parse_record raw == Some (outer, fragment, B.length raw));
        assert (exists fragment'. W.parse_record raw == Some (outer, fragment', B.length raw))
      | _ :: _ ->
        assert False
    )

let lemma_raw_records_exactly_nonempty_parse_record
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : Lemma
      (requires raw_records_exactly raw outer count /\ count > 0)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (outer, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw)
=
  let parsed = CL.parse_record_prefix raw in
  assert (length parsed.CL.values == count);
  assert (all_records_outer_type outer parsed.CL.values);
  match W.parse_record raw with
  | None ->
    assert (B.length raw + 1 > 0);
    assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
    assert (parsed.CL.values == []);
    assert False
  | Some (content_type, fragment, consumed) ->
    W.lemma_parse_record_serializes raw;
    if consumed == 0 || consumed > B.length raw then (
      assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
      assert (parsed.CL.values == []);
      assert False
    ) else (
      let rest = Seq.slice raw consumed (B.length raw) in
      let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
      let record =
        { M.record_outer_type = content_type;
          M.record_fragment = fragment } in
      assert (CL.parse_record_prefix raw ==
        {
          CL.values = record :: tail.CL.values;
          CL.consumed = consumed + tail.CL.consumed;
          CL.residual = tail.CL.residual;
        });
      assert (parsed.CL.values == record :: tail.CL.values);
      assert (all_records_outer_type outer (record :: tail.CL.values));
      assert (content_type == outer);
      assert (W.parse_record raw == Some (outer, fragment, consumed));
      assert (exists fragment'. exists (consumed':nat).
        W.parse_record raw == Some (outer, fragment', consumed') /\
        consumed' > 0 /\
        consumed' <= B.length raw)
    )

let lemma_raw_records_exactly_single_serialized
  (outer:T.content_type)
  (fragment:B.bytes{B.length fragment <= 16640})
  : Lemma
      (raw_records_exactly (W.serialize_record outer fragment) outer 1)
=
  let raw = W.serialize_record outer fragment in
  W.lemma_parse_record_serialize_record outer fragment;
  CL.lemma_parse_record_prefix_serializes raw;
  assert (B.length raw > 0);
  assert (W.parse_record raw == Some (outer, fragment, B.length raw));
  let rest = Seq.slice raw (B.length raw) (B.length raw) in
  Seq.lemma_len_slice raw (B.length raw) (B.length raw);
  assert (B.length rest == 0);
  Seq.lemma_eq_intro rest B.empty;
  assert (rest == B.empty);
  assert (CL.parse_record_prefix_fuel (B.length raw) rest ==
    CL.raw_record_stream_view rest);
  assert (CL.raw_record_stream_view rest ==
    { CL.values = []; CL.consumed = 0; CL.residual = rest });
  assert (CL.record_stream_serializes raw (CL.parse_record_prefix raw));
  assert (CL.parse_record_prefix raw ==
    {
      CL.values = [{ M.record_outer_type = outer; M.record_fragment = fragment }];
      CL.consumed = B.length raw;
      CL.residual = B.empty;
    });
  assert (length (CL.parse_record_prefix raw).CL.values == 1);
  assert (all_records_outer_type outer (CL.parse_record_prefix raw).CL.values)

let lemma_raw_application_data_record_exactly
  (fragment:B.bytes{B.length fragment <= 16640})
  : Lemma
      (raw_records_exactly (W.serialize_record T.ApplicationData fragment) T.ApplicationData 1)
=
  lemma_raw_records_exactly_single_serialized T.ApplicationData fragment

let serialized_cleartext_tls_message (msg:M.tls_message) : GTot B.bytes =
  let (content_type, fragment) = W.serialize_tls_message msg in
  W.serialize_record content_type fragment

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

let lemma_protected_record_count_positive
  (dir:direction)
  (msg:M.tls_message)
  : Lemma (protected_record_count dir msg > 0)
=
  match dir, msg with
  | CL.Sent, M.TlsApplicationData bytes ->
    S.lemma_application_data_record_count_len_positive (B.length bytes)
  | _, _ -> ()

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

let lemma_network_message_raw_delta_legal_protected_single_parse_record
  (model:connection_model)
  (msg:directed_message M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        network_message_raw_delta_legal model msg raw /\
        network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false /\
        protected_record_count msg.CL.message_direction msg.CL.message_value == 1)
      (ensures exists fragment.
        W.parse_record raw == Some (T.ApplicationData, fragment, B.length raw))
=
  assert (raw_records_exactly raw T.ApplicationData 1);
  lemma_raw_records_exactly_one_parse_record raw T.ApplicationData

let lemma_network_message_raw_delta_legal_protected_parse_prefix
  (model:connection_model)
  (msg:directed_message M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        network_message_raw_delta_legal model msg raw /\
        network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (T.ApplicationData, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw)
=
  lemma_protected_record_count_positive msg.CL.message_direction msg.CL.message_value;
  lemma_raw_records_exactly_nonempty_parse_record
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

let lemma_event_raw_delta_legal_protected_single_parse_record
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires event_raw_delta_legal model ev raw_sent raw_received)
      (ensures event_protected_single_raw_parse_success ev raw_sent raw_received)
=
  match ev with
  | ConnLocalEvent _ -> ()
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then ()
    else if protected_record_count msg.CL.message_direction msg.CL.message_value == 1
    then
      match msg.CL.message_direction with
      | CL.Sent ->
        lemma_network_message_raw_delta_legal_protected_single_parse_record model msg raw_sent
      | CL.Received ->
        lemma_network_message_raw_delta_legal_protected_single_parse_record model msg raw_received
    else ()

let lemma_event_raw_delta_legal_protected_parse_prefix
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires event_raw_delta_legal model ev raw_sent raw_received)
      (ensures event_protected_raw_parse_prefix_success ev raw_sent raw_received)
=
  match ev with
  | ConnLocalEvent _ -> ()
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then ()
    else
      match msg.CL.message_direction with
      | CL.Sent ->
        lemma_network_message_raw_delta_legal_protected_parse_prefix model msg raw_sent
      | CL.Received ->
        lemma_network_message_raw_delta_legal_protected_parse_prefix model msg raw_received

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

let lemma_legal_connection_delta_protected_single_parse_record
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures event_protected_single_raw_parse_success
        delta.delta_event
        delta.delta_raw_sent
        delta.delta_raw_received)
=
  lemma_event_raw_delta_legal_protected_single_parse_record
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received

let lemma_legal_connection_delta_protected_parse_prefix
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures event_protected_raw_parse_prefix_success
        delta.delta_event
        delta.delta_raw_sent
        delta.delta_raw_received)
=
  lemma_event_raw_delta_legal_protected_parse_prefix
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received

let connection_state_single_step : RTC.binrel connection_state =
  fun st0 st1 -> exists delta. legal_connection_delta st0 delta st1

let connection_state_evolves : RTC.preorder connection_state =
  RTC.closure connection_state_single_step

let connection_state_consistent (st:connection_state) : GTot prop =
  connection_state_evolves (initial st.cs_model.model_config) st
