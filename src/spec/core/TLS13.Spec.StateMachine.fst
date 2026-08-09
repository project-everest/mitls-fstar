module TLS13.Spec.StateMachine

(**
  Core TLS 1.3 connection state machine: essential state/config/event
  vocabulary, the initial state, the legal-event and step transition functions,
  and the minimal raw-wire relation at the semantic boundary. This is the
  audit-facing executable model. Auxiliary predicates, projections, invariants,
  and reachability live in property modules under TLS13.Spec.StateMachine.*.
  This module depends only on core and assumption modules.
**)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module H = TLS13.Handshake.Spec
module K = TLS13.Keys
module M = TLS13.Messages
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished
module R = TLS13.Record.Spec
module RF = TLS13.Spec.StateMachine.RecordFraming
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
  | HsAwaitingClientHello
  | HsClientHelloReceived
  | HsServerHelloSent
  | HsServerEncryptedFlightSent
  | HsServerFinishedSent
  | HsClientFinishedReceived
  | HsClientFinishedVerified
type connection_control_state =
  | ControlNew
  | ControlHandshaking of handshake_stage
  | ControlApplicationData
  | ControlClosing
  | ControlClosed
  | ControlFailed of T.tls_error
type traffic_epoch =
  | TrafficHandshake
  | TrafficApplication
type traffic_label =
  | ClientTraffic
  | ServerTraffic
type traffic_direction =
  | TrafficWrite
  | TrafficRead
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
type server_handshake_selection = {
  server_selected_client_hello: GCH.clientHello;
  server_selected_cipher_suite: T.cipher_suite;
  server_selected_group: T.named_group;
  server_selected_signature_scheme: T.signature_scheme;
  server_random: B.bytes_of_len 32;
  server_key_share_private: option C.x25519_private;
  server_key_share_public: C.x25519_public;
  server_selected_credential: server_credential_identity;
}
let server_selection_key_share_consistent
  (selection:server_handshake_selection)
  : prop =
  match selection.server_key_share_private with
  | Some sk -> C.x25519_public_from_private sk == selection.server_key_share_public
  | None -> True
type handshake_state = {
  hs_start: option handshake_start;
  hs_server_selection: option server_handshake_selection;
  hs_client_hello: option GCH.clientHello;
  hs_server_hello: option GSH.serverHello;
  hs_encrypted_extensions: option GEE.encryptedExtensions;
  hs_certificate: option GCert.certificate;
  hs_validated_peer: option X.peer_identity;
  hs_certificate_verify: option GCV.certificateVerify;
  hs_certificate_verify_verified: bool;
  hs_server_finished: option GFin.finished;
  hs_server_finished_verified: bool;
  hs_client_finished: option GFin.finished;
  hs_transcript: Tr.transcript;
  hs_buffers: handshake_buffer_state;
  hs_keys: key_schedule_state;
}
let empty_handshake_state : handshake_state = {
  hs_start = None;
  hs_server_selection = None;
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
let client_hello_key_share (ch:GCH.clientHello) : option C.x25519_public =
  match Sem.clientHello_key_share_x25519 ch with
  | Some k -> if B.length k = 32 then Some (k <: C.x25519_public) else None
  | None -> None
let server_hello_key_share (sh:GSH.serverHello) : option C.x25519_public =
  match Sem.serverHello_key_share_x25519 sh with
  | Some k -> if B.length k = 32 then Some (k <: C.x25519_public) else None
  | None -> None
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
type role_traffic_key_install = {
  install_role: endpoint_role;
  install_payload: traffic_key_install;
}
type local_event =
  | LocalStartHandshake of handshake_start
  | LocalStartServer
  | LocalSelectServerParameters of server_handshake_selection
  | LocalDeriveSharedSecret of C.x25519_shared_secret
  | LocalInstallTrafficKeys of traffic_key_install
  | LocalInstallTrafficKeysForRole of role_traffic_key_install
  | LocalValidateCertificate of X.peer_identity
  | LocalVerifyCertificateSignature of GCV.certificateVerify
  | LocalSignCertificateVerify of GCV.certificateVerify
  | LocalVerifyFinished of GFin.finished
  | LocalVerifyClientFinished of GFin.finished
  | LocalDeliverApplicationData of B.bytes
  | LocalFail of T.tls_error
noextract
type protected_handshake_step = {
  protected_handshake_message: M.handshake_msg;
  protected_handshake_fragment: B.bytes;
  protected_handshake_offset: nat;
  protected_handshake_consumed: nat;
  protected_handshake_head: bool;
  (* A BUFFERING step takes delivery of a record whose plaintext does not
     complete a handshake message: it appends the plaintext to the pending
     buffer, advances the read sequence, and steps nothing else.  It is what
     makes a message spanning three or more records deliverable -- with only
     ordinary head steps, reassembly would stall as soon as one record plus
     the leftover still did not contain a whole message.

     [protected_handshake_message], [protected_handshake_offset] and
     [protected_handshake_consumed] are inert for such a step. *)
  protected_handshake_buffering: bool;
}
type conn_event =
  | ConnNetworkEvent of directed_message M.tls_message
  | ConnProtectedHandshake of protected_handshake_step
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
(** A configuration carries a server credential.  This is a PROTOCOL-level
    well-formedness fact, not an implementation bound: the step relation already
    demands it at `LocalStartServer` / `ControlNew`, and every server-side
    transition that reads a credential matches on `config_server`.  Naming it
    here lets the implementation and the system-level proofs share one
    definition instead of respelling `Some? ...config_server` inline.

    NOTE the deliberate layering.  This predicate says only that the credential
    is PRESENT; it says nothing about how large the chain may be.  Any bound on
    the chain length is a property of a particular implementation's buffers, NOT
    of the protocol, so it does not belong here -- see
    `TLS13.Impl.ConnectionState.Repr.server_config_valid`, which conjoins this
    predicate with the implementation's own bound. **)
let config_server_present (cfg:connection_config) : prop =
  Some? cfg.config_server

let server_config_present (st:connection_state) : prop =
  config_server_present st.cs_model.model_config

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
let install_record_keys_for_role
  (role:endpoint_role)
  (record:record_layer_state)
  (install:traffic_key_install)
  : record_layer_state =
  match role, install.install_epoch, install.install_direction with
  | ServerEndpoint, TrafficApplication, TrafficWrite ->
    let material = install.install_material in
    {
    record with
      record_write =
        R.install_keys record.record_write R.Application material.traffic_key material.traffic_iv;
    }
  | _, _, _ ->
    install_record_keys record install
let traffic_material_matches_record_direction
  (material:traffic_key_material)
  (st:R.direction_state)
  : prop =
  st.R.key == Some material.traffic_key /\
  st.R.static_iv == Some material.traffic_iv
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
let application_record_keys_installed_for_role
  (role:endpoint_role)
  (model:connection_model)
  : prop =
  let keys = model.model_handshake.hs_keys in
  match
    traffic_material_for_label
      keys
      TrafficApplication
      (traffic_label_for_endpoint_direction role TrafficRead),
    traffic_material_for_label
      keys
      TrafficApplication
      (traffic_label_for_endpoint_direction role TrafficWrite)
  with
  | Some read_material, Some write_material ->
    traffic_material_matches_record_direction
      read_material
      model.model_record.record_read /\
    traffic_material_matches_record_direction
      write_material
      model.model_record.record_write
  | _, _ ->
    False
let derive_shared_secret_model
  (model:connection_model)
  (hs:handshake_state)
  (shared:C.x25519_shared_secret)
  : connection_model =
  let early = K.early_secret B.empty in
  let handshake = K.handshake_secret early shared in
  let master = K.master_secret handshake in
  let keys = { hs.hs_keys with ks_shared_secret = Some shared } in
  with_handshake_state
    model
    { hs with
        hs_keys =
          { keys with
              ks_early_secret = Some early;
              ks_handshake_secret = Some handshake;
              ks_master_secret = Some master;
          };
    }
let step_local_event (model:connection_model) (ev:local_event) : GTot (option connection_model) =
  let hs = model.model_handshake in
  match ev, model.model_control with
  | LocalStartHandshake start, ControlNew ->
    Some (with_handshake_stage model { hs with hs_start = Some start } HsStarted)
  | LocalStartServer, ControlNew ->
    Some (with_handshake_stage model hs HsAwaitingClientHello)
  | LocalSelectServerParameters selection, ControlHandshaking HsClientHelloReceived ->
    Some (with_handshake_stage
      model
      { hs with
          hs_server_selection = Some selection;
          hs_client_hello = Some selection.server_selected_client_hello;
      }
      HsClientHelloReceived)
  | LocalDeriveSharedSecret shared, ControlHandshaking HsServerHelloReceived ->
    Some (derive_shared_secret_model model hs shared)
  | LocalDeriveSharedSecret shared, ControlHandshaking HsClientHelloReceived ->
    Some (derive_shared_secret_model model hs shared)
  | LocalInstallTrafficKeys install, ControlHandshaking _ ->
    let keys = update_key_schedule_with_install hs.hs_keys install in
    Some {
      model with
        model_record = install_record_keys model.model_record install;
        model_handshake = { hs with hs_keys = keys };
    }
  | LocalInstallTrafficKeysForRole role_install, ControlHandshaking _ ->
    let install = role_install.install_payload in
    let keys =
      update_key_schedule_with_install_for_role
        role_install.install_role
        hs.hs_keys
        install in
    Some {
      model with
        model_record =
          install_record_keys_for_role
            role_install.install_role
            model.model_record
            install;
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
  | LocalSignCertificateVerify cv, ControlHandshaking HsServerEncryptedFlightSent ->
    Some (with_handshake_stage
      model
      { hs with
          hs_certificate_verify = Some cv;
          hs_buffers =
            { hs.hs_buffers with
                hb_certificate_verify_input =
                  Some (H.certificate_verify_input (Tr.hash hs.hs_transcript));
            };
      }
      HsServerEncryptedFlightSent)
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
  | LocalVerifyClientFinished fin, ControlHandshaking HsClientFinishedReceived ->
    Some {
      model with
        model_control = ControlApplicationData;
        model_handshake =
          append_handshake_to_transcript
            { hs with hs_client_finished = Some fin }
            (M.Finished fin);
    }
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
  | CL.Received, M.ClientHello ch, ControlHandshaking HsAwaitingClientHello ->
    let hs' =
      append_handshake_to_transcript
        { hs with
            hs_client_hello = Some ch;
            hs_buffers =
              { hs.hs_buffers with hb_client_hello_bytes = W.serialize_handshake msg };
        }
        msg in
    Some (with_handshake_stage model hs' HsClientHelloReceived)
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
  | CL.Sent, M.ServerHello sh, ControlHandshaking HsClientHelloReceived ->
    let hs' =
      append_handshake_to_transcript
        { hs with
            hs_server_hello = Some sh;
            hs_buffers =
              { hs.hs_buffers with hb_server_hello_bytes = W.serialize_handshake msg };
        }
        msg in
    Some (with_handshake_stage model hs' HsServerHelloSent)
  | CL.Sent, M.EncryptedExtensions ee, ControlHandshaking HsServerHelloSent ->
    Some (with_handshake_stage
      { model with
          model_record =
            { model.model_record with
                record_write = R.next_seq model.model_record.record_write;
            };
      }
      (append_handshake_to_transcript
        { hs with hs_encrypted_extensions = Some ee }
        msg)
      HsServerEncryptedFlightSent)
  | CL.Sent, M.Certificate cert, ControlHandshaking HsServerEncryptedFlightSent ->
    Some (with_handshake_stage
      { model with
          model_record =
            { model.model_record with
                record_write = R.next_seq model.model_record.record_write;
            };
      }
      (append_handshake_to_transcript
        { hs with
            hs_certificate = Some cert;
            hs_buffers =
            { hs.hs_buffers with
                hb_certificate_leaf_der =
                  (match (Sem.certificate_entries cert) with
                   | leaf :: _ -> Some leaf
                   | [] -> None);
            };
        }
        msg)
      HsServerEncryptedFlightSent)
  | CL.Sent, M.CertificateVerify cv, ControlHandshaking HsServerEncryptedFlightSent ->
    Some (with_handshake_stage
      { model with
          model_record =
            { model.model_record with
                record_write = R.next_seq model.model_record.record_write;
            };
      }
      (append_handshake_to_transcript
        { hs with
            hs_certificate_verify = Some cv;
            hs_certificate_verify_verified = true;
        }
        msg)
      HsServerEncryptedFlightSent)
  | CL.Sent, M.Finished fin, ControlHandshaking HsServerEncryptedFlightSent ->
    Some (with_handshake_stage
      { model with
          model_record =
            { model.model_record with
                record_write = R.next_seq model.model_record.record_write;
            };
      }
      (append_handshake_to_transcript
        { hs with hs_server_finished = Some fin }
        msg)
      HsServerFinishedSent)
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
                  (match (Sem.certificate_entries cert) with
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
    // Fix 1 (atomic): the client processes the server Finished in a single step -
    // append it to the transcript, mark it verified, and install the server's
    // application read keys (record read epoch -> Application) so that no window
    // exists in which the server can send an application-keys record the client
    // cannot decrypt. The application traffic secret is derived from the transcript
    // THROUGH the server Finished, so the append happens before the derivation.
    let hs_v =
      append_handshake_to_transcript
        { hs with
            hs_server_finished = Some fin;
            hs_server_finished_verified = true;
        }
        (M.Finished fin) in
    (match hs_v.hs_keys.ks_master_secret with
     | Some master ->
       let secret = K.server_application_traffic_secret master (Tr.hash hs_v.hs_transcript) in
       let material = traffic_key_material_for_secret secret in
       Some (with_handshake_stage
         { model with
             model_record =
               { model.model_record with
                   record_read =
                     R.install_keys
                       model.model_record.record_read
                       R.Application
                       material.traffic_key
                       material.traffic_iv;
               };
         }
         { hs_v with
             hs_keys =
               { hs_v.hs_keys with ks_server_application_traffic = Some material };
         }
         HsServerFinishedVerified)
     | None -> None)
  | CL.Received, M.Finished fin, ControlHandshaking HsServerFinishedSent ->
    // Fix 1 (atomic, mirror): the server processes the client Finished in a single
    // step - install the client's application read keys (record read epoch ->
    // Application) and advance to ControlApplicationData, closing the mirror window
    // in which the client could send an application-keys record the server cannot
    // decrypt. The application traffic secret is derived from the transcript THROUGH
    // the server Finished (already present), so it is computed BEFORE appending the
    // client Finished to the transcript.
    (match hs.hs_keys.ks_master_secret with
     | Some master ->
       let secret = K.client_application_traffic_secret master (Tr.hash hs.hs_transcript) in
       let material = traffic_key_material_for_secret secret in
       let hs_v =
         append_handshake_to_transcript
           { hs with hs_client_finished = Some fin }
           (M.Finished fin) in
       Some {
         model with
           model_control = ControlApplicationData;
           model_record =
             { model.model_record with
                 record_read =
                   R.install_keys
                     model.model_record.record_read
                     R.Application
                     material.traffic_key
                     material.traffic_iv;
             };
           model_handshake =
             { hs_v with
                 hs_keys =
                   { hs_v.hs_keys with ks_client_application_traffic = Some material };
             };
       }
     | None -> None)
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
(** RFC 8446 §4.6.3.  A KeyUpdate rotates exactly one direction's application
    traffic secret.  Which key-schedule slot that is depends on the endpoint's
    role: [TrafficWrite] names our own sending secret, [TrafficRead] the peer's.
    Sending a KeyUpdate rotates our write key; receiving one rotates our read
    key.  Going through [traffic_label_for_endpoint_direction] rather than
    naming [ks_client_application_traffic] / [ks_server_application_traffic]
    directly is what makes this arm correct for a server as well as a client.

    The [next_seq] is immaterial to the result — [R.install_keys] resets the
    sequence number to zero, as §5.3 requires on a key change — but it is kept
    so the shape matches the other record-advancing arms.

    Marked [unfold] on purpose: downstream invariants routinely need to see
    that rotation touches only [model_record] and [model_handshake.hs_keys]
    (control state, config, transcript and application state are all
    preserved).  Behind an ordinary [let] that fact costs an extra unfolding
    in every such proof, which is enough to push several of the larger
    reachability lemmas over their rlimit. *)
unfold
let rotate_application_traffic
  (model:connection_model)
  (tdir:traffic_direction)
  : option connection_model =
  let hs = model.model_handshake in
  let label =
    traffic_label_for_endpoint_direction model.model_config.config_role tdir in
  match traffic_material_for_label hs.hs_keys TrafficApplication label with
  | None -> None
  | Some old ->
    let updated = updated_traffic_key_material old in
    let record =
      match tdir with
      | TrafficRead ->
        { model.model_record with
            record_read =
              R.install_keys
                (R.next_seq model.model_record.record_read)
                R.Application
                updated.traffic_key
                updated.traffic_iv }
      | TrafficWrite ->
        { model.model_record with
            record_write =
              R.install_keys
                (R.next_seq model.model_record.record_write)
                R.Application
                updated.traffic_key
                updated.traffic_iv } in
    Some {
      model with
        model_record = record;
        model_handshake = {
          hs with
            hs_keys =
              update_key_schedule_with_label
                hs.hs_keys TrafficApplication label updated;
        };
    }

(** Sending a KeyUpdate discharges a pending response obligation exactly when it
    is the response form.  §4.6.3 requires the reply to a [update_requested] to
    carry [update_not_requested]; a spontaneous [update_requested] therefore
    leaves any outstanding obligation in place rather than silently clearing
    it. *)
let sent_key_update_response
  (app:application_state)
  (req:M.key_update_request)
  : application_state =
  match req with
  | M.UpdateNotRequested ->
    { app with app_key_update_response_pending = false }
  | M.UpdateRequested ->
    app

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
                   (RF.application_data_record_count bytes);
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
   (match dir with
    | CL.Received ->
      (* The peer rotated its sending key, so rotate our read key.  Only an
         [update_requested] obliges us to answer (§4.6.3); answering an
         [update_not_requested] would make the two endpoints ping-pong. *)
      (match rotate_application_traffic model TrafficRead with
       | Some model' ->
         Some {
           model' with
             model_application =
               received_key_update_pending model.model_application req;
         }
       | None -> None)
    | CL.Sent ->
      (* Rotate our own sending key.  This arm is deliberately not conditioned
         on an outstanding response obligation: an endpoint may initiate a
         KeyUpdate spontaneously, which is what keeps a long-lived connection
         inside the AEAD usage limits of §5.5. *)
      (match rotate_application_traffic model TrafficWrite with
       | Some model' ->
         Some {
           model' with
             model_application =
               sent_key_update_response model.model_application req;
         }
       | None -> None))
  | M.TlsAlert T.Close_notify, ControlApplicationData ->
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
  | M.TlsAlert T.Close_notify, ControlClosing ->
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
  | M.TlsAlert alert, ControlFailed _ ->
    // A failed connection is dead: it sends nothing further (a `Sent` alert from
    // `ControlFailed` is illegal / not a real transition).  Receiving an alert on
    // an already-failed connection is passive and stays failed (idempotent).
    (match dir with
     | CL.Sent -> None
     | CL.Received -> Some (fail_model model (T.AlertError alert)))
  | M.TlsAlert alert, _ ->
    // Stream-integrity fix (RECORD level).  This catch-all used to be
    // DIRECTION-BLIND: `Some (fail_model ...)` for BOTH directions, at EVERY
    // remaining control.  That made a `CL.Sent` alert a legal transition at, e.g.,
    // `ControlNew` / `HsClientHelloSent`, where `record_write.R.epoch == R.Initial`
    // and `record_write.R.key == None`.  Since `network_message_is_cleartext`
    // (below) classifies EVERY alert as NON-cleartext, the protected branch of
    // `network_message_raw_delta_legal` then permitted a "garbage protected"
    // `Application_data` record sealed under no key at all.  Consequences:
    //   * protected-record COUNTS stopped witnessing "the peer sent its Finished"
    //     (an alert inflates the count identically), which killed every counting
    //     route to the cross-endpoint handshake facts; and
    //   * `~cleartext sent` no longer implied `~(R.Initial? (snap_wr p).R.epoch)`,
    //     so the ToServer handshake-seal bridge could not be fired for a payload
    //     whose message identity was not already known.
    // The fix COMPLETES the pattern the `ControlFailed` arm immediately above
    // already uses (:961-967): make the catch-all direction-explicit and REFUSE
    // the send.  It is faithful — an endpoint's own failure is modelled by the
    // `LocalFail` local event, which emits nothing on the wire; the only alert any
    // endpoint ever SENDS is `Close_notify`, whose `CL.Sent` arm is live exactly at
    // `ControlApplicationData` (:929) and is `None` at `ControlClosing` (:949).
    // Because a consistent endpoint at `ControlApplicationData` has both
    // application record epochs installed
    // (`lemma_connection_appdata_keys_installed_for_role` then
    // `lemma_connection_application_ready_record_epochs_installed`), "non-cleartext
    // SEND ==> write key present ==> ~Initial write epoch" is now DERIVABLE rather
    // than assumed.  Removing a transition only SHRINKS the reachable set, so no
    // invariant preservation can be made harder by this change.
    (match dir with
     | CL.Sent -> None
     | CL.Received -> Some (fail_model model (T.AlertError alert)))
  | M.TlsChangeCipherSpec, ControlHandshaking _ ->
    Some model
  | _, _ ->
    None
let protected_handshake_message_supported (msg:M.handshake_msg) : bool =
  match msg with
  | M.EncryptedExtensions _
  | M.Certificate _
  | M.CertificateVerify _
  | M.Finished _ -> true
  | _ -> false

(* ==================================================================== *)
(* Cross-record handshake reassembly.                                   *)
(*                                                                      *)
(* TLS 1.3 permits a single handshake message to span several records,  *)
(* so a record's plaintext may end part-way through a message.  The     *)
(* unconsumed tail is held in the pending buffer and the NEXT record's  *)
(* plaintext is appended to it before parsing resumes.                  *)
(*                                                                      *)
(* The step record deliberately keeps [protected_handshake_fragment]    *)
(* equal to the RECORD PLAINTEXT for a head step.  That identity is     *)
(* what [TLS13.Spec.StateMachine.Canonical]'s decode projection relates *)
(* to the wire, and it is relied on by the receiver-side pairing        *)
(* proofs.  The concatenation with the leftover is derived here rather  *)
(* than stored in the step, so the wire relation is untouched.          *)
(* ==================================================================== *)

(* The unparsed suffix of the pending protected-handshake plaintext.

   [set_pending_protected_handshake] keeps [parsed < length bytes] whenever the
   buffer is non-empty and otherwise clears it to ([B.empty], 0), so this slice
   is empty exactly when [protected_handshake_buffer_empty] holds. *)
let pending_protected_handshake_leftover (model:connection_model) : B.bytes =
  let hb = model.model_handshake.hs_buffers in
  let bytes = hb.hb_encrypted_server_handshake_bytes in
  let parsed = hb.hb_encrypted_server_handshake_parsed in
  if parsed <= B.length bytes
  then Seq.slice bytes parsed (B.length bytes)
  else B.empty

(* The byte stream a step parses out of.

   A HEAD step resumes at the front of the leftover and continues into the
   record it takes delivery of, so its stream is [leftover ++ fragment].  A
   TAIL step continues inside the buffer already published by its head, whose
   fragment IS that buffer, so its stream is the fragment itself.

   When the pending buffer is empty the leftover is empty and a head step's
   stream is exactly its fragment, which is the pre-reassembly behaviour. *)
let protected_handshake_stream
  (model:connection_model)
  (step:protected_handshake_step)
  : B.bytes =
  if step.protected_handshake_head
  then
    B.append
      (pending_protected_handshake_leftover model)
      step.protected_handshake_fragment
  else step.protected_handshake_fragment

let set_pending_protected_handshake
  (model:connection_model)
  (fragment:B.bytes)
  (parsed:nat)
  : connection_model =
  let hs = model.model_handshake in
  let buffers =
    if parsed < B.length fragment
    then
      { hs.hs_buffers with
          hb_encrypted_server_handshake_bytes = fragment;
          hb_encrypted_server_handshake_parsed = parsed;
      }
    else
      { hs.hs_buffers with
          hb_encrypted_server_handshake_bytes = B.empty;
          hb_encrypted_server_handshake_parsed = 0;
      } in
  { model with model_handshake = { hs with hs_buffers = buffers } }
(* A buffering step consumes one record and nothing else: the read sequence
   advances (exactly as it does for a head step that carries a message, since
   in both cases one protected record has been opened), the record's plaintext
   is appended to whatever the previous record left unparsed, and the parse
   position resets to the front of the accumulated stream.

   Resetting [parsed] to 0 also COMPACTS the buffer: the bytes of messages
   already delivered are dropped, so the pending buffer only ever holds the
   prefix of the one message still being assembled. *)
let step_protected_handshake_buffer
  (model:connection_model)
  (step:protected_handshake_step)
  : GTot connection_model =
  let advanced =
    { model with
        model_record =
          { model.model_record with
              record_read = R.next_seq model.model_record.record_read;
          };
    } in
  set_pending_protected_handshake
    advanced
    (protected_handshake_stream model step)
    0

let step_protected_handshake
  (model:connection_model)
  (step:protected_handshake_step)
  : GTot (option connection_model) =
  if step.protected_handshake_buffering
  then
    (if step.protected_handshake_head
     then Some (step_protected_handshake_buffer model step)
     else None)
  else if protected_handshake_message_supported step.protected_handshake_message
  then
    match
      step_handshake_message
        model
        CL.Received
        step.protected_handshake_message
    with
    | None -> None
    | Some stepped ->
      let consumed_to =
        step.protected_handshake_offset + step.protected_handshake_consumed in
      let record_adjusted =
        if step.protected_handshake_head
        then stepped
        else
          match step.protected_handshake_message with
          | M.Finished _ -> stepped
          | _ ->
            { stepped with
                model_record =
                  { stepped.model_record with
                      record_read = model.model_record.record_read;
                  };
            } in
      Some
        (set_pending_protected_handshake
          record_adjusted
          step.protected_handshake_fragment
          consumed_to)
  else None
let step_model (model:connection_model) (ev:conn_event) : GTot (option connection_model) =
  match ev with
  | ConnNetworkEvent msg ->
    step_tls_message model msg.CL.message_direction msg.CL.message_value
  | ConnProtectedHandshake step ->
    step_protected_handshake model step
  | ConnLocalEvent local ->
    step_local_event model local
let rec cipher_suite_offered (suites:list T.cipher_suite) (suite:T.cipher_suite)
  : Tot prop
        (decreases suites)
  =
  match suites with
  | [] -> False
  | offered :: rest -> offered == suite \/ cipher_suite_offered rest suite
let rec signature_scheme_offered
  (schemes:list T.signature_scheme)
  (scheme:T.signature_scheme)
  : Tot prop
        (decreases schemes)
  =
  match schemes with
  | [] -> False
  | offered :: rest -> offered == scheme \/ signature_scheme_offered rest scheme
let rec named_group_offered
  (groups:list T.named_group)
  (group:T.named_group)
  : Tot prop
        (decreases groups)
  =
  match groups with
  | [] -> False
  | offered :: rest -> offered == group \/ named_group_offered rest group
let sni_policy_accepts
  (policy:option T.hostname)
  (client_sni:option T.hostname)
  : prop =
  match policy with
  | None -> True
  | Some expected -> client_sni == Some expected
let server_selection_acceptable
  (cfg:server_config)
  (selection:server_handshake_selection)
  : prop =
  let ch = selection.server_selected_client_hello in
  cipher_suite_offered
    cfg.server_supported_cipher_suites
    selection.server_selected_cipher_suite /\
  cipher_suite_offered
    (Sem.clientHello_cipher_suites ch)
    selection.server_selected_cipher_suite /\
  named_group_offered
    cfg.server_supported_groups
    selection.server_selected_group /\
  signature_scheme_offered
    cfg.server_allowed_signature_schemes
    selection.server_selected_signature_scheme /\
  (match Sem.clientHello_sig_algs ch with
   | Some sas ->
     signature_scheme_offered sas selection.server_selected_signature_scheme
   | None -> False) /\
  selection.server_selected_credential == cfg.server_credential_identity /\
  sni_policy_accepts cfg.server_sni_policy (Sem.clientHello_server_name ch) /\
  server_selection_key_share_consistent selection
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
let client_hello_matches_start (start:handshake_start) (ch:GCH.clientHello) : prop =
  Seq.equal (Sem.clientHello_random ch) start.start_client_random /\
  Sem.clientHello_server_name ch == Some start.start_server_name /\
  (match Sem.clientHello_key_share_x25519 ch with
   | Some k -> B.length k = 32 /\ Seq.equal k start.start_client_key_share_public
   | None -> False) /\
  Sem.clientHello_cipher_suites ch == start.start_cipher_suites /\
  Sem.clientHello_sig_algs ch == Some start.start_signature_schemes /\
  (* A ClientHello is only ever sent inside a single TLS plaintext record, whose
     fragment is bounded by 16640 bytes; with the QuackyDucky-generated codec the
     wire image is no longer canonical-by-construction, so this record-size bound
     is stated explicitly here (it used to be implied by the hand-written
     canonical ClientHello serializer). *)
  B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640
let server_hello_matches_selection
  (selection:server_handshake_selection)
  (sh:GSH.serverHello)
  : prop =
  (match Sem.serverHello_random sh with
   | Some r -> Seq.equal r selection.server_random
   | None -> False) /\
  (match Sem.serverHello_key_share_x25519 sh with
   | Some k -> B.length k = 32 /\ Seq.equal k selection.server_key_share_public
   | None -> False) /\
  selection.server_selected_cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256 /\
  Sem.serverHello_cipher_suite sh == Some selection.server_selected_cipher_suite /\
  B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640
let certificate_msg_matches_server_config
  (cfg:server_config)
  (cert:GCert.certificate)
  : prop =
  (Sem.certificate_entries cert) == [cfg.server_certificate_chain]
let server_certificate_verify_signature_valid
  (selection:server_handshake_selection)
  (hs:handshake_state)
  (cv:GCV.certificateVerify)
  : prop =
  Sem.certificateVerify_scheme cv == selection.server_selected_signature_scheme /\
  C.verify_signature
    (Sem.certificateVerify_scheme cv)
    selection.server_selected_credential
    (H.certificate_verify_input (Tr.hash hs.hs_transcript))
    (Sem.certificateVerify_signature_bytes cv)
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
let traffic_install_matches_key_schedule_for_role
  (role:endpoint_role)
  (hs:handshake_state)
  (install:traffic_key_install)
  : GTot prop =
  match expected_traffic_secret_for_role
          role
          hs
          install.install_epoch
          install.install_direction with
  | Some secret ->
    install.install_material == traffic_key_material_for_secret secret
  | None -> False
let application_traffic_available_for_role
  (role:endpoint_role)
  (hs:handshake_state)
  (dir:direction)
  : GTot prop =
  let traffic_dir =
    match dir with
    | CL.Sent -> TrafficWrite
    | CL.Received -> TrafficRead in
  Some?
    (traffic_material_for_label
      hs.hs_keys
      TrafficApplication
      (traffic_label_for_endpoint_direction role traffic_dir))
let traffic_install_allowed_at_stage
  (stage:handshake_stage)
  (install:traffic_key_install)
  : prop =
  match install.install_epoch with
  | TrafficHandshake -> stage == HsServerHelloReceived
  | TrafficApplication -> stage == HsServerFinishedVerified
let traffic_install_allowed_at_stage_for_role
  (role:endpoint_role)
  (stage:handshake_stage)
  (install:traffic_key_install)
  : prop =
  match role with
  | ClientEndpoint ->
    traffic_install_allowed_at_stage stage install
  | ServerEndpoint ->
    (match install.install_epoch with
     | TrafficHandshake -> stage == HsServerHelloSent
     | TrafficApplication ->
       (match install.install_direction with
        | TrafficWrite -> stage == HsServerFinishedSent
        | TrafficRead -> stage == HsClientFinishedReceived))
let legal_local_event (model:connection_model) (ev:local_event) : GTot prop =
  let hs = model.model_handshake in
  match ev, model.model_control with
  | LocalStartHandshake start, ControlNew ->
    model.model_config.config_role == ClientEndpoint /\
    start_matches_config model.model_config start /\
    handshake_start_key_share_consistent start
  | LocalStartServer, ControlNew ->
    model.model_config.config_role == ServerEndpoint /\
    (match model.model_config.config_server with
     | Some _ -> True
     | None -> False)
  | LocalSelectServerParameters selection, ControlHandshaking HsClientHelloReceived ->
    model.model_config.config_role == ServerEndpoint /\
    hs.hs_server_selection == None /\
    hs.hs_keys.ks_shared_secret == None /\
    hs.hs_client_hello == Some selection.server_selected_client_hello /\
    (match model.model_config.config_server with
     | Some cfg -> server_selection_acceptable cfg selection
     | None -> False)
  | LocalDeriveSharedSecret shared, ControlHandshaking HsServerHelloReceived ->
    model.model_config.config_role == ClientEndpoint /\
    hs.hs_keys.ks_shared_secret == None /\
    (match hs.hs_start, hs.hs_server_hello with
     | Some start, Some sh ->
       handshake_start_key_share_consistent start /\
       (match start.start_client_key_share_private with
        | Some sk ->
          (match server_hello_key_share sh with
           | Some k -> C.x25519_shared sk k == Some shared
           | None -> False)
        | None -> False)
     | _, _ -> False)
  | LocalDeriveSharedSecret shared, ControlHandshaking HsClientHelloReceived ->
    model.model_config.config_role == ServerEndpoint /\
    hs.hs_keys.ks_shared_secret == None /\
    (match hs.hs_server_selection with
     | Some selection ->
       server_selection_key_share_consistent selection /\
       (match selection.server_key_share_private with
       | Some sk ->
         (match client_hello_key_share selection.server_selected_client_hello with
          | Some k -> C.x25519_shared sk k == Some shared
          | None -> False)
       | None -> False)
     | None -> False)
  | LocalInstallTrafficKeys install, ControlHandshaking stage ->
    model.model_config.config_role == ClientEndpoint /\
    traffic_install_allowed_at_stage stage install /\
    traffic_install_matches_key_schedule hs install
  | LocalInstallTrafficKeysForRole role_install, ControlHandshaking stage ->
    role_install.install_role == model.model_config.config_role /\
    traffic_install_allowed_at_stage_for_role
      role_install.install_role
      stage
      role_install.install_payload /\
    traffic_install_matches_key_schedule_for_role
      role_install.install_role
      hs
      role_install.install_payload
  | LocalValidateCertificate peer, ControlHandshaking HsCertificateReceived ->
    model.model_config.config_role == ClientEndpoint /\
    (match hs.hs_certificate with
     | Some cert ->
       X.validate_chain
         model.model_config.config_server_name
         model.model_config.config_validation_time
         model.model_config.config_trust_store
         (Sem.certificate_entries cert) == Some peer
     | None -> False)
  | LocalVerifyCertificateSignature cv, ControlHandshaking HsCertificateVerifyReceived ->
    model.model_config.config_role == ClientEndpoint /\
    (match hs.hs_validated_peer, hs.hs_certificate_verify, hs.hs_buffers.hb_certificate_verify_input with
     | Some peer, Some stored_cv, Some input ->
       stored_cv == cv /\
       C.verify_signature (Sem.certificateVerify_scheme cv) peer.X.leaf_public_key input (Sem.certificateVerify_signature_bytes cv)
     | _, _, _ -> False)
  | LocalSignCertificateVerify cv, ControlHandshaking HsServerEncryptedFlightSent ->
    model.model_config.config_role == ServerEndpoint /\
    hs.hs_certificate_verify == None /\
    W.certificateVerify_representable cv /\
    (match hs.hs_certificate, hs.hs_server_selection with
     | Some _, Some selection ->
       server_certificate_verify_signature_valid selection hs cv /\
       signature_scheme_offered
         model.model_config.config_signature_schemes
         (Sem.certificateVerify_scheme cv)
     | _, _ -> False)
  | LocalVerifyFinished fin, ControlHandshaking HsServerFinishedReceived ->
    model.model_config.config_role == ClientEndpoint /\
    (match hs.hs_server_finished, hs.hs_keys.ks_server_handshake_traffic with
     | Some stored_fin, Some server_hs ->
       stored_fin == fin /\
       H.verify_finished server_hs.traffic_secret (Tr.hash hs.hs_transcript) fin
     | _, _ -> False)
  | LocalVerifyClientFinished fin, ControlHandshaking HsClientFinishedReceived ->
    model.model_config.config_role == ServerEndpoint /\
    application_record_keys_installed_for_role ServerEndpoint model /\
    (match hs.hs_client_finished, hs.hs_keys.ks_client_handshake_traffic with
     | Some stored_fin, Some client_hs ->
       stored_fin == fin /\
       H.verify_finished client_hs.traffic_secret (Tr.hash hs.hs_transcript) fin
     | _, _ -> False)
  | LocalDeliverApplicationData bytes, ControlApplicationData ->
    (* NOTE (application-data stream integrity): `app_pending_plaintext` is set
       once to `B.empty` in `empty_application_state` and never written again by
       any step, so this legality guard forces `bytes == B.empty`.  The
       TLS-to-host-application delivery hop is thus unimplemented: it can only
       ever append an empty chunk to `app_received`, leaving the received byte
       stream (the concatenation) unchanged.  The Pulse drivers statically
       exclude this event. *)
    exists pending.
      Seq.equal model.model_application.app_pending_plaintext (B.append bytes pending)
  | LocalFail _, _ ->
    True
  | _, _ ->
    False
let protected_handshake_buffer_empty (model:connection_model) : prop =
  Seq.equal
    model.model_handshake.hs_buffers.hb_encrypted_server_handshake_bytes
    B.empty /\
  model.model_handshake.hs_buffers.hb_encrypted_server_handshake_parsed == 0

(* An empty pending buffer leaves nothing to prepend, so a step's parse stream
   is exactly its fragment.  This is the bridge that keeps every property
   proved before cross-record reassembly applicable: such properties carry
   [protected_handshake_buffer_empty] (directly, or via the reachability
   invariants that establish it), and under it the generalised
   [legal_protected_handshake_step] and [step_protected_handshake] coincide
   with the fragment-only versions they replace. *)
let lemma_protected_handshake_stream_of_buffer_empty
  (model:connection_model)
  (step:protected_handshake_step)
  : Lemma
      (requires protected_handshake_buffer_empty model)
      (ensures
        Seq.equal
          (protected_handshake_stream model step)
          step.protected_handshake_fragment)
      [SMTPat (protected_handshake_stream model step);
       SMTPat (protected_handshake_buffer_empty model)]
  = Seq.append_empty_l step.protected_handshake_fragment

(* A tail step never prepends: its stream is its fragment unconditionally. *)
let lemma_protected_handshake_stream_tail
  (model:connection_model)
  (step:protected_handshake_step)
  : Lemma
      (requires step.protected_handshake_head == false)
      (ensures
        protected_handshake_stream model step ==
        step.protected_handshake_fragment)
  = ()

(* Local events never touch the protected-handshake reassembly buffer.  The
   only [hs_buffers] field any of them writes is [hb_certificate_verify_input]
   (at [LocalSignCertificateVerify]).  This is what lets a normalisation proved
   at one model be transported across an intervening local event, e.g. the
   client's traffic-key install ahead of the server flight. *)
let lemma_local_event_preserves_protected_handshake_buffer
  (model:connection_model)
  (ev:local_event)
  (model1:connection_model)
  : Lemma
      (requires step_local_event model ev == Some model1)
      (ensures
        model1.model_handshake.hs_buffers.hb_encrypted_server_handshake_bytes ==
          model.model_handshake.hs_buffers.hb_encrypted_server_handshake_bytes /\
        model1.model_handshake.hs_buffers.hb_encrypted_server_handshake_parsed ==
          model.model_handshake.hs_buffers.hb_encrypted_server_handshake_parsed)
  = ()

let legal_handshake_message
  (model:connection_model)
  (dir:direction)
  (msg:M.handshake_msg)
  : GTot prop =
  let hs = model.model_handshake in
  match dir, msg, model.model_control with
  | CL.Sent, M.ClientHello ch, ControlHandshaking HsStarted ->
    model.model_config.config_role == ClientEndpoint /\
    (match hs.hs_start with
     | Some start -> client_hello_matches_start start ch
     | None -> False)
  | CL.Received, M.ClientHello _, ControlHandshaking HsAwaitingClientHello ->
    model.model_config.config_role == ServerEndpoint /\
    (match model.model_config.config_server with
     | Some _ -> True
     | None -> False)
  | CL.Received, M.ServerHello sh, ControlHandshaking HsClientHelloSent ->
    model.model_config.config_role == ClientEndpoint /\
    B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640 /\
    (match Sem.serverHello_cipher_suite sh with
     | Some cs ->
       H.is_supported_cipher_suite cs /\
       (match hs.hs_start with
        | Some start -> cipher_suite_offered start.start_cipher_suites cs
        | None -> False)
     | None -> False)
  | CL.Sent, M.ServerHello sh, ControlHandshaking HsClientHelloReceived ->
    model.model_config.config_role == ServerEndpoint /\
    Some? hs.hs_keys.ks_shared_secret /\
    (match hs.hs_server_selection with
     | Some selection -> server_hello_matches_selection selection sh
     | None -> False)
  | CL.Sent, M.EncryptedExtensions ee, ControlHandshaking HsServerHelloSent ->
    model.model_config.config_role == ServerEndpoint /\
    Sem.encryptedExtensions_alpn ee == None /\
    Some? hs.hs_keys.ks_server_handshake_traffic
  | CL.Sent, M.Certificate cert, ControlHandshaking HsServerEncryptedFlightSent ->
    model.model_config.config_role == ServerEndpoint /\
    hs.hs_encrypted_extensions <> None /\
    hs.hs_certificate == None /\
    Some? hs.hs_keys.ks_server_handshake_traffic /\
    W.certificate_representable cert /\
    (match model.model_config.config_server with
     | Some cfg -> certificate_msg_matches_server_config cfg cert
     | None -> False)
  | CL.Sent, M.CertificateVerify cv, ControlHandshaking HsServerEncryptedFlightSent ->
    model.model_config.config_role == ServerEndpoint /\
    hs.hs_certificate <> None /\
    hs.hs_certificate_verify_verified == false /\
    Some? hs.hs_keys.ks_server_handshake_traffic /\
    W.certificateVerify_representable cv /\
    (match hs.hs_certificate_verify with
     | Some stored_cv -> stored_cv == cv
     | None -> False)
  | CL.Sent, M.Finished fin, ControlHandshaking HsServerEncryptedFlightSent ->
    model.model_config.config_role == ServerEndpoint /\
    hs.hs_certificate_verify_verified /\
    (match hs.hs_keys.ks_server_handshake_traffic with
     | Some server_hs ->
       H.verify_finished server_hs.traffic_secret (Tr.hash hs.hs_transcript) fin
     | None -> False)
  | CL.Received, M.EncryptedExtensions _, ControlHandshaking HsServerHelloReceived ->
    model.model_config.config_role == ClientEndpoint /\
    Some? hs.hs_keys.ks_server_handshake_traffic
  | CL.Received, M.Certificate cert, ControlHandshaking HsEncryptedExtensionsReceived ->
    model.model_config.config_role == ClientEndpoint /\
    (Sem.certificate_entries cert) <> []
  | CL.Received, M.CertificateVerify _, ControlHandshaking HsCertificateValidated ->
    model.model_config.config_role == ClientEndpoint /\
    Some? hs.hs_validated_peer
  | CL.Received, M.Finished _, ControlHandshaking HsCertificateVerifyVerified ->
    model.model_config.config_role == ClientEndpoint /\
    Some? hs.hs_keys.ks_server_handshake_traffic /\
    Some? hs.hs_keys.ks_master_secret
  | CL.Received, M.Finished _, ControlHandshaking HsServerFinishedSent ->
    model.model_config.config_role == ServerEndpoint /\
    Some? hs.hs_keys.ks_client_handshake_traffic /\
    Some? hs.hs_keys.ks_master_secret /\
    // Stream-integrity fix: a server may not accept the client Finished (and
    // thereby atomically enter ControlApplicationData) until it has installed its
    // own application WRITE key.  Faithful to TLS 1.3 (both application traffic
    // secrets are derived together, through the server Finished), and it removes a
    // Fix-1 atomicity wart whereby a server could reach application data
    // permanently unable to send.  The Pulse server driver already installs this
    // key (LocalInstallServerApplicationTrafficKeys at HsServerFinishedSent) before
    // it can process the client Finished, so this guard is always satisfied by the
    // implementation.
    Some? hs.hs_keys.ks_server_application_traffic
  | CL.Sent, M.Finished _, ControlHandshaking HsServerFinishedVerified ->
    model.model_config.config_role == ClientEndpoint /\
    // The client may not declare the handshake finished while it still holds
    // unconsumed protected-handshake plaintext.  Without this guard the client
    // reaches ControlApplicationData with a non-empty pending buffer, and
    // because legal_handshake_message admits no message at all in
    // ControlApplicationData that plaintext can never be drained: the endpoint
    // is wedged permanently unsettled.  See TLS13.System.Internal.
    protected_handshake_buffer_empty model /\
    Some? hs.hs_keys.ks_client_handshake_traffic /\
    Some? hs.hs_keys.ks_client_application_traffic /\
    Some? hs.hs_keys.ks_server_application_traffic /\
    // Stream-integrity fix (RECORD level, not slot level).  The three conjuncts
    // above are SLOT-level (key-schedule slots); they say nothing about the
    // RECORD layer.  The client's handshake-WRITE record install is an OPTIONAL
    // local (`traffic_install_allowed_at_stage_for_role` only *permits* it at
    // `HsServerHelloReceived`; nothing compels it), so without this conjunct a
    // client could legally send its Finished with
    // `model_record.record_write.epoch == Initial` and no write key.  `Sent,
    // Finished` is not cleartext, so the protected branch of
    // `network_message_raw_delta_legal` would then tie the wire bytes to no seal
    // at all -- a "garbage protected" record -- which makes the ToServer
    // handshake-seal bridge genuinely FALSE, not merely underivable.  The server
    // side has no such hole because its handshake-write install is control-forced
    // (`lemma_server_handshake_write_record_has_keys`).
    //
    // This is the same move as the `Received, Finished, HsServerFinishedSent` arm
    // immediately above, one level down.  It is faithful to TLS 1.3: a client
    // cannot send an encrypted Finished without its handshake write keys.  The
    // Pulse client driver selects `LocalInstallClientHandshakeTrafficKeys`
    // (TrafficHandshake + TrafficWrite) at `HsServerHelloReceived`, well before
    // the Finished send, so the guard is always satisfied by the implementation.
    //
    // WEAKEST SUFFICIENT GUARD: only `Some? key` is demanded, not `Some?
    // static_iv` and not an epoch pin.  Under `connection_state_consistent`,
    // `Some? key` already excludes `R.Initial` (the Initial arm forces
    // `key == None`) and the committed negative-epoch lemmas exclude
    // `R.Application`, so `lemma_client_finished_verified_write_epoch_handshake`
    // yields `epoch == R.Handshake`; consistency's Handshake arm then supplies
    // the full traffic-material match, hence `static_iv` too.
    Some? model.model_record.record_write.R.key
  | CL.Received, M.HelloRetryRequest, ControlHandshaking HsClientHelloSent ->
    model.model_config.config_role == ClientEndpoint /\
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
    (* Note: a client-received PROTECTED handshake message may also be
       delivered by [ConnProtectedHandshake] with [protected_handshake_head],
       including when the record carries exactly one message.  The two
       descriptions denote the SAME transition -- see
       [TLS13.Spec.StateMachine.Replay.lemma_single_message_head_step_replay_normalizes].
       The implementation emits only the head/tail form, so there is one
       receive path; this route is retained so that the pairing proofs can
       normalise into it. *)
    legal_handshake_message model dir handshake_msg
  | M.TlsApplicationData _, ControlApplicationData ->
    application_traffic_available_for_role
      model.model_config.config_role
      hs
      dir
  | M.TlsIgnoredPostHandshake _, ControlApplicationData ->
    model.model_config.config_role == ClientEndpoint /\
    dir == CL.Received /\ Some? hs.hs_keys.ks_server_application_traffic
  | M.TlsKeyUpdate req, ControlApplicationData ->
    (* Either endpoint may rotate, and either may initiate.  The material that
       has to exist is exactly the one this direction rotates -- our read key
       on receive, our write key on send -- which keeps this predicate in step
       with [rotate_application_traffic]'s success condition. *)
    Some?
      (traffic_material_for_label
         hs.hs_keys
         TrafficApplication
         (traffic_label_for_endpoint_direction
            model.model_config.config_role
            (match dir with
             | CL.Received -> TrafficRead
             | CL.Sent -> TrafficWrite)))
  | M.TlsAlert T.Close_notify, ControlApplicationData ->
    True
  | M.TlsAlert T.Close_notify, ControlClosing ->
    dir == CL.Received
  | M.TlsAlert _, _ ->
    True
  | M.TlsChangeCipherSpec, ControlHandshaking _ ->
    True
  | _, _ ->
    False
(* The largest accumulated protected-handshake plaintext a client will hold
   while reassembling a message that spans several records.  It matches the
   implementation's [max_handshake_flight_len].

   A cap is not a convenience: without one, a peer could feed unboundedly
   many records that each merely extend the pending buffer, and the number of
   records a client accepts in the handshake-receiving region would no longer
   be bounded by the number of messages it has taken delivery of.  Capping
   the buffer restores a bound -- messages plus buffered bytes -- because
   every buffered record contributes at least one byte. *)
let max_pending_protected_handshake : nat = 32768

(* The stages at which a CLIENT can receive a protected handshake message,
   and hence the only stages at which it may set protected plaintext aside.

   These are exactly the [CL.Received] client arms of
   [legal_handshake_message] for the four supported protected messages:
   [EncryptedExtensions], [Certificate], [CertificateVerify] and [Finished].
   Deriving the buffering guard from them is what keeps buffering from
   weakening any stage-gated property.  In particular
   [HsCertificateReceived] is absent -- the pipeline is genuinely blocked
   there until [LocalValidateCertificate] runs -- so "receiving Certificate
   blocks the pipeline" survives unchanged. *)
let protected_handshake_buffering_stage (stage:handshake_stage) : bool =
  match stage with
  | HsServerHelloReceived
  | HsEncryptedExtensionsReceived
  | HsCertificateValidated
  | HsCertificateVerifyVerified -> true
  | _ -> false

let legal_protected_handshake_step
  (model:connection_model)
  (step:protected_handshake_step)
  : GTot prop =
  let offset = step.protected_handshake_offset in
  let consumed = step.protected_handshake_consumed in
  model.model_config.config_role == ClientEndpoint /\
  (if step.protected_handshake_buffering
   then
     (* A BUFFERING step takes delivery of a record and sets its plaintext
        aside without interpreting it.  It is what makes a handshake message
        spanning three or more records deliverable: with only message-bearing
        steps, reassembly stalls the moment one record plus the accumulated
        leftover still does not contain a whole message, because no step is
        then enabled and the record cannot be left undecrypted (opening it
        advances the read sequence irreversibly).

        It carries no message, so [protected_handshake_message],
        [protected_handshake_offset] and [protected_handshake_consumed] say
        nothing and are pinned to inert values.

        Buffering is confined to the stages at which the client can actually
        receive a protected handshake message (see
        [protected_handshake_buffering_stage]).  Anywhere else the buffer
        could never be drained, so admitting it would be a way to wedge the
        endpoint while still consuming records. *)
     step.protected_handshake_head == true /\
     offset == 0 /\
     consumed == 0 /\
     0 < B.length step.protected_handshake_fragment /\
     B.length (protected_handshake_stream model step) <=
       max_pending_protected_handshake /\
     (match model.model_control with
      | ControlHandshaking stage -> protected_handshake_buffering_stage stage
      | _ -> False) /\
     (* Buffering is a LAST RESORT, not an alternative to delivering a
        message: it is legal only when a head step is genuinely unavailable.
        Either there is already pending plaintext (the head rule demands
        [protected_handshake_buffer_empty], so a non-empty buffer forces this
        step to be a buffering one), or this record's own plaintext, taken
        alone, does not parse as a whole handshake message (so the head rule
        cannot fire on it either).  Without this conjunct a client could
        legally buffer a record that *does* carry a complete message instead
        of delivering it, letting it accept arbitrarily many records-worth of
        already-decodable messages while never advancing past a single
        buffering-eligible control -- which is exactly the reassembly
        mechanism, but pointed at messages that need no reassembly at all. *)
     (~ (protected_handshake_buffer_empty model) \/
      W.parse_handshake step.protected_handshake_fragment == None)
   else
     offset < B.length step.protected_handshake_fragment /\
     0 < consumed /\
     offset + consumed <= B.length step.protected_handshake_fragment /\
     protected_handshake_message_supported step.protected_handshake_message /\
     W.parse_handshake
       (Seq.slice
         step.protected_handshake_fragment
         offset
         (B.length step.protected_handshake_fragment)) ==
       Some (step.protected_handshake_message, consumed) /\
     legal_handshake_message model CL.Received step.protected_handshake_message /\
     (if step.protected_handshake_head
      then
        (* The head step takes delivery of a whole record, so its offset comes
           off the wire rather than from state, and nothing may be pending.

           [consumed] is NOT required to be strictly less than the fragment
           length.  That strict inequality was what forced a record carrying
           exactly one message down the [ConnNetworkEvent] path and created
           the fork; dropping it lets the head step describe such a record,
           with the pending buffer left empty by
           [set_pending_protected_handshake] and no tail steps following.

           A message spanning several records is NOT handled here: the head
           step reads only this record's plaintext.  It is handled by
           BUFFERING steps, which accumulate plaintext until a whole message
           is present and then let ordinary TAIL steps drain it.  Keeping the
           head rule exactly as it was is what leaves every sender/receiver
           pairing proof untouched. *)
        protected_handshake_buffer_empty model /\
        offset == 0
      else
        Seq.equal
          step.protected_handshake_fragment
          model.model_handshake.hs_buffers.hb_encrypted_server_handshake_bytes /\
        offset ==
          model.model_handshake.hs_buffers.hb_encrypted_server_handshake_parsed))
let legal_event (model:connection_model) (ev:conn_event) : GTot prop =
  match ev with
  | ConnNetworkEvent msg ->
    legal_tls_message model msg.CL.message_direction msg.CL.message_value
  | ConnProtectedHandshake step ->
    legal_protected_handshake_step model step
  | ConnLocalEvent local ->
    legal_local_event model local
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
let serialized_cleartext_tls_message (msg:M.tls_message) : GTot B.bytes =
  let (content_type, fragment) = W.serialize_tls_message msg in
  W.serialize_record content_type fragment
let cleartext_tls_message_raw (msg:M.tls_message) (raw:B.bytes) : GTot prop =
  match msg with
  | M.TlsHandshake M.HelloRetryRequest ->
    raw_records_exactly raw T.Handshake 1
  | _ ->
    Seq.equal raw (serialized_cleartext_tls_message msg)
let received_cleartext_tls_message_raw (msg:M.tls_message) (raw:B.bytes) : GTot prop =
  match msg with
  | M.TlsHandshake (M.ClientHello _) ->
    exists fragment.
      W.parse_record_wire raw == Some (T.Handshake, fragment, B.length raw) /\
      W.parse_tls_message T.Handshake fragment == Some msg
  | _ ->
    cleartext_tls_message_raw msg raw
let network_message_is_cleartext (dir:direction) (msg:M.tls_message) : bool =
  match dir, msg with
  | CL.Sent, M.TlsHandshake (M.ClientHello _) -> true
  | CL.Received, M.TlsHandshake (M.ClientHello _) -> true
  | CL.Received, M.TlsHandshake (M.ServerHello _) -> true
  | CL.Sent, M.TlsHandshake (M.ServerHello _) -> true
  | CL.Received, M.TlsHandshake M.HelloRetryRequest -> true
  | _, M.TlsChangeCipherSpec -> true
  | _, _ -> false
let protected_record_count (dir:direction) (msg:M.tls_message) : nat =
  match dir, msg with
  | CL.Sent, M.TlsApplicationData bytes -> RF.application_data_record_count bytes
  | _, _ -> 1
let network_message_raw_delta_legal
  (model:connection_model)
  (msg:directed_message M.tls_message)
  (raw:B.bytes)
  : GTot prop =
  if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
  then
    match msg.CL.message_direction with
    | CL.Sent -> cleartext_tls_message_raw msg.CL.message_value raw
    | CL.Received -> received_cleartext_tls_message_raw msg.CL.message_value raw
  else
    raw_records_exactly
      raw
      T.Application_data
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
  | ConnProtectedHandshake step ->
    Seq.equal raw_sent B.empty /\
    (if step.protected_handshake_head
     then raw_records_exactly raw_received T.Application_data 1
     else Seq.equal raw_received B.empty)
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction with
     | CL.Sent ->
       network_message_raw_delta_legal model msg raw_sent /\
       Seq.equal raw_received B.empty
     | CL.Received ->
       Seq.equal raw_sent B.empty /\
       network_message_raw_delta_legal model msg raw_received)
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
