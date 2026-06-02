module TLS13.Impl.ConnectionState

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box { box, (!), (:=) }
open FStar.List.Tot

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module IM = TLS13.Impl.Messages
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module R = TLS13.Record.Spec
module Rec = TLS13.Record
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module V = Pulse.Lib.Vec
module X = TLS13.X509.Spec

(**
  Concrete connection-state storage for the rich TLS13.Spec.ConnectionState
  model.  Raw wire/event history is ghost-only in [ghost_state], as in the
  calc sample; the extractable fields store the current mutable connection
  model: config, control state, record states, handshake slots, key schedule,
  and pending application buffers.
**)

let state_ref : Type0 = MR.mref CS.connection_state_evolves

noextract
let max_hostname_len : nat = IM.max_server_name_len

noextract
let max_trust_anchors_len : nat = 65536

noextract
let max_public_key_len : nat = 4096

noextract
let max_cipher_suites : nat = IM.max_cipher_suites

noextract
let max_signature_schemes : nat = IM.max_signature_schemes

noextract
let max_client_hello_len : nat = 512

noextract
let max_server_hello_len : nat = 4096

noextract
let max_handshake_flight_len : nat = 32768

noextract
let max_transcript_len : nat = 65536

noextract
let max_certificate_verify_input_len : nat = 256

noextract
let max_pending_plaintext_len : nat = 32768

noextract
let max_pending_raw_len : nat = 32768

noeq
type sized_bytes = {
  bytes: V.vec U8.t;
  len: box SZ.t;
}

noeq
type optional_sized_bytes = {
  present: box bool;
  value: sized_bytes;
}

noeq
type optional_fixed_bytes = {
  present: box bool;
  bytes: V.vec U8.t;
}

noeq
type u16_list_storage = {
  items: V.vec U16.t;
  len: box SZ.t;
}

noeq
type connection_config_storage = {
  role_tag: box U8.t;
  server_name: sized_bytes;
  trust_anchors: sized_bytes;
  validation_time_seconds: box SZ.t;
  cipher_suites: u16_list_storage;
  signature_schemes: u16_list_storage;
}

noeq
type control_storage = {
  control_tag: box U8.t;
  handshake_stage_tag: box U8.t;
  failure_present: box bool;
  failure_code: box U8.t;
  failure_alert: box U8.t;
}

noeq
type traffic_key_material_storage = {
  present: box bool;
  traffic_secret: V.vec U8.t;
  traffic_key: V.vec U8.t;
  traffic_iv: V.vec U8.t;
}

noeq
type optional_secret_storage = {
  present: box bool;
  secret: V.vec U8.t;
}

noeq
type key_schedule_storage = {
  early_secret: optional_secret_storage;
  shared_secret: optional_secret_storage;
  handshake_secret: optional_secret_storage;
  master_secret: optional_secret_storage;
  client_handshake_traffic: traffic_key_material_storage;
  server_handshake_traffic: traffic_key_material_storage;
  client_application_traffic: traffic_key_material_storage;
  server_application_traffic: traffic_key_material_storage;
  exporter_master_secret: optional_secret_storage;
  resumption_master_secret: optional_secret_storage;
}

noeq
type handshake_start_storage = {
  present: box bool;
  server_name: sized_bytes;
  client_random: V.vec U8.t;
  client_key_share_private: optional_fixed_bytes;
  client_key_share_public: V.vec U8.t;
  cipher_suites: u16_list_storage;
  signature_schemes: u16_list_storage;
}

noeq
type handshake_message_storage = {
  client_hello_present: box bool;
  client_hello: IM.client_hello;
  server_hello: box (option IM.server_hello);
  encrypted_extensions_present: box bool;
  encrypted_extensions: IM.encrypted_extensions;
  certificate_present: box bool;
  certificate: IM.certificate_msg;
  certificate_verify_present: box bool;
  certificate_verify: IM.certificate_verify;
  server_finished_present: box bool;
  server_finished: IM.finished;
  client_finished_present: box bool;
  client_finished: IM.finished;
}

noeq
type peer_storage = {
  present: box bool;
  validated_hostname: sized_bytes;
  leaf_public_key: sized_bytes;
  permitted_signature_schemes: u16_list_storage;
}

noeq
type handshake_buffer_storage = {
  client_hello_bytes: sized_bytes;
  server_hello_bytes: sized_bytes;
  encrypted_server_handshake_bytes: sized_bytes;
  encrypted_server_handshake_parsed: box SZ.t;
  certificate_leaf_der: optional_sized_bytes;
  certificate_verify_input: optional_sized_bytes;
}

noeq
type handshake_storage = {
  start: handshake_start_storage;
  messages: handshake_message_storage;
  validated_peer: peer_storage;
  certificate_verify_verified: box bool;
  server_finished_verified: box bool;
  transcript: sized_bytes;
  buffers: handshake_buffer_storage;
  keys: key_schedule_storage;
}

noeq
type record_storage = {
  read: Rec.record_state;
  write: Rec.record_state;
}

noeq
type application_storage = {
  pending_plaintext: sized_bytes;
  pending_source_record: sized_bytes;
  pending_source_offset: box SZ.t;
  pending_received_raw: sized_bytes;
}

noeq
type connection_state = {
  config: connection_config_storage;
  control: control_storage;
  records: record_storage;
  handshake: handshake_storage;
  application: application_storage;
  ghost_state: state_ref;
}

noextract
let connection_state_ref (c:connection_state) : state_ref = c.ghost_state

noextract
let byte_prefix_matches
  (storage:B.bytes)
  (len:SZ.t)
  (bytes:B.bytes)
  : prop =
  SZ.v len <= B.length storage /\
  B.length bytes == SZ.v len /\
  Seq.equal bytes (Seq.slice storage 0 (SZ.v len))

noextract
let fixed_bytes_match
  (storage:B.bytes)
  (n:nat)
  (bytes:B.bytes)
  : prop =
  B.length storage == n /\
  B.length bytes == n /\
  Seq.equal storage bytes

noextract
let optional_fixed_bytes_match
  (present:bool)
  (storage:B.bytes)
  (n:nat)
  (bytes:option (b:B.bytes{B.length b == n}))
  : prop =
  B.length storage == n /\
  (if present then
    match bytes with
    | Some b -> fixed_bytes_match storage n b
    | None -> False
  else
    bytes == None)

noextract
let endpoint_role_tag_matches (tag:U8.t) (role:CS.endpoint_role) : prop =
  match role with
  | CS.ClientEndpoint -> U8.v tag == 0

noextract
let handshake_stage_tag_matches (tag:U8.t) (stage:CS.handshake_stage) : prop =
  match stage with
  | CS.HsNotStarted -> U8.v tag == 0
  | CS.HsStarted -> U8.v tag == 1
  | CS.HsClientHelloSent -> U8.v tag == 2
  | CS.HsServerHelloReceived -> U8.v tag == 3
  | CS.HsEncryptedExtensionsReceived -> U8.v tag == 4
  | CS.HsCertificateReceived -> U8.v tag == 5
  | CS.HsCertificateValidated -> U8.v tag == 6
  | CS.HsCertificateVerifyReceived -> U8.v tag == 7
  | CS.HsCertificateVerifyVerified -> U8.v tag == 8
  | CS.HsServerFinishedReceived -> U8.v tag == 9
  | CS.HsServerFinishedVerified -> U8.v tag == 10
  | CS.HsClientFinishedSent -> U8.v tag == 11

noextract
let alert_tag_matches (tag:U8.t) (alert:T.alert_description) : prop =
  IM.alert_description_matches tag alert

noextract
let tls_error_code_matches
  (code:U8.t)
  (alert:U8.t)
  (err:T.tls_error)
  : prop =
  match err with
  | T.AlertError a -> U8.v code == 0 /\ alert_tag_matches alert a
  | T.UnsupportedCipherSuite -> U8.v code == 1
  | T.UnsupportedNamedGroup -> U8.v code == 2
  | T.UnsupportedSignature -> U8.v code == 3
  | T.HelloRetryRequestRejected -> U8.v code == 4
  | T.BadCertificate -> U8.v code == 5
  | T.BadCertificateVerify -> U8.v code == 6
  | T.BadFinished -> U8.v code == 7
  | T.BadRecordTag -> U8.v code == 8
  | T.OutputBufferTooSmall -> U8.v code == 9
  | T.IoError -> U8.v code == 10

noextract
let failure_option_matches
  (present:bool)
  (code:U8.t)
  (alert:U8.t)
  (failure:option T.tls_error)
  : prop =
  if present then
    match failure with
    | Some err -> tls_error_code_matches code alert err
    | None -> False
  else
    failure == None

noextract
let control_state_matches
  (control_tag:U8.t)
  (stage_tag:U8.t)
  (failure_present:bool)
  (failure_code:U8.t)
  (failure_alert:U8.t)
  (control:CS.connection_control_state)
  : prop =
  match control with
  | CS.ControlNew ->
    U8.v control_tag == 0 /\ not failure_present
  | CS.ControlHandshaking stage ->
    U8.v control_tag == 1 /\
    handshake_stage_tag_matches stage_tag stage /\
    not failure_present
  | CS.ControlApplicationData ->
    U8.v control_tag == 2 /\ not failure_present
  | CS.ControlClosing ->
    U8.v control_tag == 3 /\ not failure_present
  | CS.ControlClosed ->
    U8.v control_tag == 4 /\ not failure_present
  | CS.ControlFailed err ->
    U8.v control_tag == 5 /\
    failure_present /\
    tls_error_code_matches failure_code failure_alert err

let sized_bytes_allocated
  ([@@@mkey] slot:sized_bytes)
  (cap:nat)
  : slprop =
  exists* bytes len.
    V.pts_to slot.bytes bytes **
    Box.pts_to slot.len len **
    pure (V.is_full_vec slot.bytes /\
          V.length slot.bytes == cap /\
          B.length bytes == cap /\
          SZ.v len <= cap)

let sized_bytes_exactly
  ([@@@mkey] slot:sized_bytes)
  (cap:nat)
  (bytes:B.bytes)
  : slprop =
  exists* storage len.
    V.pts_to slot.bytes storage **
    Box.pts_to slot.len len **
    pure (V.is_full_vec slot.bytes /\
          V.length slot.bytes == cap /\
          B.length storage == cap /\
          SZ.v len <= cap /\
          byte_prefix_matches storage len bytes)

let optional_sized_bytes_exactly
  ([@@@mkey] slot:optional_sized_bytes)
  (cap:nat)
  (bytes:option B.bytes)
  : slprop =
  exists* present.
    Box.pts_to slot.present present **
    (if present then
       match bytes with
       | Some b -> sized_bytes_exactly slot.value cap b
       | None -> sized_bytes_allocated slot.value cap ** pure False
     else
       sized_bytes_allocated slot.value cap ** pure (bytes == None))

let fixed_bytes_allocated
  ([@@@mkey] bytes:V.vec U8.t)
  (n:nat)
  : slprop =
  exists* storage.
    V.pts_to bytes storage **
    pure (V.is_full_vec bytes /\
          V.length bytes == n /\
          B.length storage == n)

let fixed_bytes_exactly
  ([@@@mkey] bytes:V.vec U8.t)
  (n:nat)
  (spec:B.bytes)
  : slprop =
  exists* storage.
    V.pts_to bytes storage **
    pure (V.is_full_vec bytes /\
          V.length bytes == n /\
          fixed_bytes_match storage n spec)

let optional_fixed_bytes_exactly
  ([@@@mkey] slot:optional_fixed_bytes)
  (n:nat)
  (spec:option (b:B.bytes{B.length b == n}))
  : slprop =
  exists* present storage.
    Box.pts_to slot.present present **
    V.pts_to slot.bytes storage **
    pure (V.is_full_vec slot.bytes /\
          V.length slot.bytes == n /\
          optional_fixed_bytes_match present storage n spec)

let cipher_suite_list_allocated
  ([@@@mkey] slot:u16_list_storage)
  (cap:nat)
  : slprop =
  exists* items len.
    V.pts_to slot.items items **
    Box.pts_to slot.len len **
    pure (V.is_full_vec slot.items /\
          V.length slot.items == cap /\
          Seq.length items == cap /\
          SZ.v len <= cap)

let cipher_suite_list_exactly
  ([@@@mkey] slot:u16_list_storage)
  (cap:nat)
  (suites:list T.cipher_suite)
  : slprop =
  exists* items len.
    V.pts_to slot.items items **
    Box.pts_to slot.len len **
    pure (V.is_full_vec slot.items /\
          V.length slot.items == cap /\
          Seq.length items == cap /\
          SZ.v len <= cap /\
          IM.cipher_suites_match items (SZ.v len) suites)

let signature_scheme_list_allocated
  ([@@@mkey] slot:u16_list_storage)
  (cap:nat)
  : slprop =
  exists* items len.
    V.pts_to slot.items items **
    Box.pts_to slot.len len **
    pure (V.is_full_vec slot.items /\
          V.length slot.items == cap /\
          Seq.length items == cap /\
          SZ.v len <= cap)

let signature_scheme_list_exactly
  ([@@@mkey] slot:u16_list_storage)
  (cap:nat)
  (schemes:list T.signature_scheme)
  : slprop =
  exists* items len.
    V.pts_to slot.items items **
    Box.pts_to slot.len len **
    pure (V.is_full_vec slot.items /\
          V.length slot.items == cap /\
          Seq.length items == cap /\
          SZ.v len <= cap /\
          IM.signature_schemes_match items (SZ.v len) schemes)

let connection_config_exactly
  ([@@@mkey] cfg:connection_config_storage)
  (spec:CS.connection_config)
  : slprop =
  exists* role validation_time.
    Box.pts_to cfg.role_tag role **
    sized_bytes_exactly cfg.server_name max_hostname_len spec.CS.config_server_name **
    sized_bytes_exactly cfg.trust_anchors max_trust_anchors_len spec.CS.config_trust_store.X.anchors **
    Box.pts_to cfg.validation_time_seconds validation_time **
    cipher_suite_list_exactly cfg.cipher_suites max_cipher_suites spec.CS.config_cipher_suites **
    signature_scheme_list_exactly cfg.signature_schemes max_signature_schemes spec.CS.config_signature_schemes **
    pure (endpoint_role_tag_matches role spec.CS.config_role /\
          SZ.v validation_time == spec.CS.config_validation_time.X.seconds_since_epoch)

let control_exactly
  ([@@@mkey] control:control_storage)
  (model_control:CS.connection_control_state)
  (failure:option T.tls_error)
  : slprop =
  exists* control_tag stage_tag failure_present failure_code failure_alert.
    Box.pts_to control.control_tag control_tag **
    Box.pts_to control.handshake_stage_tag stage_tag **
    Box.pts_to control.failure_present failure_present **
    Box.pts_to control.failure_code failure_code **
    Box.pts_to control.failure_alert failure_alert **
    pure (control_state_matches
            control_tag
            stage_tag
            failure_present
            failure_code
            failure_alert
            model_control /\
          failure_option_matches failure_present failure_code failure_alert failure)

let optional_secret_exactly
  ([@@@mkey] slot:optional_secret_storage)
  (spec:option (b:B.bytes{B.length b == 32}))
  : slprop =
  exists* present secret.
    Box.pts_to slot.present present **
    V.pts_to slot.secret secret **
    pure (V.is_full_vec slot.secret /\
          V.length slot.secret == 32 /\
          B.length secret == 32 /\
          optional_fixed_bytes_match present secret 32 spec)

let traffic_key_material_exactly
  ([@@@mkey] slot:traffic_key_material_storage)
  (spec:option CS.traffic_key_material)
  : slprop =
  exists* present secret key iv.
    Box.pts_to slot.present present **
    V.pts_to slot.traffic_secret secret **
    V.pts_to slot.traffic_key key **
    V.pts_to slot.traffic_iv iv **
    pure (V.is_full_vec slot.traffic_secret /\
          V.is_full_vec slot.traffic_key /\
          V.is_full_vec slot.traffic_iv /\
          V.length slot.traffic_secret == 32 /\
          V.length slot.traffic_key == 32 /\
          V.length slot.traffic_iv == 12 /\
          B.length secret == 32 /\
          B.length key == 32 /\
          B.length iv == 12 /\
          (if present then
            match spec with
            | Some m ->
              Seq.equal secret m.CS.traffic_secret /\
              Seq.equal key m.CS.traffic_key /\
              Seq.equal iv m.CS.traffic_iv
            | None -> False
          else
            spec == None))

let key_schedule_exactly
  ([@@@mkey] keys:key_schedule_storage)
  (spec:CS.key_schedule_state)
  : slprop =
  optional_secret_exactly keys.early_secret spec.CS.ks_early_secret **
  optional_secret_exactly keys.shared_secret spec.CS.ks_shared_secret **
  optional_secret_exactly keys.handshake_secret spec.CS.ks_handshake_secret **
  optional_secret_exactly keys.master_secret spec.CS.ks_master_secret **
  traffic_key_material_exactly keys.client_handshake_traffic spec.CS.ks_client_handshake_traffic **
  traffic_key_material_exactly keys.server_handshake_traffic spec.CS.ks_server_handshake_traffic **
  traffic_key_material_exactly keys.client_application_traffic spec.CS.ks_client_application_traffic **
  traffic_key_material_exactly keys.server_application_traffic spec.CS.ks_server_application_traffic **
  optional_secret_exactly keys.exporter_master_secret spec.CS.ks_exporter_master_secret **
  optional_secret_exactly keys.resumption_master_secret spec.CS.ks_resumption_master_secret

let handshake_start_fields_allocated
  ([@@@mkey] start:handshake_start_storage)
  : slprop =
  sized_bytes_allocated start.server_name max_hostname_len **
  fixed_bytes_allocated start.client_random 32 **
  optional_fixed_bytes_exactly start.client_key_share_private 32 None **
  fixed_bytes_allocated start.client_key_share_public 32 **
  cipher_suite_list_allocated start.cipher_suites max_cipher_suites **
  signature_scheme_list_allocated start.signature_schemes max_signature_schemes

let handshake_start_fields_exactly
  ([@@@mkey] start:handshake_start_storage)
  (spec:CS.handshake_start)
  : slprop =
  sized_bytes_exactly start.server_name max_hostname_len spec.CS.start_server_name **
  fixed_bytes_exactly start.client_random 32 spec.CS.start_client_random **
  optional_fixed_bytes_exactly start.client_key_share_private 32 spec.CS.start_client_key_share_private **
  fixed_bytes_exactly start.client_key_share_public 32 spec.CS.start_client_key_share_public **
  cipher_suite_list_exactly start.cipher_suites max_cipher_suites spec.CS.start_cipher_suites **
  signature_scheme_list_exactly start.signature_schemes max_signature_schemes spec.CS.start_signature_schemes

let handshake_start_exactly
  ([@@@mkey] start:handshake_start_storage)
  (spec:option CS.handshake_start)
  : slprop =
  exists* present.
    Box.pts_to start.present present **
    (if present then
       match spec with
       | Some s -> handshake_start_fields_exactly start s
       | None -> handshake_start_fields_allocated start ** pure False
     else
       handshake_start_fields_allocated start ** pure (spec == None))

let client_hello_slot_exactly
  (present_box:box bool)
  ([@@@mkey] l:IM.client_hello)
  (spec:option M.client_hello)
  : slprop =
  exists* present random server_name key_share cipher_suites signature_schemes.
    Box.pts_to present_box present **
    V.pts_to l.IM.client_hello_random random **
    V.pts_to l.IM.client_hello_server_name server_name **
    V.pts_to l.IM.client_hello_key_share key_share **
    V.pts_to l.IM.client_hello_cipher_suites cipher_suites **
    V.pts_to l.IM.client_hello_signature_schemes signature_schemes **
    pure (V.is_full_vec l.IM.client_hello_random /\
          V.is_full_vec l.IM.client_hello_server_name /\
          V.is_full_vec l.IM.client_hello_key_share /\
          V.is_full_vec l.IM.client_hello_cipher_suites /\
          V.is_full_vec l.IM.client_hello_signature_schemes /\
          V.length l.IM.client_hello_random == 32 /\
          V.length l.IM.client_hello_server_name == max_hostname_len /\
          V.length l.IM.client_hello_key_share == 32 /\
          V.length l.IM.client_hello_cipher_suites == max_cipher_suites /\
          V.length l.IM.client_hello_signature_schemes == max_signature_schemes /\
          B.length random == 32 /\
          B.length server_name == max_hostname_len /\
          B.length key_share == 32 /\
          Seq.length cipher_suites == max_cipher_suites /\
          Seq.length signature_schemes == max_signature_schemes /\
          (if present then
            match spec with
            | Some m ->
              Seq.equal random m.M.random /\
              IM.optional_byte_prefix_matches
                l.IM.client_hello_has_server_name
                server_name
                l.IM.client_hello_server_name_len
                m.M.server_name /\
              Seq.equal key_share m.M.key_share /\
              IM.cipher_suites_match
                cipher_suites
                (SZ.v l.IM.client_hello_cipher_suites_len)
                m.M.cipher_suites /\
              IM.signature_schemes_match
                signature_schemes
                (SZ.v l.IM.client_hello_signature_schemes_len)
                m.M.signature_schemes
            | None -> False
          else
            spec == None))

let server_hello_slot_exactly
  ([@@@mkey] slot:box (option IM.server_hello))
  (spec:option M.server_hello)
  : slprop =
  exists* stored.
    Box.pts_to slot stored **
    (match stored, spec with
     | None, None -> pure True
     | Some l, Some m -> IM.is_valid_server_hello l m
     | _, _ -> pure False)

let encrypted_extensions_slot_exactly
  (present_box:box bool)
  ([@@@mkey] l:IM.encrypted_extensions)
  (spec:option M.encrypted_extensions)
  : slprop =
  exists* present alpn.
    Box.pts_to present_box present **
    V.pts_to l.IM.encrypted_extensions_alpn alpn **
    pure (V.is_full_vec l.IM.encrypted_extensions_alpn /\
          V.length l.IM.encrypted_extensions_alpn == IM.max_alpn_len /\
          B.length alpn == IM.max_alpn_len /\
          (if present then
            match spec with
            | Some m ->
              IM.optional_byte_prefix_matches
                l.IM.encrypted_extensions_has_alpn
                alpn
                l.IM.encrypted_extensions_alpn_len
                m.M.negotiated_alpn
            | None -> False
          else
            spec == None))

let certificate_slot_exactly
  (present_box:box bool)
  ([@@@mkey] l:IM.certificate_msg)
  (spec:option M.certificate_msg)
  : slprop =
  exists* present chain_bytes offsets lens.
    Box.pts_to present_box present **
    V.pts_to l.IM.certificate_msg_chain_bytes chain_bytes **
    V.pts_to l.IM.certificate_msg_cert_offsets offsets **
    V.pts_to l.IM.certificate_msg_cert_lens lens **
    pure (V.is_full_vec l.IM.certificate_msg_chain_bytes /\
          V.is_full_vec l.IM.certificate_msg_cert_offsets /\
          V.is_full_vec l.IM.certificate_msg_cert_lens /\
          V.length l.IM.certificate_msg_chain_bytes == IM.max_certificate_chain_bytes /\
          V.length l.IM.certificate_msg_cert_offsets == IM.max_certificate_chain_entries /\
          V.length l.IM.certificate_msg_cert_lens == IM.max_certificate_chain_entries /\
          B.length chain_bytes == IM.max_certificate_chain_bytes /\
          Seq.length offsets == IM.max_certificate_chain_entries /\
          Seq.length lens == IM.max_certificate_chain_entries /\
          (if present then
            match spec with
            | Some m ->
              IM.certificate_chain_matches
                chain_bytes
                (SZ.v l.IM.certificate_msg_chain_bytes_len)
                offsets
                lens
                (SZ.v l.IM.certificate_msg_cert_count)
                m.M.chain
            | None -> False
          else
            spec == None))

let certificate_verify_slot_exactly
  (present_box:box bool)
  ([@@@mkey] l:IM.certificate_verify)
  (spec:option M.certificate_verify)
  : slprop =
  exists* present signature.
    Box.pts_to present_box present **
    V.pts_to l.IM.certificate_verify_signature signature **
    pure (V.is_full_vec l.IM.certificate_verify_signature /\
          V.length l.IM.certificate_verify_signature == IM.max_signature_len /\
          B.length signature == IM.max_signature_len /\
          (if present then
            match spec with
            | Some m ->
              IM.byte_prefix_matches
                signature
                l.IM.certificate_verify_signature_len
                m.M.signature /\
              IM.signature_scheme_matches l.IM.certificate_verify_scheme m.M.scheme
            | None -> False
          else
            spec == None))

let finished_slot_exactly
  (present_box:box bool)
  ([@@@mkey] l:IM.finished)
  (spec:option M.finished)
  : slprop =
  exists* present verify_data.
    Box.pts_to present_box present **
    V.pts_to l.IM.finished_verify_data verify_data **
    pure (V.is_full_vec l.IM.finished_verify_data /\
          V.length l.IM.finished_verify_data == 32 /\
          B.length verify_data == 32 /\
          (if present then
            match spec with
            | Some m -> Seq.equal verify_data m.M.verify_data
            | None -> False
          else
            spec == None))

let handshake_messages_exactly
  ([@@@mkey] msgs:handshake_message_storage)
  (hs:CS.handshake_state)
  : slprop =
  client_hello_slot_exactly msgs.client_hello_present msgs.client_hello hs.CS.hs_client_hello **
  server_hello_slot_exactly msgs.server_hello hs.CS.hs_server_hello **
  encrypted_extensions_slot_exactly
    msgs.encrypted_extensions_present
    msgs.encrypted_extensions
    hs.CS.hs_encrypted_extensions **
  certificate_slot_exactly msgs.certificate_present msgs.certificate hs.CS.hs_certificate **
  certificate_verify_slot_exactly
    msgs.certificate_verify_present
    msgs.certificate_verify
    hs.CS.hs_certificate_verify **
  finished_slot_exactly msgs.server_finished_present msgs.server_finished hs.CS.hs_server_finished **
  finished_slot_exactly msgs.client_finished_present msgs.client_finished hs.CS.hs_client_finished

let peer_fields_allocated
  ([@@@mkey] peer:peer_storage)
  : slprop =
  sized_bytes_allocated peer.validated_hostname max_hostname_len **
  sized_bytes_allocated peer.leaf_public_key max_public_key_len **
  signature_scheme_list_allocated peer.permitted_signature_schemes max_signature_schemes

let peer_fields_exactly
  ([@@@mkey] peer:peer_storage)
  (spec:X.peer_identity)
  : slprop =
  sized_bytes_exactly peer.validated_hostname max_hostname_len spec.X.validated_hostname **
  sized_bytes_exactly peer.leaf_public_key max_public_key_len spec.X.leaf_public_key **
  signature_scheme_list_exactly
    peer.permitted_signature_schemes
    max_signature_schemes
    spec.X.permitted_signature_schemes

let peer_exactly
  ([@@@mkey] peer:peer_storage)
  (spec:option X.peer_identity)
  : slprop =
  exists* present.
    Box.pts_to peer.present present **
    (if present then
       match spec with
       | Some p -> peer_fields_exactly peer p
       | None -> peer_fields_allocated peer ** pure False
     else
       peer_fields_allocated peer ** pure (spec == None))

let handshake_buffers_exactly
  ([@@@mkey] buffers:handshake_buffer_storage)
  (spec:CS.handshake_buffer_state)
  : slprop =
  exists* parsed.
    sized_bytes_exactly
      buffers.client_hello_bytes
      max_client_hello_len
      spec.CS.hb_client_hello_bytes **
    sized_bytes_exactly
      buffers.server_hello_bytes
      max_server_hello_len
      spec.CS.hb_server_hello_bytes **
    sized_bytes_exactly
      buffers.encrypted_server_handshake_bytes
      max_handshake_flight_len
      spec.CS.hb_encrypted_server_handshake_bytes **
    Box.pts_to buffers.encrypted_server_handshake_parsed parsed **
    optional_sized_bytes_exactly
      buffers.certificate_leaf_der
      max_handshake_flight_len
      spec.CS.hb_certificate_leaf_der **
    optional_sized_bytes_exactly
      buffers.certificate_verify_input
      max_certificate_verify_input_len
      spec.CS.hb_certificate_verify_input **
    pure (SZ.v parsed == spec.CS.hb_encrypted_server_handshake_parsed)

let handshake_exactly
  ([@@@mkey] handshake:handshake_storage)
  (hs:CS.handshake_state)
  : slprop =
  exists* cv_verified server_finished_verified.
    handshake_start_exactly handshake.start hs.CS.hs_start **
    handshake_messages_exactly handshake.messages hs **
    peer_exactly handshake.validated_peer hs.CS.hs_validated_peer **
    Box.pts_to handshake.certificate_verify_verified cv_verified **
    Box.pts_to handshake.server_finished_verified server_finished_verified **
    sized_bytes_exactly handshake.transcript max_transcript_len hs.CS.hs_transcript **
    handshake_buffers_exactly handshake.buffers hs.CS.hs_buffers **
    key_schedule_exactly handshake.keys hs.CS.hs_keys **
    pure (cv_verified == hs.CS.hs_certificate_verify_verified /\
          server_finished_verified == hs.CS.hs_server_finished_verified)

let record_layer_exactly
  ([@@@mkey] records:record_storage)
  (spec:CS.record_layer_state)
  : slprop =
  Rec.is_record_state records.read spec.CS.record_read **
  Rec.is_record_state records.write spec.CS.record_write

let application_exactly
  ([@@@mkey] app:application_storage)
  (spec:CS.application_state)
  : slprop =
  exists* source_offset.
    sized_bytes_exactly
      app.pending_plaintext
      max_pending_plaintext_len
      spec.CS.app_pending_plaintext **
    sized_bytes_exactly
      app.pending_source_record
      max_pending_plaintext_len
      spec.CS.app_pending_source_record **
    Box.pts_to app.pending_source_offset source_offset **
    sized_bytes_exactly
      app.pending_received_raw
      max_pending_raw_len
      spec.CS.app_pending_received_raw **
    pure (SZ.v source_offset == spec.CS.app_pending_source_offset /\
          CS.pending_application_consistent spec)

let connection_model_exactly
  ([@@@mkey] c:connection_state)
  (model:CS.connection_model)
  : slprop =
  connection_config_exactly c.config model.CS.model_config **
  control_exactly c.control model.CS.model_control model.CS.model_failure **
  record_layer_exactly c.records model.CS.model_record **
  handshake_exactly c.handshake model.CS.model_handshake **
  application_exactly c.application model.CS.model_application

[@@pulse_unfold]
let connection_exactly
  ([@@@mkey] c:connection_state)
  (st:CS.connection_state)
  : slprop =
  MR.pts_to c.ghost_state #1.0R st **
  connection_model_exactly c st.CS.cs_model **
  pure (CS.connection_state_consistent st)

let is_connection_state (c:connection_state) : slprop =
  exists* st. connection_exactly c st

let tls_decode_error : T.tls_error = T.AlertError T.DecodeError

let tls_unexpected_message_error : T.tls_error = T.AlertError T.UnexpectedMessage

let tls_hello_retry_request_rejected_error : T.tls_error = T.HelloRetryRequestRejected

let local_fail_state (st:CS.connection_state) (err:T.tls_error) : CS.connection_state =
  {
    CS.cs_model = CS.fail_model st.CS.cs_model err;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log = st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalFail err)];
  }

let received_hello_retry_request_rejected_state
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : CS.connection_state =
  {
    CS.cs_model = CS.fail_model st.CS.cs_model tls_hello_retry_request_rejected_error;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake M.HelloRetryRequest;
      }];
  }

let received_change_cipher_spec_state
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : CS.connection_state =
  {
    CS.cs_model = st.CS.cs_model;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsChangeCipherSpec;
      }];
  }

let received_alert_failure_state
  (st:CS.connection_state)
  (alert:T.alert_description)
  (raw_received:B.bytes)
  : CS.connection_state =
  {
    CS.cs_model = CS.fail_model st.CS.cs_model (T.AlertError alert);
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsAlert alert;
      }];
  }

let received_close_notify_state
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let record0 = model0.CS.model_record in
  let model1 = {
    model0 with
      CS.model_control = CS.ControlClosed;
      CS.model_record = {
        record0 with
          CS.record_read = R.next_seq record0.CS.record_read;
      };
  } in
  {
    CS.cs_model = model1;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsAlert T.CloseNotify;
      }];
  }

let received_application_data_state
  (st:CS.connection_state)
  (bytes:B.bytes)
  (raw_received:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let record0 = model0.CS.model_record in
  let app0 = model0.CS.model_application in
  let model1 = {
    model0 with
      CS.model_record = {
        record0 with
          CS.record_read = R.next_seq record0.CS.record_read;
      };
      CS.model_application = {
        app0 with
          CS.app_log = CL.append_app_received app0.CS.app_log bytes;
      };
  } in
  {
    CS.cs_model = model1;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsApplicationData bytes;
      }];
  }

let lemma_local_fail_state_evolves (st:CS.connection_state) (err:T.tls_error)
  : Lemma
      (requires CS.connection_state_consistent st)
      (ensures CS.connection_state_evolves st (local_fail_state st err) /\
               CS.connection_state_consistent (local_fail_state st err) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event = CS.ConnLocalEvent (CS.LocalFail err);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (local_fail_state st err))
=
  let delta = {
    CS.delta_event = CS.ConnLocalEvent (CS.LocalFail err);
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_connection_delta st delta (local_fail_state st err));
  assert (CS.connection_state_single_step st (local_fail_state st err));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (local_fail_state st err);
  assert (CS.connection_state_evolves st (local_fail_state st err));
  assert (CS.connection_state_consistent (local_fail_state st err))

let lemma_received_hello_retry_request_rejected_state_evolves
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsClientHelloSent /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake M.HelloRetryRequest;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_hello_retry_request_rejected_state st raw_received) /\
               CS.connection_state_consistent
                 (received_hello_retry_request_rejected_state st raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake M.HelloRetryRequest;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_hello_retry_request_rejected_state st raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake M.HelloRetryRequest;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (CS.fail_model st.CS.cs_model tls_hello_retry_request_rejected_error));
  assert (CS.legal_connection_delta
    st
    delta
    (received_hello_retry_request_rejected_state st raw_received));
  assert (CS.connection_state_single_step
    st
    (received_hello_retry_request_rejected_state st raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_hello_retry_request_rejected_state st raw_received);
  assert (CS.connection_state_evolves
    st
    (received_hello_retry_request_rejected_state st raw_received));
  assert (CS.connection_state_consistent
    (received_hello_retry_request_rejected_state st raw_received))

let lemma_received_change_cipher_spec_state_evolves
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                (exists stage.
                  st.CS.cs_model.CS.model_control == CS.ControlHandshaking stage) /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsChangeCipherSpec;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_change_cipher_spec_state st raw_received) /\
               CS.connection_state_consistent
                 (received_change_cipher_spec_state st raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsChangeCipherSpec;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_change_cipher_spec_state st raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsChangeCipherSpec;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev == Some st.CS.cs_model);
  assert (CS.legal_connection_delta st delta (received_change_cipher_spec_state st raw_received));
  assert (CS.connection_state_single_step st (received_change_cipher_spec_state st raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_change_cipher_spec_state st raw_received);
  assert (CS.connection_state_evolves st (received_change_cipher_spec_state st raw_received));
  assert (CS.connection_state_consistent (received_change_cipher_spec_state st raw_received))

let lemma_received_alert_failure_state_evolves
  (st:CS.connection_state)
  (alert:T.alert_description)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                alert <> T.CloseNotify /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsAlert alert;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_alert_failure_state st alert raw_received) /\
               CS.connection_state_consistent
                 (received_alert_failure_state st alert raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsAlert alert;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_alert_failure_state st alert raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsAlert alert;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (CS.fail_model st.CS.cs_model (T.AlertError alert)));
  assert (CS.legal_connection_delta st delta (received_alert_failure_state st alert raw_received));
  assert (CS.connection_state_single_step st (received_alert_failure_state st alert raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_alert_failure_state st alert raw_received);
  assert (CS.connection_state_evolves st (received_alert_failure_state st alert raw_received));
  assert (CS.connection_state_consistent (received_alert_failure_state st alert raw_received))

let lemma_received_close_notify_state_evolves
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                (st.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
                 st.CS.cs_model.CS.model_control == CS.ControlClosing) /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsAlert T.CloseNotify;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_close_notify_state st raw_received) /\
               CS.connection_state_consistent
                 (received_close_notify_state st raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsAlert T.CloseNotify;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_close_notify_state st raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsAlert T.CloseNotify;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_close_notify_state st raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_close_notify_state st raw_received));
  assert (CS.connection_state_single_step
    st
    (received_close_notify_state st raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_close_notify_state st raw_received);
  assert (CS.connection_state_evolves
    st
    (received_close_notify_state st raw_received));
  assert (CS.connection_state_consistent
    (received_close_notify_state st raw_received))

let lemma_received_application_data_state_evolves
  (st:CS.connection_state)
  (bytes:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsApplicationData bytes;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_application_data_state st bytes raw_received) /\
               CS.connection_state_consistent
                 (received_application_data_state st bytes raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsApplicationData bytes;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_application_data_state st bytes raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsApplicationData bytes;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_application_data_state st bytes raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_application_data_state st bytes raw_received));
  assert (CS.connection_state_single_step
    st
    (received_application_data_state st bytes raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_application_data_state st bytes raw_received);
  assert (CS.connection_state_evolves
    st
    (received_application_data_state st bytes raw_received));
  assert (CS.connection_state_consistent
    (received_application_data_state st bytes raw_received))

fn mark_decode_error
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  ensures connection_exactly c (local_fail_state st0 tls_decode_error)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  c.control.control_tag := 5uy;
  c.control.failure_present := true;
  c.control.failure_code := 0uy;
  c.control.failure_alert := 50uy;

  fold (control_exactly
    c.control
    (CS.ControlFailed tls_decode_error)
    (Some tls_decode_error));
  assert (pure ((CS.fail_model st0.CS.cs_model tls_decode_error).CS.model_control == CS.ControlFailed tls_decode_error));
  assert (pure ((CS.fail_model st0.CS.cs_model tls_decode_error).CS.model_failure == Some tls_decode_error));
  fold (connection_model_exactly c (CS.fail_model st0.CS.cs_model tls_decode_error));

  lemma_local_fail_state_evolves st0 tls_decode_error;
  MR.update c.ghost_state (local_fail_state st0 tls_decode_error);
  fold (connection_exactly c (local_fail_state st0 tls_decode_error))
}

fn mark_unexpected_message
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  ensures connection_exactly c (local_fail_state st0 tls_unexpected_message_error)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  c.control.control_tag := 5uy;
  c.control.failure_present := true;
  c.control.failure_code := 0uy;
  c.control.failure_alert := 10uy;

  fold (control_exactly
    c.control
    (CS.ControlFailed tls_unexpected_message_error)
    (Some tls_unexpected_message_error));
  assert (pure ((CS.fail_model st0.CS.cs_model tls_unexpected_message_error).CS.model_control == CS.ControlFailed tls_unexpected_message_error));
  assert (pure ((CS.fail_model st0.CS.cs_model tls_unexpected_message_error).CS.model_failure == Some tls_unexpected_message_error));
  fold (connection_model_exactly c (CS.fail_model st0.CS.cs_model tls_unexpected_message_error));

  lemma_local_fail_state_evolves st0 tls_unexpected_message_error;
  MR.update c.ghost_state (local_fail_state st0 tls_unexpected_message_error);
  fold (connection_exactly c (local_fail_state st0 tls_unexpected_message_error))
}

fn is_handshaking
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==> (exists stage.
            st0.CS.cs_model.CS.model_control == CS.ControlHandshaking stage))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  let tag = !c.control.control_tag;
  let ok = tag = 1uy;

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> (exists stage.
    st0.CS.cs_model.CS.model_control == CS.ControlHandshaking stage)));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn is_waiting_server_hello
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloSent)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 2uy;
  let ok = tag_ok && stage_ok;

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 2));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloSent));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_receive_application_data
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);

  let tag = !c.control.control_tag;
  let control_ok = tag = 2uy;
  let server_app_present = !c.handshake.keys.server_application_traffic.present;

  fold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  let seq_ok = Rec.can_advance_seq c.records.read;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let ok = control_ok && server_app_present && seq_ok;

  assert (pure (ok ==> U8.v tag == 2));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (ok ==> Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_receive_close_notify
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
             st0.CS.cs_model.CS.model_control == CS.ControlClosing) /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let tag = !c.control.control_tag;
  let app_ok = tag = 2uy;
  let closing_ok = tag = 3uy;
  let control_ok = app_ok || closing_ok;

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);

  let seq_ok = Rec.can_advance_seq c.records.read;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let ok = control_ok && seq_ok;

  assert (pure (app_ok ==> U8.v tag == 2));
  assert (pure (closing_ok ==> U8.v tag == 3));
  assert (pure (ok ==>
    (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
     st0.CS.cs_model.CS.model_control == CS.ControlClosing)));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));

  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn mark_received_change_cipher_spec
  (c:connection_state)
  (raw:array U8.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure ((exists stage.
                    st0.CS.cs_model.CS.model_control == CS.ControlHandshaking stage) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsChangeCipherSpec;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_change_cipher_spec_state st0 (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  unfold (connection_exactly c st0);
  assert (pure ((received_change_cipher_spec_state st0 (Ghost.reveal 'raw_bytes)).CS.cs_model == st0.CS.cs_model));
  lemma_received_change_cipher_spec_state_evolves st0 (Ghost.reveal 'raw_bytes);
  MR.update c.ghost_state (received_change_cipher_spec_state st0 (Ghost.reveal 'raw_bytes));
  fold (connection_exactly c (received_change_cipher_spec_state st0 (Ghost.reveal 'raw_bytes)))
}

fn mark_received_alert_failure
  (c:connection_state)
  (raw:array U8.t)
  (alert_wire:U8.t)
  (alert:T.alert_description)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (alert <> T.CloseNotify /\
                 alert_tag_matches alert_wire alert /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsAlert alert;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_alert_failure_state st0 alert (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  assert (pure (alert <> T.CloseNotify));
  assert (pure (alert_tag_matches alert_wire alert));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsAlert alert;
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  c.control.control_tag := 5uy;
  c.control.failure_present := true;
  c.control.failure_code := 0uy;
  c.control.failure_alert := alert_wire;

  assert (pure (tls_error_code_matches 0uy alert_wire (T.AlertError alert)));
  assert (pure (control_state_matches
    5uy
    0uy
    true
    0uy
    alert_wire
    (CS.ControlFailed (T.AlertError alert))));
  fold (control_exactly
    c.control
    (CS.ControlFailed (T.AlertError alert))
    (Some (T.AlertError alert)));
  assert (pure ((CS.fail_model st0.CS.cs_model (T.AlertError alert)).CS.model_control ==
                CS.ControlFailed (T.AlertError alert)));
  assert (pure ((CS.fail_model st0.CS.cs_model (T.AlertError alert)).CS.model_failure ==
                Some (T.AlertError alert)));
  fold (connection_model_exactly c (CS.fail_model st0.CS.cs_model (T.AlertError alert)));

  lemma_received_alert_failure_state_evolves st0 alert (Ghost.reveal 'raw_bytes);
  MR.update c.ghost_state (received_alert_failure_state st0 alert (Ghost.reveal 'raw_bytes));
  fold (connection_exactly c (received_alert_failure_state st0 alert (Ghost.reveal 'raw_bytes)))
}

fn mark_received_close_notify
  (c:connection_state)
  (raw:array U8.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure ((st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
                  st0.CS.cs_model.CS.model_control == CS.ControlClosing) /\
                 U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsAlert T.CloseNotify;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_close_notify_state st0 (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
                st0.CS.cs_model.CS.model_control == CS.ControlClosing));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsAlert T.CloseNotify;
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  assert (pure (st0.CS.cs_model.CS.model_failure == None));
  c.control.control_tag := 4uy;
  c.control.handshake_stage_tag := 0uy;
  c.control.failure_present := false;
  c.control.failure_code := 0uy;
  c.control.failure_alert := 0uy;

  assert (pure (control_state_matches
    4uy
    0uy
    false
    0uy
    0uy
    CS.ControlClosed));
  fold (control_exactly
    c.control
    CS.ControlClosed
    st0.CS.cs_model.CS.model_failure);

  Rec.advance_seq c.records.read;
  fold (record_layer_exactly
    c.records
    { st0.CS.cs_model.CS.model_record with
        CS.record_read = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_read });

  assert (pure ((received_close_notify_state st0 (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_control ==
                CS.ControlClosed));
  assert (pure ((received_close_notify_state st0 (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_failure ==
                st0.CS.cs_model.CS.model_failure));
  fold (connection_model_exactly
    c
    (received_close_notify_state st0 (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_close_notify_state_evolves st0 (Ghost.reveal 'raw_bytes);
  MR.update c.ghost_state (received_close_notify_state st0 (Ghost.reveal 'raw_bytes));
  fold (connection_exactly c (received_close_notify_state st0 (Ghost.reveal 'raw_bytes)))
}

fn mark_received_hello_retry_request_rejected
  (c:connection_state)
  (raw:array U8.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsClientHelloSent /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake M.HelloRetryRequest;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_hello_retry_request_rejected_state st0 (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloSent));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake M.HelloRetryRequest;
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  c.control.control_tag := 5uy;
  c.control.failure_present := true;
  c.control.failure_code := 4uy;
  c.control.failure_alert := 0uy;

  assert (pure (tls_error_code_matches
    4uy
    0uy
    tls_hello_retry_request_rejected_error));
  assert (pure (control_state_matches
    5uy
    0uy
    true
    4uy
    0uy
    (CS.ControlFailed tls_hello_retry_request_rejected_error)));
  fold (control_exactly
    c.control
    (CS.ControlFailed tls_hello_retry_request_rejected_error)
    (Some tls_hello_retry_request_rejected_error));
  assert (pure ((CS.fail_model st0.CS.cs_model tls_hello_retry_request_rejected_error).CS.model_control ==
                CS.ControlFailed tls_hello_retry_request_rejected_error));
  assert (pure ((CS.fail_model st0.CS.cs_model tls_hello_retry_request_rejected_error).CS.model_failure ==
                Some tls_hello_retry_request_rejected_error));
  fold (connection_model_exactly
    c
    (CS.fail_model st0.CS.cs_model tls_hello_retry_request_rejected_error));

  lemma_received_hello_retry_request_rejected_state_evolves
    st0
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_hello_retry_request_rejected_state st0 (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_hello_retry_request_rejected_state st0 (Ghost.reveal 'raw_bytes)))
}

fn mark_received_application_data
  (c:connection_state)
  (raw:array U8.t)
  (#bytes:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                 Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                 U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsApplicationData bytes;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsApplicationData bytes;
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  Rec.advance_seq c.records.read;
  fold (record_layer_exactly
    c.records
    { st0.CS.cs_model.CS.model_record with
        CS.record_read = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_read });

  unfold (application_exactly c.application st0.CS.cs_model.CS.model_application);
  assert (pure (CS.pending_application_consistent
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application));
  fold (application_exactly
    c.application
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_application);

  assert (pure ((received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_control ==
                st0.CS.cs_model.CS.model_control));
  assert (pure ((received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake ==
                st0.CS.cs_model.CS.model_handshake));
  fold (connection_model_exactly
    c
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_application_data_state_evolves
    st0
    bytes
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)))
}
