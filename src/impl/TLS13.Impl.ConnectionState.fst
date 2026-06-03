module TLS13.Impl.ConnectionState

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box { box, (!), (:=) }
open FStar.List.Tot

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CS = TLS13.Spec.ConnectionState
module H = TLS13.Handshake.Spec
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module KS = TLS13.KeySchedule
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Arr = Pulse.Lib.Array
module ArrPts = Pulse.Lib.Array.PtsTo
module R = TLS13.Record.Spec
module Rec = TLS13.Record
module Ser = TLS13.Impl.Serializer
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.StateMachine
module Slice = Pulse.Lib.Slice
module SZ = FStar.SizeT
module T = TLS13.Types
module Tr = TLS13.Transcript
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec
module X = TLS13.X509.Spec

(**
  Concrete connection-state storage for the rich TLS13.Spec.ConnectionState
  model.  Raw wire/event history is ghost-only in [ghost_state], as in the
  calc sample; the extractable fields store the current mutable connection
  model: config, control state, record states, handshake slots, key schedule,
  and pending application buffers.
**)

let connection_state_preorder : FStar.Preorder.preorder CS.connection_state =
  CS.connection_state_evolves

let state_ref : Type0 = MR.mref connection_state_preorder

let max_hostname_len : nat = 255

// No-argument allocation can only rely on SizeT's guaranteed 16-bit lower bound.
let max_trust_anchors_len : nat = 65535

let max_public_key_len : nat = 4096

let max_cipher_suites : nat = 16

let max_signature_schemes : nat = 16

let max_client_hello_len : nat = 512

let max_server_hello_len : nat = 4096

let max_handshake_flight_len : nat = 32768

let max_transcript_len : nat = 65535

let max_certificate_verify_input_len : nat = 256

let max_pending_plaintext_len : nat = 32768

let max_pending_raw_len : nat = 32768

let option_is_some #a (x:option a) : prop =
  match x with
  | Some _ -> True
  | None -> False

let lemma_option_is_some_some #a (x:option a)
  : Lemma
      (requires option_is_some x)
      (ensures Some? x)
=
  match x with
  | Some _ -> ()
  | None -> ()

let lemma_option_is_some_some_imp #a (x:option a) (b:bool)
  : Lemma
      (requires (b ==> option_is_some x))
      (ensures (b ==> Some? x))
=
  match x with
  | Some _ -> ()
  | None -> ()

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
type client_hello_slot_storage = {
  ch_present: box bool;
  ch_value: IM.client_hello;
}

noeq
type handshake_message_storage = {
  client_hello_present: box bool;
  client_hello: IM.client_hello;
  server_hello: box (option IM.server_hello);
  encrypted_extensions: box (option IM.encrypted_extensions);
  certificate: box (option IM.certificate_msg);
  certificate_verify: box (option IM.certificate_verify);
  server_finished: box (option IM.finished);
  client_finished: box (option IM.finished);
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
  server_key_share: optional_fixed_bytes;
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

let lemma_optional_fixed_bytes_match_some
  (present:bool)
  (storage:B.bytes)
  (n:nat)
  (bytes:option (b:B.bytes{B.length b == n}))
  : Lemma
      (requires optional_fixed_bytes_match present storage n bytes /\
                present)
      (ensures bytes == Some storage)
=
  match bytes with
  | Some b ->
    assert (fixed_bytes_match storage n b);
    Seq.lemma_eq_intro storage b;
    assert (storage == b)
  | None -> ()

let lemma_optional_fixed_bytes_match_present_of_some
  (present:bool)
  (storage:B.bytes)
  (n:nat)
  (bytes:option (b:B.bytes{B.length b == n}))
  : Lemma
      (requires optional_fixed_bytes_match present storage n bytes /\
                Some? bytes)
      (ensures present /\
               bytes == Some storage)
=
  match bytes with
  | Some b ->
    (match present with
    | true ->
      assert (fixed_bytes_match storage n b);
      Seq.lemma_eq_intro storage b;
      assert (storage == b)
    | false -> ())
  | None -> ()

let lemma_server_key_share_option_some
  (server:option M.server_hello)
  (storage:TLS13.Crypto.Spec.x25519_public)
  : Lemma
      (requires (match server with
                 | Some sh -> Some sh.M.key_share
                 | None -> None) == Some storage)
      (ensures Some? server /\
               server == Some (Some?.v server) /\
               storage == (Some?.v server).M.key_share)
=
  match server with
  | Some sh -> ()
  | None -> ()

let lemma_option_some_v (#a:Type0) (o:option a)
  : Lemma
      (requires Some? o)
      (ensures o == Some (Some?.v o))
=
  match o with
  | Some _ -> ()
  | None -> ()

let lemma_len32_refinement_tautology ()
  : Lemma
      (ensures forall (b:B.bytes). {:pattern (B.length b)}
                 (B.length b == 32) == (B.length b == 32))
=
  ()

let lemma_x25519_shared_option_shape
  (sk:TLS13.Crypto.Spec.x25519_private)
  (pk:TLS13.Crypto.Spec.x25519_public)
  : Lemma
      (ensures (match TLS13.Crypto.Spec.x25519_shared sk pk with
                | Some _ -> true
                | None -> false) \/
               (match TLS13.Crypto.Spec.x25519_shared sk pk with
                | None -> true
                | Some _ -> false))
=
  match TLS13.Crypto.Spec.x25519_shared sk pk with
  | Some _ -> ()
  | None -> ()

let sizet_lte_plain (x:SZ.t) (y:SZ.t) : bool =
  SZ.lte x y

let lemma_sizet_lte_plain (x:SZ.t) (y:SZ.t)
  : Lemma (sizet_lte_plain x y == (SZ.v x <= SZ.v y))
=
  ()

let lemma_certificate_chain_matches_nonempty
  (storage:B.bytes)
  (storage_len:nat)
  (offsets:Seq.seq SZ.t)
  (lens:Seq.seq SZ.t)
  (count:nat)
  (chain:list B.bytes)
  : Lemma
      (requires IM.certificate_chain_matches storage storage_len offsets lens count chain /\
                count > 0)
      (ensures chain <> [])
=
  match chain with
  | [] -> ()
  | _ :: _ -> ()

let lemma_certificate_chain_matches_head
  (storage:B.bytes)
  (storage_len:nat)
  (offsets:Seq.seq SZ.t)
  (lens:Seq.seq SZ.t)
  (count:nat)
  (chain:list B.bytes)
  : Lemma
      (requires IM.certificate_chain_matches storage storage_len offsets lens count chain /\
                count > 0)
      (ensures
        (match chain with
        | leaf :: _ ->
          let offset = SZ.v (Seq.index offsets 0) in
          let cert_len = SZ.v (Seq.index lens 0) in
          offset + cert_len <= storage_len /\
          Seq.equal leaf (Seq.slice storage offset (offset + cert_len))
        | [] -> False))
=
  match chain with
  | [] -> ()
  | _ :: _ -> ()

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

type control_snapshot = {
  snapshot_control_tag: U8.t;
  snapshot_handshake_stage_tag: U8.t;
  snapshot_failure_present: bool;
  snapshot_failure_code: U8.t;
  snapshot_failure_alert: U8.t;
}

noextract
let control_snapshot_matches
  (snapshot:control_snapshot)
  (st:CS.connection_state)
  : prop =
  control_state_matches
    snapshot.snapshot_control_tag
    snapshot.snapshot_handshake_stage_tag
    snapshot.snapshot_failure_present
    snapshot.snapshot_failure_code
    snapshot.snapshot_failure_alert
    st.CS.cs_model.CS.model_control /\
  failure_option_matches
    snapshot.snapshot_failure_present
    snapshot.snapshot_failure_code
    snapshot.snapshot_failure_alert
    st.CS.cs_model.CS.model_failure

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
  exists* present storage len.
    Box.pts_to slot.present present **
    V.pts_to slot.value.bytes storage **
    Box.pts_to slot.value.len len **
    pure (V.is_full_vec slot.value.bytes /\
          V.length slot.value.bytes == cap /\
          B.length storage == cap /\
          SZ.v len <= cap /\
          (if present then
             match bytes with
             | Some b -> byte_prefix_matches storage len b
             | None -> False
           else
             bytes == None))

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

noextract
let normalize_optional_fixed32
  (spec:option (b:B.bytes{B.length b == 32}))
  : option (b:B.bytes{B.length b == 32}) =
  if Some? spec then Some (Some?.v spec) else None

let lemma_normalize_optional_fixed32_some
  (spec:option (b:B.bytes{B.length b == 32}))
  (storage:B.bytes{B.length storage == 32})
  : Lemma
      (requires normalize_optional_fixed32 spec == Some storage)
      (ensures spec == Some storage)
=
  match spec with
  | Some b -> ()
  | None -> ()

let cipher_suite_list_allocated
  ([@@@mkey] slot:u16_list_storage)
  (cap:nat)
  : slprop =
  exists* (items:Seq.seq U16.t) (len:SZ.t).
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
  exists* (items:Seq.seq U16.t) (len:SZ.t).
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
  (spec:option TLS13.Crypto.Spec.secret)
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

let lemma_traffic_key_material_match_present_of_some
  (present:bool)
  (secret:B.bytes)
  (key:B.bytes)
  (iv:B.bytes)
  (spec:option CS.traffic_key_material)
  : Lemma
      (requires (if present then
                 match spec with
                 | Some m ->
                   Seq.equal secret m.CS.traffic_secret /\
                   Seq.equal key m.CS.traffic_key /\
                   Seq.equal iv m.CS.traffic_iv
                 | None -> False
               else
                 spec == None) /\
               Some? spec)
      (ensures present /\
              spec == Some {
                CS.traffic_secret = secret;
                CS.traffic_key = key;
                CS.traffic_iv = iv;
              })
=
  match spec with
  | Some m ->
    Seq.lemma_eq_intro secret m.CS.traffic_secret;
    Seq.lemma_eq_intro key m.CS.traffic_key;
    Seq.lemma_eq_intro iv m.CS.traffic_iv;
    assert (secret == m.CS.traffic_secret);
    assert (key == m.CS.traffic_key);
    assert (iv == m.CS.traffic_iv);
    assert (m == {
      CS.traffic_secret = secret;
      CS.traffic_key = key;
      CS.traffic_iv = iv;
    })
  | None -> ()

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

fn store_optional_secret
  (slot:optional_secret_storage)
  (src:array U8.t)
  (#src_secret:erased TLS13.Crypto.Spec.secret)
  requires (exists* prev. optional_secret_exactly slot prev) **
           ArrPts.pts_to src src_secret
  ensures optional_secret_exactly slot (Some (Ghost.reveal src_secret)) **
          ArrPts.pts_to src src_secret
{
  with prev. unfold (optional_secret_exactly slot prev);
  with old_present old_secret. _;
  ArrPts.pts_to_len src;
  V.pts_to_len slot.secret;
  V.to_array_pts_to slot.secret;
  Arr.memcpy 32sz src (V.vec_to_array slot.secret);
  V.to_vec_pts_to slot.secret;
  slot.present := true;
  with stored. assert (V.pts_to slot.secret stored);
  assert (pure (stored == Ghost.reveal src_secret));
  assert (pure (optional_fixed_bytes_match true stored 32 (Some (Ghost.reveal src_secret))));
  fold (optional_secret_exactly slot (Some (Ghost.reveal src_secret)))
}

fn store_traffic_key_material
  (slot:traffic_key_material_storage)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  requires (exists* prev. traffic_key_material_exactly slot prev) **
           ArrPts.pts_to traffic_secret_src material.CS.traffic_secret **
           ArrPts.pts_to traffic_key_src material.CS.traffic_key **
           ArrPts.pts_to traffic_iv_src material.CS.traffic_iv
  ensures traffic_key_material_exactly slot (Some (Ghost.reveal material)) **
          ArrPts.pts_to traffic_secret_src material.CS.traffic_secret **
          ArrPts.pts_to traffic_key_src material.CS.traffic_key **
          ArrPts.pts_to traffic_iv_src material.CS.traffic_iv
{
  with prev. unfold (traffic_key_material_exactly slot prev);
  with old_present old_secret old_key old_iv. _;
  ArrPts.pts_to_len traffic_secret_src;
  ArrPts.pts_to_len traffic_key_src;
  ArrPts.pts_to_len traffic_iv_src;
  V.pts_to_len slot.traffic_secret;
  V.pts_to_len slot.traffic_key;
  V.pts_to_len slot.traffic_iv;
  V.to_array_pts_to slot.traffic_secret;
  V.to_array_pts_to slot.traffic_key;
  V.to_array_pts_to slot.traffic_iv;
  Arr.memcpy 32sz traffic_secret_src (V.vec_to_array slot.traffic_secret);
  Arr.memcpy 32sz traffic_key_src (V.vec_to_array slot.traffic_key);
  Arr.memcpy 12sz traffic_iv_src (V.vec_to_array slot.traffic_iv);
  V.to_vec_pts_to slot.traffic_secret;
  V.to_vec_pts_to slot.traffic_key;
  V.to_vec_pts_to slot.traffic_iv;
  slot.present := true;
  with stored_secret. assert (V.pts_to slot.traffic_secret stored_secret);
  with stored_key. assert (V.pts_to slot.traffic_key stored_key);
  with stored_iv. assert (V.pts_to slot.traffic_iv stored_iv);
  assert (pure (stored_secret == (Ghost.reveal material).CS.traffic_secret));
  assert (pure (stored_key == (Ghost.reveal material).CS.traffic_key));
  assert (pure (stored_iv == (Ghost.reveal material).CS.traffic_iv));
  fold (traffic_key_material_exactly slot (Some (Ghost.reveal material)))
}

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
  signature_scheme_list_exactly start.signature_schemes max_signature_schemes spec.CS.start_signature_schemes **
  pure (CS.handshake_start_key_share_consistent spec)

let handshake_start_payload_exactly
  ([@@@mkey] start:handshake_start_storage)
  (present:bool)
  (spec:option CS.handshake_start)
  : slprop =
  if present then
    exists* (s:CS.handshake_start).
      handshake_start_fields_exactly start s **
      pure (spec == Some s)
  else
    handshake_start_fields_allocated start ** pure (spec == None)

let handshake_start_exactly
  ([@@@mkey] start:handshake_start_storage)
  (spec:option CS.handshake_start)
  : slprop =
  exists* present.
    Box.pts_to start.present present **
    handshake_start_payload_exactly start present spec

let bounded_u16_sizet (n:nat) : SZ.t =
  if n < 65536 then SZ.uint_to_t n else 0sz

let lemma_bounded_u16_sizet_of_sizet
  (n:nat)
  (z:SZ.t)
  : Lemma
      (requires n == SZ.v z /\ n < 65536)
      (ensures bounded_u16_sizet n == z)
=
  SZ.size_v_inj z

let rec lemma_cipher_suites_match_length
  (wire:Seq.seq U16.t)
  (len:nat)
  (suites:list T.cipher_suite)
  : Lemma
      (requires IM.cipher_suites_match wire len suites)
      (ensures len == length suites)
      (decreases len)
=
  if len == 0 then
    ()
  else if len <= Seq.length wire then
    match suites with
    | suite :: rest ->
      lemma_cipher_suites_match_length
        (Seq.slice wire 1 (Seq.length wire))
        (len - 1)
        rest
    | [] -> ()
  else
    ()

let rec lemma_signature_schemes_match_length
  (wire:Seq.seq U16.t)
  (len:nat)
  (schemes:list T.signature_scheme)
  : Lemma
      (requires IM.signature_schemes_match wire len schemes)
      (ensures len == length schemes)
      (decreases len)
=
  if len == 0 then
    ()
  else if len <= Seq.length wire then
    match schemes with
    | scheme :: rest ->
      lemma_signature_schemes_match_length
        (Seq.slice wire 1 (Seq.length wire))
        (len - 1)
        rest
    | [] -> ()
  else
    ()

let client_hello_server_name_len_for (m:M.client_hello) : SZ.t =
  match m.M.server_name with
  | Some sn -> bounded_u16_sizet (B.length sn)
  | None -> 0sz

let client_hello_cipher_suites_len_for (m:M.client_hello) : SZ.t =
  bounded_u16_sizet (length m.M.cipher_suites)

let client_hello_signature_schemes_len_for (m:M.client_hello) : SZ.t =
  bounded_u16_sizet (length m.M.signature_schemes)

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
                true
                server_name
                (client_hello_server_name_len_for m)
                m.M.server_name /\
              Seq.equal key_share m.M.key_share /\
              IM.cipher_suites_match
                cipher_suites
                (SZ.v (client_hello_cipher_suites_len_for m))
                m.M.cipher_suites /\
              IM.signature_schemes_match
                signature_schemes
                (SZ.v (client_hello_signature_schemes_len_for m))
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
     | _, _ -> pure False) **
    pure ((match stored with | None -> true | Some _ -> false) ==
          (match spec with | None -> true | Some _ -> false))

let encrypted_extensions_slot_exactly
  ([@@@mkey] slot:box (option IM.encrypted_extensions))
  (spec:option M.encrypted_extensions)
  : slprop =
  exists* stored.
    Box.pts_to slot stored **
    (match stored, spec with
     | None, None -> pure True
     | Some l, Some m -> IM.is_valid_encrypted_extensions l m
     | _, _ -> pure False) **
    pure ((match stored with | None -> true | Some _ -> false) ==
          (match spec with | None -> true | Some _ -> false))

let certificate_slot_exactly
  ([@@@mkey] slot:box (option IM.certificate_msg))
  (spec:option M.certificate_msg)
  : slprop =
  exists* stored.
    Box.pts_to slot stored **
    (match stored, spec with
     | None, None -> pure True
     | Some l, Some m -> IM.is_valid_certificate_msg l m
     | _, _ -> pure False) **
    pure ((match stored with | None -> true | Some _ -> false) ==
          (match spec with | None -> true | Some _ -> false))

let certificate_verify_slot_exactly
  ([@@@mkey] slot:box (option IM.certificate_verify))
  (spec:option M.certificate_verify)
  : slprop =
  exists* stored.
    Box.pts_to slot stored **
    (match stored, spec with
     | None, None -> pure True
     | Some l, Some m -> IM.is_valid_certificate_verify l m
     | _, _ -> pure False) **
    pure ((match stored with | None -> true | Some _ -> false) ==
          (match spec with | None -> true | Some _ -> false))

let finished_slot_exactly
  ([@@@mkey] slot:box (option IM.finished))
  (spec:option M.finished)
  : slprop =
  exists* stored.
    Box.pts_to slot stored **
    (match stored, spec with
     | None, None -> pure True
     | Some l, Some m -> IM.is_valid_finished l m
     | _, _ -> pure False) **
    pure ((match stored with | None -> true | Some _ -> false) ==
          (match spec with | None -> true | Some _ -> false))

let handshake_messages_exactly
  ([@@@mkey] msgs:handshake_message_storage)
  (hs:CS.handshake_state)
  : slprop =
  client_hello_slot_exactly msgs.client_hello_present msgs.client_hello hs.CS.hs_client_hello **
  server_hello_slot_exactly msgs.server_hello hs.CS.hs_server_hello **
  encrypted_extensions_slot_exactly msgs.encrypted_extensions hs.CS.hs_encrypted_extensions **
  certificate_slot_exactly msgs.certificate hs.CS.hs_certificate **
  certificate_verify_slot_exactly msgs.certificate_verify hs.CS.hs_certificate_verify **
  finished_slot_exactly msgs.server_finished hs.CS.hs_server_finished **
  finished_slot_exactly msgs.client_finished hs.CS.hs_client_finished

let server_key_share_exactly
  ([@@@mkey] slot:optional_fixed_bytes)
  (hs:CS.handshake_state)
  : slprop =
  optional_fixed_bytes_exactly
    slot
    32
    (match hs.CS.hs_server_hello with
     | Some sh -> Some sh.M.key_share
     | None -> None)

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
  exists* present hostname hostname_len public_key public_key_len schemes schemes_len.
    Box.pts_to peer.present present **
    V.pts_to peer.validated_hostname.bytes hostname **
    Box.pts_to peer.validated_hostname.len hostname_len **
    V.pts_to peer.leaf_public_key.bytes public_key **
    Box.pts_to peer.leaf_public_key.len public_key_len **
    V.pts_to peer.permitted_signature_schemes.items schemes **
    Box.pts_to peer.permitted_signature_schemes.len schemes_len **
    pure (V.is_full_vec peer.validated_hostname.bytes /\
          V.length peer.validated_hostname.bytes == max_hostname_len /\
          B.length hostname == max_hostname_len /\
          SZ.v hostname_len <= max_hostname_len /\
          V.is_full_vec peer.leaf_public_key.bytes /\
          V.length peer.leaf_public_key.bytes == max_public_key_len /\
          B.length public_key == max_public_key_len /\
          SZ.v public_key_len <= max_public_key_len /\
          V.is_full_vec peer.permitted_signature_schemes.items /\
          V.length peer.permitted_signature_schemes.items == max_signature_schemes /\
          Seq.length schemes == max_signature_schemes /\
          SZ.v schemes_len <= max_signature_schemes /\
          (if present then
             match spec with
             | Some p ->
               byte_prefix_matches hostname hostname_len p.X.validated_hostname /\
               byte_prefix_matches public_key public_key_len p.X.leaf_public_key /\
               IM.signature_schemes_match
                 schemes
                 (SZ.v schemes_len)
                 p.X.permitted_signature_schemes
             | None -> False
           else
             spec == None))

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
    server_key_share_exactly handshake.server_key_share hs **
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

noextract
let default_connection_config : CS.connection_config = {
  CS.config_role = CS.ClientEndpoint;
  CS.config_server_name = B.empty;
  CS.config_trust_store = { X.anchors = B.empty };
  CS.config_validation_time = { X.seconds_since_epoch = 0 };
  CS.config_cipher_suites = [T.TLS_CHACHA20_POLY1305_SHA256];
  CS.config_signature_schemes = [T.RsaPssRsaeSha256];
}

noextract
let default_initial_state : CS.connection_state =
  CS.initial default_connection_config

noextract
let configured_connection_config
  (server_name:B.bytes)
  (trust_anchors:B.bytes)
  (validation_time_seconds:SZ.t)
  : CS.connection_config =
  {
    CS.config_role = CS.ClientEndpoint;
    CS.config_server_name = server_name;
    CS.config_trust_store = { X.anchors = trust_anchors };
    CS.config_validation_time = { X.seconds_since_epoch = SZ.v validation_time_seconds };
    CS.config_cipher_suites = default_connection_config.CS.config_cipher_suites;
    CS.config_signature_schemes = default_connection_config.CS.config_signature_schemes;
  }

noextract
let configured_initial_state
  (server_name:B.bytes)
  (trust_anchors:B.bytes)
  (validation_time_seconds:SZ.t)
  : CS.connection_state =
  CS.initial (configured_connection_config server_name trust_anchors validation_time_seconds)

let lemma_default_initial_consistent ()
  : Lemma (CS.connection_state_consistent default_initial_state)
=
  ()

let lemma_configured_initial_consistent
  (server_name:B.bytes)
  (trust_anchors:B.bytes)
  (validation_time_seconds:SZ.t)
  : Lemma
      (CS.connection_state_consistent
        (configured_initial_state server_name trust_anchors validation_time_seconds))
=
  ()

fn alloc_empty_sized_bytes (#cap:nat)
  requires pure (SZ.fits cap)
  returns slot:sized_bytes
  ensures sized_bytes_exactly slot cap B.empty
{
  let cap_sz = SZ.uint_to_t cap;
  let bytes = V.alloc 0uy cap_sz;
  let len = Box.alloc 0sz;
  let slot = { bytes; len };
  assert (pure (SZ.v cap_sz == cap));
  rewrite (V.pts_to bytes (Seq.create cap 0uy)) as
    (V.pts_to slot.bytes (Seq.create cap 0uy));
  rewrite (Box.pts_to len 0sz) as (Box.pts_to slot.len 0sz);
  assert (pure (B.length (Seq.create cap 0uy) == cap));
  Seq.lemma_len_slice (Seq.create cap 0uy) 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice (Seq.create cap 0uy) 0 0);
  assert (pure (byte_prefix_matches (Seq.create cap 0uy) (SZ.uint_to_t 0) B.empty));
  fold (sized_bytes_exactly slot cap B.empty);
  slot
}

fn copy_array_to_sized_bytes
  (#cap:nat)
  (src:array U8.t)
  (dst:sized_bytes)
  (src_len:SZ.t)
  requires ArrPts.pts_to src 'src_bytes **
           sized_bytes_allocated dst cap **
           pure (SZ.fits cap /\
                 B.length 'src_bytes == SZ.v src_len /\
                 SZ.v src_len <= cap)
  ensures ArrPts.pts_to src 'src_bytes **
          sized_bytes_exactly dst cap (Ghost.reveal 'src_bytes)
{
  unfold (sized_bytes_allocated dst cap);
  with dst_storage dst_len. _;

  ArrPts.pts_to_len src;
  V.to_array_pts_to dst.bytes;

  let dst_cap = SZ.uint_to_t cap;
  let src_slice = Slice.from_array src src_len;
  let dst_slice = Slice.from_array (V.vec_to_array dst.bytes) dst_cap;

  let dst_split = Slice.split dst_slice src_len;

  Slice.pts_to_len src_slice;
  Slice.pts_to_len (fst dst_split);
  assert (pure (Slice.len src_slice == src_len));
  assert (pure (Slice.len (fst dst_split) == src_len));
  Slice.copy (fst dst_split) src_slice;

  Slice.to_array src_slice;

  Slice.join (fst dst_split) (snd dst_split) dst_slice;
  Slice.to_array dst_slice;
  V.to_vec_pts_to dst.bytes;
  dst.len := src_len;

  with copied_dst_storage. assert (V.pts_to dst.bytes copied_dst_storage);
  Seq.lemma_len_slice copied_dst_storage 0 (SZ.v src_len);
  assert (pure (Seq.equal
    (Seq.slice copied_dst_storage 0 (SZ.v src_len))
    (Ghost.reveal 'src_bytes)));
  fold (sized_bytes_exactly dst cap (Ghost.reveal 'src_bytes))
}

fn alloc_empty_optional_sized_bytes (#cap:nat)
  requires pure (SZ.fits cap)
  returns slot:optional_sized_bytes
  ensures optional_sized_bytes_exactly slot cap None
{
  let cap_sz = SZ.uint_to_t cap;
  let present = Box.alloc false;
  let bytes = V.alloc 0uy cap_sz;
  let len = Box.alloc 0sz;
  let value = { bytes; len };
  let slot = { present; value };
  assert (pure (SZ.v cap_sz == cap));
  rewrite (Box.pts_to present false) as (Box.pts_to slot.present false);
  rewrite (V.pts_to bytes (Seq.create cap 0uy)) as
    (V.pts_to slot.value.bytes (Seq.create cap 0uy));
  rewrite (Box.pts_to len 0sz) as (Box.pts_to slot.value.len 0sz);
  assert (pure (B.length (Seq.create cap 0uy) == cap));
  fold (optional_sized_bytes_exactly slot cap None);
  slot
}

fn copy_optional_sized_bytes_to_array
  (#cap:nat)
  (slot:optional_sized_bytes)
  (dst:array U8.t)
  (dst_len:SZ.t)
  (#bytes_opt:erased (option B.bytes))
  requires optional_sized_bytes_exactly slot cap bytes_opt **
           ArrPts.pts_to dst 'old_dst **
           pure (B.length 'old_dst == SZ.v dst_len /\
                 cap <= SZ.v dst_len /\
                 Some? (Ghost.reveal bytes_opt))
  returns copied_len:SZ.t
  ensures exists* dst_bytes.
          optional_sized_bytes_exactly slot cap bytes_opt **
          ArrPts.pts_to dst dst_bytes **
          pure (B.length dst_bytes == SZ.v dst_len /\
                SZ.v copied_len <= B.length dst_bytes /\
                (match Ghost.reveal bytes_opt with
                | Some bytes ->
                  SZ.v copied_len == B.length bytes /\
                  Seq.equal (Seq.slice dst_bytes 0 (SZ.v copied_len)) bytes
                | None -> False))
{
  unfold (optional_sized_bytes_exactly slot cap (Ghost.reveal bytes_opt));
  with present storage len. _;

  let copy_len = !slot.value.len;
  assert (pure (copy_len == len));
  assert (pure (present));
  assert (pure (
    match Ghost.reveal bytes_opt with
    | Some bytes -> byte_prefix_matches storage copy_len bytes
    | None -> False));
  assert (pure (SZ.v copy_len <= cap));
  assert (pure (SZ.v copy_len <= SZ.v dst_len));

  ArrPts.pts_to_len dst;
  V.to_array_pts_to slot.value.bytes;
  Arr.memcpy_l copy_len (V.vec_to_array slot.value.bytes) dst;
  V.to_vec_pts_to slot.value.bytes;

  with dst_bytes. assert (ArrPts.pts_to dst dst_bytes);
  assert (pure (B.length dst_bytes == SZ.v dst_len));
  assert (pure (SZ.v copy_len <= B.length dst_bytes));
  assert (pure (Seq.equal
    (Seq.slice dst_bytes 0 (SZ.v copy_len))
    (Seq.slice storage 0 (SZ.v copy_len))));
  assert (pure (
    match Ghost.reveal bytes_opt with
    | Some bytes ->
      SZ.v copy_len == B.length bytes /\
      Seq.equal (Seq.slice dst_bytes 0 (SZ.v copy_len)) bytes
    | None -> False));

  fold (optional_sized_bytes_exactly slot cap (Ghost.reveal bytes_opt));
  copy_len
}

fn alloc_empty_optional_fixed32 ()
  requires emp
  returns slot:optional_fixed_bytes
  ensures optional_fixed_bytes_exactly slot 32 None
{
  let present = Box.alloc false;
  let bytes = V.alloc 0uy 32sz;
  let slot = { present; bytes };
  rewrite (Box.pts_to present false) as (Box.pts_to slot.present false);
  rewrite (V.pts_to bytes (Seq.create 32 0uy)) as
    (V.pts_to slot.bytes (Seq.create 32 0uy));
  assert (pure (B.length (Seq.create 32 0uy) == 32));
  assert_norm (optional_fixed_bytes_match false (Seq.create 32 0uy) 32 None);
  fold (optional_fixed_bytes_exactly slot 32 None);
  slot
}

fn alloc_empty_secret ()
  requires emp
  returns slot:optional_secret_storage
  ensures optional_secret_exactly slot None
{
  let present = Box.alloc false;
  let secret = V.alloc 0uy 32sz;
  let slot = { present; secret };
  rewrite (Box.pts_to present false) as (Box.pts_to slot.present false);
  rewrite (V.pts_to secret (Seq.create 32 0uy)) as
    (V.pts_to slot.secret (Seq.create 32 0uy));
  assert (pure (B.length (Seq.create 32 0uy) == 32));
  assert_norm (optional_fixed_bytes_match false (Seq.create 32 0uy) 32 None);
  fold (optional_secret_exactly slot None);
  slot
}

fn alloc_empty_traffic_key_material ()
  requires emp
  returns slot:traffic_key_material_storage
  ensures traffic_key_material_exactly slot None
{
  let present = Box.alloc false;
  let traffic_secret = V.alloc 0uy 32sz;
  let traffic_key = V.alloc 0uy 32sz;
  let traffic_iv = V.alloc 0uy 12sz;
  let slot = { present; traffic_secret; traffic_key; traffic_iv };
  rewrite (Box.pts_to present false) as (Box.pts_to slot.present false);
  rewrite (V.pts_to traffic_secret (Seq.create 32 0uy)) as
    (V.pts_to slot.traffic_secret (Seq.create 32 0uy));
  rewrite (V.pts_to traffic_key (Seq.create 32 0uy)) as
    (V.pts_to slot.traffic_key (Seq.create 32 0uy));
  rewrite (V.pts_to traffic_iv (Seq.create 12 0uy)) as
    (V.pts_to slot.traffic_iv (Seq.create 12 0uy));
  assert (pure (B.length (Seq.create 32 0uy) == 32));
  assert (pure (B.length (Seq.create 12 0uy) == 12));
  fold (traffic_key_material_exactly slot None);
  slot
}

fn alloc_default_cipher_suites ()
  requires emp
  returns slot:u16_list_storage
  ensures cipher_suite_list_exactly
            slot
            max_cipher_suites
            default_connection_config.CS.config_cipher_suites
{
  let items = V.alloc 0x1303us (SZ.uint_to_t max_cipher_suites);
  let len = Box.alloc 1sz;
  let slot = { items; len };
  rewrite (V.pts_to items (Seq.create max_cipher_suites 0x1303us)) as
    (V.pts_to slot.items (Seq.create max_cipher_suites 0x1303us));
  rewrite (Box.pts_to len 1sz) as (Box.pts_to slot.len 1sz);
  assert (pure (Seq.length (Seq.create max_cipher_suites 0x1303us) == max_cipher_suites));
  Seq.lemma_index_create max_cipher_suites 0x1303us 0;
  assert (pure (Seq.index (Seq.create max_cipher_suites 0x1303us) 0 == 0x1303us));
  assert_norm (IM.cipher_suite_matches 0x1303us T.TLS_CHACHA20_POLY1305_SHA256);
  assert_norm (default_connection_config.CS.config_cipher_suites ==
    [T.TLS_CHACHA20_POLY1305_SHA256]);
  assert (pure (IM.cipher_suites_match
    (Seq.create max_cipher_suites 0x1303us)
    1
    default_connection_config.CS.config_cipher_suites));
  fold (cipher_suite_list_exactly
    slot
    max_cipher_suites
    default_connection_config.CS.config_cipher_suites);
  slot
}

fn alloc_default_signature_schemes ()
  requires emp
  returns slot:u16_list_storage
  ensures signature_scheme_list_exactly
            slot
            max_signature_schemes
            default_connection_config.CS.config_signature_schemes
{
  let items = V.alloc 0x0804us (SZ.uint_to_t max_signature_schemes);
  let len = Box.alloc 1sz;
  let slot = { items; len };
  rewrite (V.pts_to items (Seq.create max_signature_schemes 0x0804us)) as
    (V.pts_to slot.items (Seq.create max_signature_schemes 0x0804us));
  rewrite (Box.pts_to len 1sz) as (Box.pts_to slot.len 1sz);
  assert (pure (Seq.length (Seq.create max_signature_schemes 0x0804us) == max_signature_schemes));
  Seq.lemma_index_create max_signature_schemes 0x0804us 0;
  assert (pure (Seq.index (Seq.create max_signature_schemes 0x0804us) 0 == 0x0804us));
  assert_norm (IM.signature_scheme_matches 0x0804us T.RsaPssRsaeSha256);
  assert_norm (default_connection_config.CS.config_signature_schemes ==
    [T.RsaPssRsaeSha256]);
  assert (pure (IM.signature_schemes_match
    (Seq.create max_signature_schemes 0x0804us)
    1
    default_connection_config.CS.config_signature_schemes));
  fold (signature_scheme_list_exactly
    slot
    max_signature_schemes
    default_connection_config.CS.config_signature_schemes);
  slot
}

fn alloc_default_config_storage ()
  requires emp
  returns cfg:connection_config_storage
  ensures connection_config_exactly cfg default_connection_config
{
  assert (pure (SZ.fits max_hostname_len));
  assert (pure (SZ.fits max_trust_anchors_len));
  let role_tag = Box.alloc 0uy;
  let server_name = alloc_empty_sized_bytes #max_hostname_len;
  let trust_anchors = alloc_empty_sized_bytes #max_trust_anchors_len;
  let validation_time_seconds = Box.alloc 0sz;
  let cipher_suites = alloc_default_cipher_suites ();
  let signature_schemes = alloc_default_signature_schemes ();
  let cfg = {
    role_tag;
    server_name;
    trust_anchors;
    validation_time_seconds;
    cipher_suites;
    signature_schemes;
  };
  rewrite (Box.pts_to role_tag 0uy) as (Box.pts_to cfg.role_tag 0uy);
  rewrite (sized_bytes_exactly server_name max_hostname_len B.empty) as
    (sized_bytes_exactly cfg.server_name max_hostname_len default_connection_config.CS.config_server_name);
  rewrite (sized_bytes_exactly trust_anchors max_trust_anchors_len B.empty) as
    (sized_bytes_exactly cfg.trust_anchors max_trust_anchors_len default_connection_config.CS.config_trust_store.X.anchors);
  rewrite (Box.pts_to validation_time_seconds 0sz) as
    (Box.pts_to cfg.validation_time_seconds 0sz);
  rewrite (cipher_suite_list_exactly
    cipher_suites
    max_cipher_suites
    default_connection_config.CS.config_cipher_suites) as
    (cipher_suite_list_exactly
      cfg.cipher_suites
      max_cipher_suites
      default_connection_config.CS.config_cipher_suites);
  rewrite (signature_scheme_list_exactly
    signature_schemes
    max_signature_schemes
    default_connection_config.CS.config_signature_schemes) as
    (signature_scheme_list_exactly
      cfg.signature_schemes
      max_signature_schemes
      default_connection_config.CS.config_signature_schemes);
  assert_norm (endpoint_role_tag_matches 0uy CS.ClientEndpoint);
  assert (pure (endpoint_role_tag_matches 0uy default_connection_config.CS.config_role));
  assert (pure (SZ.v 0sz ==
    default_connection_config.CS.config_validation_time.X.seconds_since_epoch));
  fold (connection_config_exactly cfg default_connection_config);
  cfg
}

fn alloc_config_storage
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires ArrPts.pts_to server_name 'server_name_bytes **
           ArrPts.pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <= max_hostname_len /\
                 SZ.v trust_anchors_len <= max_trust_anchors_len)
  returns cfg:connection_config_storage
  ensures ArrPts.pts_to server_name 'server_name_bytes **
          ArrPts.pts_to trust_anchors 'trust_anchors_bytes **
          connection_config_exactly
            cfg
            (configured_connection_config
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds)
{
  assert (pure (SZ.fits max_hostname_len));
  assert (pure (SZ.fits max_trust_anchors_len));
  let role_tag = Box.alloc 0uy;
  let server_name_slot = alloc_empty_sized_bytes #max_hostname_len;
  unfold (sized_bytes_exactly server_name_slot max_hostname_len B.empty);
  with empty_server_name_storage empty_server_name_len. _;
  fold (sized_bytes_allocated server_name_slot max_hostname_len);
  copy_array_to_sized_bytes
    #max_hostname_len
    server_name
    server_name_slot
    server_name_len;
  let trust_anchors_slot = alloc_empty_sized_bytes #max_trust_anchors_len;
  unfold (sized_bytes_exactly trust_anchors_slot max_trust_anchors_len B.empty);
  with empty_trust_anchors_storage empty_trust_anchors_len. _;
  fold (sized_bytes_allocated trust_anchors_slot max_trust_anchors_len);
  copy_array_to_sized_bytes
    #max_trust_anchors_len
    trust_anchors
    trust_anchors_slot
    trust_anchors_len;
  let validation_time_seconds_box = Box.alloc validation_time_seconds;
  let cipher_suites = alloc_default_cipher_suites ();
  let signature_schemes = alloc_default_signature_schemes ();
  let cfg = {
    role_tag;
    server_name = server_name_slot;
    trust_anchors = trust_anchors_slot;
    validation_time_seconds = validation_time_seconds_box;
    cipher_suites;
    signature_schemes;
  };
  rewrite (Box.pts_to role_tag 0uy) as (Box.pts_to cfg.role_tag 0uy);
  rewrite (sized_bytes_exactly
    server_name_slot
    max_hostname_len
    (Ghost.reveal 'server_name_bytes)) as
    (sized_bytes_exactly
      cfg.server_name
      max_hostname_len
      (configured_connection_config
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds).CS.config_server_name);
  rewrite (sized_bytes_exactly
    trust_anchors_slot
    max_trust_anchors_len
    (Ghost.reveal 'trust_anchors_bytes)) as
    (sized_bytes_exactly
      cfg.trust_anchors
      max_trust_anchors_len
      (configured_connection_config
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds).CS.config_trust_store.X.anchors);
  rewrite (Box.pts_to validation_time_seconds_box validation_time_seconds) as
    (Box.pts_to cfg.validation_time_seconds validation_time_seconds);
  rewrite (cipher_suite_list_exactly
    cipher_suites
    max_cipher_suites
    default_connection_config.CS.config_cipher_suites) as
    (cipher_suite_list_exactly
      cfg.cipher_suites
      max_cipher_suites
      (configured_connection_config
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds).CS.config_cipher_suites);
  rewrite (signature_scheme_list_exactly
    signature_schemes
    max_signature_schemes
    default_connection_config.CS.config_signature_schemes) as
    (signature_scheme_list_exactly
      cfg.signature_schemes
      max_signature_schemes
      (configured_connection_config
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds).CS.config_signature_schemes);
  assert_norm (endpoint_role_tag_matches 0uy CS.ClientEndpoint);
  assert (pure (endpoint_role_tag_matches
    0uy
    (configured_connection_config
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds).CS.config_role));
  assert (pure (SZ.v validation_time_seconds ==
    (configured_connection_config
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds).CS.config_validation_time.X.seconds_since_epoch));
  fold (connection_config_exactly
    cfg
    (configured_connection_config
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds));
  cfg
}

fn alloc_control_new ()
  requires emp
  returns control:control_storage
  ensures control_exactly control CS.ControlNew None
{
  let control_tag = Box.alloc 0uy;
  let handshake_stage_tag = Box.alloc 0uy;
  let failure_present = Box.alloc false;
  let failure_code = Box.alloc 0uy;
  let failure_alert = Box.alloc 0uy;
  let control = {
    control_tag;
    handshake_stage_tag;
    failure_present;
    failure_code;
    failure_alert;
  };
  rewrite (Box.pts_to control_tag 0uy) as (Box.pts_to control.control_tag 0uy);
  rewrite (Box.pts_to handshake_stage_tag 0uy) as
    (Box.pts_to control.handshake_stage_tag 0uy);
  rewrite (Box.pts_to failure_present false) as
    (Box.pts_to control.failure_present false);
  rewrite (Box.pts_to failure_code 0uy) as (Box.pts_to control.failure_code 0uy);
  rewrite (Box.pts_to failure_alert 0uy) as (Box.pts_to control.failure_alert 0uy);
  assert_norm (control_state_matches 0uy 0uy false 0uy 0uy CS.ControlNew);
  assert_norm (failure_option_matches false 0uy 0uy None);
  fold (control_exactly control CS.ControlNew None);
  control
}

fn alloc_key_schedule_empty ()
  requires emp
  returns keys:key_schedule_storage
  ensures key_schedule_exactly keys CS.empty_key_schedule_state
{
  let early_secret = alloc_empty_secret ();
  let shared_secret = alloc_empty_secret ();
  let handshake_secret = alloc_empty_secret ();
  let master_secret = alloc_empty_secret ();
  let client_handshake_traffic = alloc_empty_traffic_key_material ();
  let server_handshake_traffic = alloc_empty_traffic_key_material ();
  let client_application_traffic = alloc_empty_traffic_key_material ();
  let server_application_traffic = alloc_empty_traffic_key_material ();
  let exporter_master_secret = alloc_empty_secret ();
  let resumption_master_secret = alloc_empty_secret ();
  let keys = {
    early_secret;
    shared_secret;
    handshake_secret;
    master_secret;
    client_handshake_traffic;
    server_handshake_traffic;
    client_application_traffic;
    server_application_traffic;
    exporter_master_secret;
    resumption_master_secret;
  };
  rewrite (optional_secret_exactly early_secret None) as
    (optional_secret_exactly keys.early_secret CS.empty_key_schedule_state.CS.ks_early_secret);
  rewrite (optional_secret_exactly shared_secret None) as
    (optional_secret_exactly keys.shared_secret CS.empty_key_schedule_state.CS.ks_shared_secret);
  rewrite (optional_secret_exactly handshake_secret None) as
    (optional_secret_exactly keys.handshake_secret CS.empty_key_schedule_state.CS.ks_handshake_secret);
  rewrite (optional_secret_exactly master_secret None) as
    (optional_secret_exactly keys.master_secret CS.empty_key_schedule_state.CS.ks_master_secret);
  rewrite (traffic_key_material_exactly client_handshake_traffic None) as
    (traffic_key_material_exactly keys.client_handshake_traffic CS.empty_key_schedule_state.CS.ks_client_handshake_traffic);
  rewrite (traffic_key_material_exactly server_handshake_traffic None) as
    (traffic_key_material_exactly keys.server_handshake_traffic CS.empty_key_schedule_state.CS.ks_server_handshake_traffic);
  rewrite (traffic_key_material_exactly client_application_traffic None) as
    (traffic_key_material_exactly keys.client_application_traffic CS.empty_key_schedule_state.CS.ks_client_application_traffic);
  rewrite (traffic_key_material_exactly server_application_traffic None) as
    (traffic_key_material_exactly keys.server_application_traffic CS.empty_key_schedule_state.CS.ks_server_application_traffic);
  rewrite (optional_secret_exactly exporter_master_secret None) as
    (optional_secret_exactly keys.exporter_master_secret CS.empty_key_schedule_state.CS.ks_exporter_master_secret);
  rewrite (optional_secret_exactly resumption_master_secret None) as
    (optional_secret_exactly keys.resumption_master_secret CS.empty_key_schedule_state.CS.ks_resumption_master_secret);
  fold (key_schedule_exactly keys CS.empty_key_schedule_state);
  keys
}

fn alloc_handshake_start_empty ()
  requires emp
  returns start:handshake_start_storage
  ensures handshake_start_exactly start None
{
  assert (pure (SZ.fits max_hostname_len));
  let present = Box.alloc false;
  let server_name = alloc_empty_sized_bytes #max_hostname_len;
  let client_random = V.alloc 0uy 32sz;
  let client_key_share_private = alloc_empty_optional_fixed32 ();
  let client_key_share_public = V.alloc 0uy 32sz;
  let cipher_suites_items = V.alloc 0us (SZ.uint_to_t max_cipher_suites);
  let cipher_suites_len = Box.alloc 0sz;
  let cipher_suites = { items = cipher_suites_items; len = cipher_suites_len };
  let signature_schemes_items = V.alloc 0us (SZ.uint_to_t max_signature_schemes);
  let signature_schemes_len = Box.alloc 0sz;
  let signature_schemes = { items = signature_schemes_items; len = signature_schemes_len };
  let start = {
    present;
    server_name;
    client_random;
    client_key_share_private;
    client_key_share_public;
    cipher_suites;
    signature_schemes;
  };
  rewrite (Box.pts_to present false) as (Box.pts_to start.present false);
  unfold (sized_bytes_exactly server_name max_hostname_len B.empty);
  with server_name_storage server_name_len. _;
  rewrite (V.pts_to server_name.bytes server_name_storage) as
    (V.pts_to start.server_name.bytes server_name_storage);
  rewrite (Box.pts_to server_name.len server_name_len) as
    (Box.pts_to start.server_name.len server_name_len);
  fold (sized_bytes_allocated start.server_name max_hostname_len);
  rewrite (V.pts_to client_random (Seq.create 32 0uy)) as
    (V.pts_to start.client_random (Seq.create 32 0uy));
  rewrite (optional_fixed_bytes_exactly client_key_share_private 32 None) as
    (optional_fixed_bytes_exactly start.client_key_share_private 32 None);
  rewrite (V.pts_to client_key_share_public (Seq.create 32 0uy)) as
    (V.pts_to start.client_key_share_public (Seq.create 32 0uy));
  rewrite (V.pts_to cipher_suites_items (Seq.create max_cipher_suites 0us)) as
    (V.pts_to start.cipher_suites.items (Seq.create max_cipher_suites 0us));
  rewrite (Box.pts_to cipher_suites_len 0sz) as
    (Box.pts_to start.cipher_suites.len 0sz);
  rewrite (V.pts_to signature_schemes_items (Seq.create max_signature_schemes 0us)) as
    (V.pts_to start.signature_schemes.items (Seq.create max_signature_schemes 0us));
  rewrite (Box.pts_to signature_schemes_len 0sz) as
    (Box.pts_to start.signature_schemes.len 0sz);
  assert (pure (B.length (Seq.create 32 0uy) == 32));
  assert (pure (Seq.length (Seq.create max_cipher_suites 0us) == max_cipher_suites));
  assert (pure (Seq.length (Seq.create max_signature_schemes 0us) == max_signature_schemes));
  fold (fixed_bytes_allocated start.client_random 32);
  fold (fixed_bytes_allocated start.client_key_share_public 32);
  fold (cipher_suite_list_allocated start.cipher_suites max_cipher_suites);
  fold (signature_scheme_list_allocated start.signature_schemes max_signature_schemes);
  fold (handshake_start_fields_allocated start);
  fold (handshake_start_payload_exactly start false None);
  fold (handshake_start_exactly start None);
  start
}

fn alloc_client_hello_slot_empty ()
  requires emp
  returns ch_slot:client_hello_slot_storage
  ensures client_hello_slot_exactly ch_slot.ch_present ch_slot.ch_value None
{
  let present_box = Box.alloc false;
  let client_hello_random = V.alloc 0uy 32sz;
  let client_hello_server_name = V.alloc 0uy (SZ.uint_to_t max_hostname_len);
  let client_hello_key_share = V.alloc 0uy 32sz;
  let client_hello_cipher_suites = V.alloc 0us (SZ.uint_to_t max_cipher_suites);
  let client_hello_signature_schemes = V.alloc 0us (SZ.uint_to_t max_signature_schemes);
  let l = {
    IM.client_hello_random;
    IM.client_hello_server_name;
    IM.client_hello_server_name_len = 0sz;
    IM.client_hello_has_server_name = false;
    IM.client_hello_key_share;
    IM.client_hello_cipher_suites;
    IM.client_hello_cipher_suites_len = 0sz;
    IM.client_hello_signature_schemes;
    IM.client_hello_signature_schemes_len = 0sz;
  };
  rewrite (V.pts_to client_hello_random (Seq.create 32 0uy)) as
    (V.pts_to l.IM.client_hello_random (Seq.create 32 0uy));
  rewrite (V.pts_to client_hello_server_name (Seq.create max_hostname_len 0uy)) as
    (V.pts_to l.IM.client_hello_server_name (Seq.create max_hostname_len 0uy));
  rewrite (V.pts_to client_hello_key_share (Seq.create 32 0uy)) as
    (V.pts_to l.IM.client_hello_key_share (Seq.create 32 0uy));
  rewrite (V.pts_to client_hello_cipher_suites (Seq.create max_cipher_suites 0us)) as
    (V.pts_to l.IM.client_hello_cipher_suites (Seq.create max_cipher_suites 0us));
  rewrite (V.pts_to client_hello_signature_schemes (Seq.create max_signature_schemes 0us)) as
    (V.pts_to l.IM.client_hello_signature_schemes (Seq.create max_signature_schemes 0us));
  assert (pure (B.length (Seq.create 32 0uy) == 32));
  assert (pure (B.length (Seq.create max_hostname_len 0uy) == max_hostname_len));
  assert (pure (Seq.length (Seq.create max_cipher_suites 0us) == max_cipher_suites));
  assert (pure (Seq.length (Seq.create max_signature_schemes 0us) == max_signature_schemes));
  fold (client_hello_slot_exactly present_box l None);
  let ch_slot = { ch_present = present_box; ch_value = l };
  rewrite (client_hello_slot_exactly present_box l None) as
    (client_hello_slot_exactly ch_slot.ch_present ch_slot.ch_value None);
  ch_slot
}

fn alloc_handshake_messages_empty ()
  requires emp
  returns msgs:handshake_message_storage
  ensures handshake_messages_exactly msgs CS.empty_handshake_state
{
  let client_hello_slot : client_hello_slot_storage = alloc_client_hello_slot_empty ();
  let client_hello_present : box bool = client_hello_slot.ch_present;
  let client_hello : IM.client_hello = client_hello_slot.ch_value;
  rewrite (client_hello_slot_exactly client_hello_slot.ch_present client_hello_slot.ch_value None) as
    (client_hello_slot_exactly client_hello_present client_hello None);
  let server_hello : box (option IM.server_hello) = Box.alloc (None #IM.server_hello);
  let encrypted_extensions : box (option IM.encrypted_extensions) =
    Box.alloc (None #IM.encrypted_extensions);
  let certificate : box (option IM.certificate_msg) =
    Box.alloc (None #IM.certificate_msg);
  let certificate_verify : box (option IM.certificate_verify) =
    Box.alloc (None #IM.certificate_verify);
  let server_finished : box (option IM.finished) = Box.alloc (None #IM.finished);
  let client_finished : box (option IM.finished) = Box.alloc (None #IM.finished);
  let msgs = {
    client_hello_present;
    client_hello;
    server_hello;
    encrypted_extensions;
    certificate;
    certificate_verify;
    server_finished;
    client_finished;
  };
  rewrite (client_hello_slot_exactly client_hello_present client_hello None) as
    (client_hello_slot_exactly msgs.client_hello_present msgs.client_hello CS.empty_handshake_state.CS.hs_client_hello);
  rewrite (Box.pts_to server_hello None) as (Box.pts_to msgs.server_hello None);
  rewrite (Box.pts_to encrypted_extensions None) as
    (Box.pts_to msgs.encrypted_extensions None);
  rewrite (Box.pts_to certificate None) as (Box.pts_to msgs.certificate None);
  rewrite (Box.pts_to certificate_verify None) as
    (Box.pts_to msgs.certificate_verify None);
  rewrite (Box.pts_to server_finished None) as (Box.pts_to msgs.server_finished None);
  rewrite (Box.pts_to client_finished None) as (Box.pts_to msgs.client_finished None);
  assert_norm (CS.empty_handshake_state.CS.hs_server_hello == None);
  assert_norm (CS.empty_handshake_state.CS.hs_encrypted_extensions == None);
  assert_norm (CS.empty_handshake_state.CS.hs_certificate == None);
  assert_norm (CS.empty_handshake_state.CS.hs_certificate_verify == None);
  assert_norm (CS.empty_handshake_state.CS.hs_server_finished == None);
  assert_norm (CS.empty_handshake_state.CS.hs_client_finished == None);
  fold (server_hello_slot_exactly msgs.server_hello None);
  rewrite (server_hello_slot_exactly msgs.server_hello None) as
    (server_hello_slot_exactly msgs.server_hello CS.empty_handshake_state.CS.hs_server_hello);
  fold (encrypted_extensions_slot_exactly msgs.encrypted_extensions None);
  rewrite (encrypted_extensions_slot_exactly msgs.encrypted_extensions None) as
    (encrypted_extensions_slot_exactly msgs.encrypted_extensions CS.empty_handshake_state.CS.hs_encrypted_extensions);
  fold (certificate_slot_exactly msgs.certificate None);
  rewrite (certificate_slot_exactly msgs.certificate None) as
    (certificate_slot_exactly msgs.certificate CS.empty_handshake_state.CS.hs_certificate);
  fold (certificate_verify_slot_exactly msgs.certificate_verify None);
  rewrite (certificate_verify_slot_exactly msgs.certificate_verify None) as
    (certificate_verify_slot_exactly msgs.certificate_verify CS.empty_handshake_state.CS.hs_certificate_verify);
  fold (finished_slot_exactly msgs.server_finished None);
  rewrite (finished_slot_exactly msgs.server_finished None) as
    (finished_slot_exactly msgs.server_finished CS.empty_handshake_state.CS.hs_server_finished);
  fold (finished_slot_exactly msgs.client_finished None);
  rewrite (finished_slot_exactly msgs.client_finished None) as
    (finished_slot_exactly msgs.client_finished CS.empty_handshake_state.CS.hs_client_finished);
  fold (handshake_messages_exactly msgs CS.empty_handshake_state);
  msgs
}

fn alloc_peer_empty ()
  requires emp
  returns peer:peer_storage
  ensures peer_exactly peer None
{
  assert (pure (SZ.fits max_hostname_len));
  assert (pure (SZ.fits max_public_key_len));
  let present = Box.alloc false;
  let validated_hostname = alloc_empty_sized_bytes #max_hostname_len;
  let leaf_public_key = alloc_empty_sized_bytes #max_public_key_len;
  let permitted_items = V.alloc 0us (SZ.uint_to_t max_signature_schemes);
  let permitted_len = Box.alloc 0sz;
  let permitted_signature_schemes = { items = permitted_items; len = permitted_len };
  let peer = {
    present;
    validated_hostname;
    leaf_public_key;
    permitted_signature_schemes;
  };
  rewrite (Box.pts_to present false) as (Box.pts_to peer.present false);
  unfold (sized_bytes_exactly validated_hostname max_hostname_len B.empty);
  with hostname hostname_len. _;
  rewrite (V.pts_to validated_hostname.bytes hostname) as
    (V.pts_to peer.validated_hostname.bytes hostname);
  rewrite (Box.pts_to validated_hostname.len hostname_len) as
    (Box.pts_to peer.validated_hostname.len hostname_len);
  unfold (sized_bytes_exactly leaf_public_key max_public_key_len B.empty);
  with public_key public_key_len. _;
  rewrite (V.pts_to leaf_public_key.bytes public_key) as
    (V.pts_to peer.leaf_public_key.bytes public_key);
  rewrite (Box.pts_to leaf_public_key.len public_key_len) as
    (Box.pts_to peer.leaf_public_key.len public_key_len);
  rewrite (V.pts_to permitted_items (Seq.create max_signature_schemes 0us)) as
    (V.pts_to peer.permitted_signature_schemes.items
      (Seq.create max_signature_schemes 0us));
  rewrite (Box.pts_to permitted_len 0sz) as
    (Box.pts_to peer.permitted_signature_schemes.len 0sz);
  assert (pure (Seq.length (Seq.create max_signature_schemes 0us) == max_signature_schemes));
  fold (peer_exactly peer None);
  peer
}

fn alloc_handshake_buffers_empty ()
  requires emp
  returns buffers:handshake_buffer_storage
  ensures handshake_buffers_exactly buffers CS.empty_handshake_buffer_state
{
  assert (pure (SZ.fits max_client_hello_len));
  assert (pure (SZ.fits max_server_hello_len));
  assert (pure (SZ.fits max_handshake_flight_len));
  assert (pure (SZ.fits max_certificate_verify_input_len));
  let client_hello_bytes = alloc_empty_sized_bytes #max_client_hello_len;
  let server_hello_bytes = alloc_empty_sized_bytes #max_server_hello_len;
  let encrypted_server_handshake_bytes = alloc_empty_sized_bytes #max_handshake_flight_len;
  let encrypted_server_handshake_parsed = Box.alloc 0sz;
  let certificate_leaf_der = alloc_empty_optional_sized_bytes #max_handshake_flight_len;
  let certificate_verify_input = alloc_empty_optional_sized_bytes #max_certificate_verify_input_len;
  let buffers = {
    client_hello_bytes;
    server_hello_bytes;
    encrypted_server_handshake_bytes;
    encrypted_server_handshake_parsed;
    certificate_leaf_der;
    certificate_verify_input;
  };
  rewrite (sized_bytes_exactly client_hello_bytes max_client_hello_len B.empty) as
    (sized_bytes_exactly buffers.client_hello_bytes max_client_hello_len CS.empty_handshake_buffer_state.CS.hb_client_hello_bytes);
  rewrite (sized_bytes_exactly server_hello_bytes max_server_hello_len B.empty) as
    (sized_bytes_exactly buffers.server_hello_bytes max_server_hello_len CS.empty_handshake_buffer_state.CS.hb_server_hello_bytes);
  rewrite (sized_bytes_exactly encrypted_server_handshake_bytes max_handshake_flight_len B.empty) as
    (sized_bytes_exactly buffers.encrypted_server_handshake_bytes max_handshake_flight_len CS.empty_handshake_buffer_state.CS.hb_encrypted_server_handshake_bytes);
  rewrite (Box.pts_to encrypted_server_handshake_parsed 0sz) as
    (Box.pts_to buffers.encrypted_server_handshake_parsed 0sz);
  rewrite (optional_sized_bytes_exactly certificate_leaf_der max_handshake_flight_len None) as
    (optional_sized_bytes_exactly buffers.certificate_leaf_der max_handshake_flight_len CS.empty_handshake_buffer_state.CS.hb_certificate_leaf_der);
  rewrite (optional_sized_bytes_exactly certificate_verify_input max_certificate_verify_input_len None) as
    (optional_sized_bytes_exactly buffers.certificate_verify_input max_certificate_verify_input_len CS.empty_handshake_buffer_state.CS.hb_certificate_verify_input);
  fold (handshake_buffers_exactly buffers CS.empty_handshake_buffer_state);
  buffers
}

fn alloc_handshake_empty ()
  requires emp
  returns handshake:handshake_storage
  ensures handshake_exactly handshake CS.empty_handshake_state
{
  let start = alloc_handshake_start_empty ();
  let messages = alloc_handshake_messages_empty ();
  let server_key_share = alloc_empty_optional_fixed32 ();
  let validated_peer = alloc_peer_empty ();
  let certificate_verify_verified = Box.alloc false;
  let server_finished_verified = Box.alloc false;
  assert (pure (SZ.fits max_transcript_len));
  let transcript = alloc_empty_sized_bytes #max_transcript_len;
  let buffers = alloc_handshake_buffers_empty ();
  let keys = alloc_key_schedule_empty ();
  let handshake = {
    start;
    messages;
    server_key_share;
    validated_peer;
    certificate_verify_verified;
    server_finished_verified;
    transcript;
    buffers;
    keys;
  };
  rewrite (handshake_start_exactly start None) as
    (handshake_start_exactly handshake.start CS.empty_handshake_state.CS.hs_start);
  rewrite (handshake_messages_exactly messages CS.empty_handshake_state) as
    (handshake_messages_exactly handshake.messages CS.empty_handshake_state);
  rewrite (optional_fixed_bytes_exactly server_key_share 32 None) as
    (server_key_share_exactly handshake.server_key_share CS.empty_handshake_state);
  rewrite (peer_exactly validated_peer None) as
    (peer_exactly handshake.validated_peer CS.empty_handshake_state.CS.hs_validated_peer);
  rewrite (Box.pts_to certificate_verify_verified false) as
    (Box.pts_to handshake.certificate_verify_verified false);
  rewrite (Box.pts_to server_finished_verified false) as
    (Box.pts_to handshake.server_finished_verified false);
  rewrite (sized_bytes_exactly transcript max_transcript_len B.empty) as
    (sized_bytes_exactly handshake.transcript max_transcript_len CS.empty_handshake_state.CS.hs_transcript);
  rewrite (handshake_buffers_exactly buffers CS.empty_handshake_buffer_state) as
    (handshake_buffers_exactly handshake.buffers CS.empty_handshake_state.CS.hs_buffers);
  rewrite (key_schedule_exactly keys CS.empty_key_schedule_state) as
    (key_schedule_exactly handshake.keys CS.empty_handshake_state.CS.hs_keys);
  fold (handshake_exactly handshake CS.empty_handshake_state);
  handshake
}

fn alloc_application_empty ()
  requires emp
  returns app:application_storage
  ensures application_exactly app CS.empty_application_state
{
  assert (pure (SZ.fits max_pending_plaintext_len));
  assert (pure (SZ.fits max_pending_raw_len));
  let pending_plaintext = alloc_empty_sized_bytes #max_pending_plaintext_len;
  let pending_source_record = alloc_empty_sized_bytes #max_pending_plaintext_len;
  let pending_source_offset = Box.alloc 0sz;
  let pending_received_raw = alloc_empty_sized_bytes #max_pending_raw_len;
  let app = {
    pending_plaintext;
    pending_source_record;
    pending_source_offset;
    pending_received_raw;
  };
  rewrite (sized_bytes_exactly pending_plaintext max_pending_plaintext_len B.empty) as
    (sized_bytes_exactly app.pending_plaintext max_pending_plaintext_len CS.empty_application_state.CS.app_pending_plaintext);
  rewrite (sized_bytes_exactly pending_source_record max_pending_plaintext_len B.empty) as
    (sized_bytes_exactly app.pending_source_record max_pending_plaintext_len CS.empty_application_state.CS.app_pending_source_record);
  rewrite (Box.pts_to pending_source_offset 0sz) as
    (Box.pts_to app.pending_source_offset 0sz);
  rewrite (sized_bytes_exactly pending_received_raw max_pending_raw_len B.empty) as
    (sized_bytes_exactly app.pending_received_raw max_pending_raw_len CS.empty_application_state.CS.app_pending_received_raw);
  assert (pure (CS.pending_application_consistent CS.empty_application_state));
  fold (application_exactly app CS.empty_application_state);
  app
}

fn new_client_default ()
  requires emp
  returns c:connection_state
  ensures connection_exactly c default_initial_state
{
  lemma_default_initial_consistent ();
  let config = alloc_default_config_storage ();
  let control = alloc_control_new ();
  let read = Rec.record_state_new ();
  let write = Rec.record_state_new ();
  let records = { read; write };
  let handshake = alloc_handshake_empty ();
  let application = alloc_application_empty ();
  let ghost_state = MR.alloc #_ #connection_state_preorder default_initial_state;
  let c = {
    config;
    control;
    records;
    handshake;
    application;
    ghost_state;
  };
  rewrite (connection_config_exactly config default_connection_config) as
    (connection_config_exactly c.config default_initial_state.CS.cs_model.CS.model_config);
  rewrite (control_exactly control CS.ControlNew None) as
    (control_exactly
      c.control
      default_initial_state.CS.cs_model.CS.model_control
      default_initial_state.CS.cs_model.CS.model_failure);
  rewrite (Rec.is_record_state read R.initial_direction_state) as
    (Rec.is_record_state c.records.read default_initial_state.CS.cs_model.CS.model_record.CS.record_read);
  rewrite (Rec.is_record_state write R.initial_direction_state) as
    (Rec.is_record_state c.records.write default_initial_state.CS.cs_model.CS.model_record.CS.record_write);
  fold (record_layer_exactly c.records default_initial_state.CS.cs_model.CS.model_record);
  rewrite (handshake_exactly handshake CS.empty_handshake_state) as
    (handshake_exactly c.handshake default_initial_state.CS.cs_model.CS.model_handshake);
  rewrite (application_exactly application CS.empty_application_state) as
    (application_exactly c.application default_initial_state.CS.cs_model.CS.model_application);
  fold (connection_model_exactly c default_initial_state.CS.cs_model);
  rewrite (MR.pts_to ghost_state #1.0R default_initial_state) as
    (MR.pts_to c.ghost_state #1.0R default_initial_state);
  fold (connection_exactly c default_initial_state);
  c
}

fn new_client
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires ArrPts.pts_to server_name 'server_name_bytes **
           ArrPts.pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <= max_hostname_len /\
                 SZ.v trust_anchors_len <= max_trust_anchors_len)
  returns c:connection_state
  ensures ArrPts.pts_to server_name 'server_name_bytes **
          ArrPts.pts_to trust_anchors 'trust_anchors_bytes **
          connection_exactly
            c
            (configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds)
{
  lemma_configured_initial_consistent
    (Ghost.reveal 'server_name_bytes)
    (Ghost.reveal 'trust_anchors_bytes)
    validation_time_seconds;
  let config =
    alloc_config_storage
      server_name
      server_name_len
      trust_anchors
      trust_anchors_len
      validation_time_seconds;
  let control = alloc_control_new ();
  let read = Rec.record_state_new ();
  let write = Rec.record_state_new ();
  let records = { read; write };
  let handshake = alloc_handshake_empty ();
  let application = alloc_application_empty ();
  let ghost_state = MR.alloc #_ #connection_state_preorder
    (configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds);
  let c = {
    config;
    control;
    records;
    handshake;
    application;
    ghost_state;
  };
  rewrite (connection_config_exactly
    config
    (configured_connection_config
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds)) as
    (connection_config_exactly
      c.config
      (configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds).CS.cs_model.CS.model_config);
  rewrite (control_exactly control CS.ControlNew None) as
    (control_exactly
      c.control
      (configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds).CS.cs_model.CS.model_control
      (configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds).CS.cs_model.CS.model_failure);
  rewrite (Rec.is_record_state read R.initial_direction_state) as
    (Rec.is_record_state
      c.records.read
      (configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds).CS.cs_model.CS.model_record.CS.record_read);
  rewrite (Rec.is_record_state write R.initial_direction_state) as
    (Rec.is_record_state
      c.records.write
      (configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds).CS.cs_model.CS.model_record.CS.record_write);
  fold (record_layer_exactly
    c.records
    (configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds).CS.cs_model.CS.model_record);
  rewrite (handshake_exactly handshake CS.empty_handshake_state) as
    (handshake_exactly
      c.handshake
      (configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds).CS.cs_model.CS.model_handshake);
  rewrite (application_exactly application CS.empty_application_state) as
    (application_exactly
      c.application
      (configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds).CS.cs_model);
  rewrite (MR.pts_to
    ghost_state
    #1.0R
    (configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds)) as
    (MR.pts_to
      c.ghost_state
      #1.0R
      (configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds));
  fold (connection_exactly
    c
    (configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds));
  c
}

fn copy_server_hello_prefix_to_transcript
  (src:V.vec U8.t)
  (dst:V.vec U8.t)
  (src_len:SZ.t)
  (dst_offset:SZ.t)
  requires V.pts_to src 'src_bytes **
           V.pts_to dst 'dst_bytes **
           pure (V.is_full_vec src /\
                 V.is_full_vec dst /\
                 V.length src == max_server_hello_len /\
                 V.length dst == max_transcript_len /\
                 B.length 'src_bytes == max_server_hello_len /\
                 B.length 'dst_bytes == max_transcript_len /\
                 Seq.length 'src_bytes == max_server_hello_len /\
                 Seq.length 'dst_bytes == max_transcript_len /\
                 SZ.v src_len <= max_server_hello_len /\
                 SZ.v dst_offset + SZ.v src_len <= max_transcript_len)
  ensures V.pts_to src 'src_bytes **
          V.pts_to dst
            (Seq.append
              (CL.raw_slice 'dst_bytes 0 (SZ.v dst_offset))
              (Seq.append
                (CL.raw_slice 'src_bytes 0 (SZ.v src_len))
                (CL.raw_slice
                  'dst_bytes
                  (SZ.v dst_offset + SZ.v src_len)
                  max_transcript_len)))
{
  V.to_array_pts_to src;
  V.to_array_pts_to dst;

  assert (pure (SZ.fits max_server_hello_len));
  assert (pure (SZ.fits max_transcript_len));
  let src_cap = SZ.uint_to_t max_server_hello_len;
  let dst_cap = SZ.uint_to_t max_transcript_len;
  let src_slice = Slice.from_array (V.vec_to_array src) src_cap;
  let dst_slice = Slice.from_array (V.vec_to_array dst) dst_cap;

  let src_split = Slice.split src_slice src_len;

  let dst_split = Slice.split dst_slice dst_offset;
  let dst_insert_split = Slice.split (snd dst_split) src_len;

  Slice.pts_to_len (fst src_split);
  Slice.pts_to_len (fst dst_insert_split);
  assert (pure (Slice.len (fst src_split) == src_len));
  assert (pure (Slice.len (fst dst_insert_split) == src_len));
  Slice.copy (fst dst_insert_split) (fst src_split);

  Slice.join (fst src_split) (snd src_split) src_slice;
  SeqP.lemma_split 'src_bytes (SZ.v src_len);
  Slice.to_array src_slice;
  V.to_vec_pts_to src;

  Slice.join (fst dst_insert_split) (snd dst_insert_split) (snd dst_split);
  Slice.join (fst dst_split) (snd dst_split) dst_slice;
  Slice.to_array dst_slice;
  V.to_vec_pts_to dst
}

fn copy_client_hello_prefix_to_transcript
  (src:V.vec U8.t)
  (dst:V.vec U8.t)
  (src_len:SZ.t)
  (dst_offset:SZ.t)
  requires V.pts_to src 'src_bytes **
           V.pts_to dst 'dst_bytes **
           pure (V.is_full_vec src /\
                 V.is_full_vec dst /\
                 V.length src == max_client_hello_len /\
                 V.length dst == max_transcript_len /\
                 B.length 'src_bytes == max_client_hello_len /\
                 B.length 'dst_bytes == max_transcript_len /\
                 Seq.length 'src_bytes == max_client_hello_len /\
                 Seq.length 'dst_bytes == max_transcript_len /\
                 SZ.v src_len <= max_client_hello_len /\
                 SZ.v dst_offset + SZ.v src_len <= max_transcript_len)
  ensures V.pts_to src 'src_bytes **
          V.pts_to dst
            (Seq.append
              (CL.raw_slice 'dst_bytes 0 (SZ.v dst_offset))
              (Seq.append
                (CL.raw_slice 'src_bytes 0 (SZ.v src_len))
                (CL.raw_slice
                  'dst_bytes
                  (SZ.v dst_offset + SZ.v src_len)
                  max_transcript_len)))
{
  V.to_array_pts_to src;
  V.to_array_pts_to dst;

  assert (pure (SZ.fits max_client_hello_len));
  assert (pure (SZ.fits max_transcript_len));
  let src_cap = SZ.uint_to_t max_client_hello_len;
  let dst_cap = SZ.uint_to_t max_transcript_len;
  let src_slice = Slice.from_array (V.vec_to_array src) src_cap;
  let dst_slice = Slice.from_array (V.vec_to_array dst) dst_cap;

  let src_split = Slice.split src_slice src_len;

  let dst_split = Slice.split dst_slice dst_offset;
  let dst_insert_split = Slice.split (snd dst_split) src_len;

  Slice.pts_to_len (fst src_split);
  Slice.pts_to_len (fst dst_insert_split);
  assert (pure (Slice.len (fst src_split) == src_len));
  assert (pure (Slice.len (fst dst_insert_split) == src_len));
  Slice.copy (fst dst_insert_split) (fst src_split);

  Slice.join (fst src_split) (snd src_split) src_slice;
  SeqP.lemma_split 'src_bytes (SZ.v src_len);
  Slice.to_array src_slice;
  V.to_vec_pts_to src;

  Slice.join (fst dst_insert_split) (snd dst_insert_split) (snd dst_split);
  Slice.join (fst dst_split) (snd dst_split) dst_slice;
  Slice.to_array dst_slice;
  V.to_vec_pts_to dst
}

fn copy_array_to_transcript
  (src:array U8.t)
  (dst:V.vec U8.t)
  (src_len:SZ.t)
  (dst_offset:SZ.t)
  requires ArrPts.pts_to src 'src_bytes **
           V.pts_to dst 'dst_bytes **
           pure (V.is_full_vec dst /\
                 V.length dst == max_transcript_len /\
                 B.length 'src_bytes == SZ.v src_len /\
                 B.length 'dst_bytes == max_transcript_len /\
                 Seq.length 'dst_bytes == max_transcript_len /\
                 SZ.v dst_offset + SZ.v src_len <= max_transcript_len)
  ensures ArrPts.pts_to src 'src_bytes **
          V.pts_to dst
            (Seq.append
              (CL.raw_slice 'dst_bytes 0 (SZ.v dst_offset))
              (Seq.append
                'src_bytes
                (CL.raw_slice
                  'dst_bytes
                  (SZ.v dst_offset + SZ.v src_len)
                  max_transcript_len)))
{
  ArrPts.pts_to_len src;
  V.to_array_pts_to dst;

  assert (pure (SZ.fits max_transcript_len));
  let dst_cap = SZ.uint_to_t max_transcript_len;
  let src_slice = Slice.from_array src src_len;
  let dst_slice = Slice.from_array (V.vec_to_array dst) dst_cap;

  let dst_split = Slice.split dst_slice dst_offset;
  let dst_insert_split = Slice.split (snd dst_split) src_len;

  Slice.pts_to_len src_slice;
  Slice.pts_to_len (fst dst_insert_split);
  assert (pure (Slice.len src_slice == src_len));
  assert (pure (Slice.len (fst dst_insert_split) == src_len));
  Slice.copy (fst dst_insert_split) src_slice;

  Slice.to_array src_slice;

  Slice.join (fst dst_insert_split) (snd dst_insert_split) (snd dst_split);
  Slice.join (fst dst_split) (snd dst_split) dst_slice;
  Slice.to_array dst_slice;
  V.to_vec_pts_to dst
}

fn copy_fixed32_array_to_vec
  (src:array U8.t)
  (dst:V.vec U8.t)
  requires ArrPts.pts_to src 'src_bytes **
           V.pts_to dst 'old_dst **
           pure (B.length 'src_bytes == 32 /\
                 V.is_full_vec dst /\
                 V.length dst == 32 /\
                 B.length 'old_dst == 32)
  ensures ArrPts.pts_to src 'src_bytes **
          V.pts_to dst 'src_bytes **
          pure (V.is_full_vec dst /\ V.length dst == 32)
{
  ArrPts.pts_to_len src;
  V.pts_to_len dst;
  V.to_array_pts_to dst;
  Arr.memcpy 32sz src (V.vec_to_array dst);
  V.to_vec_pts_to dst;
  with stored. assert (V.pts_to dst stored);
  assert (pure (stored == Ghost.reveal 'src_bytes))
}

fn store_optional_fixed32_from_array
  (src:array U8.t)
  (slot:optional_fixed_bytes)
  (#bytes:erased (b:B.bytes{B.length b == 32}))
  requires ArrPts.pts_to src bytes **
           optional_fixed_bytes_exactly slot 32 None
  ensures ArrPts.pts_to src bytes **
          optional_fixed_bytes_exactly slot 32 (Some (Ghost.reveal bytes))
{
  unfold (optional_fixed_bytes_exactly slot 32 None);
  with present old_storage. _;
  copy_fixed32_array_to_vec src slot.bytes;
  slot.present := true;
  with stored. assert (V.pts_to slot.bytes stored);
  assert (pure (stored == Ghost.reveal bytes));
  assert (pure (optional_fixed_bytes_match true stored 32 (Some (Ghost.reveal bytes))));
  fold (optional_fixed_bytes_exactly slot 32 (Some (Ghost.reveal bytes)))
}

fn copy_cipher_suite_list_storage
  (src:u16_list_storage)
  (dst:u16_list_storage)
  (cap:nat)
  (#suites:erased (list T.cipher_suite))
  requires cipher_suite_list_exactly src cap suites **
           cipher_suite_list_allocated dst cap **
           pure (SZ.fits cap)
  ensures cipher_suite_list_exactly src cap suites **
          cipher_suite_list_exactly dst cap suites
{
  unfold (cipher_suite_list_exactly src cap (Ghost.reveal suites));
  unfold (cipher_suite_list_allocated dst cap);
  with src_items. assert (V.pts_to src.items src_items);
  with src_len. assert (Box.pts_to src.len src_len);
  with dst_items. assert (V.pts_to dst.items dst_items);
  with dst_len. assert (Box.pts_to dst.len dst_len);
  let src_len_runtime = !src.len;
  assert (pure (src_len_runtime == src_len));
  let cap_sz = SZ.uint_to_t cap;
  V.to_array_pts_to src.items;
  V.to_array_pts_to dst.items;
  Arr.memcpy cap_sz (V.vec_to_array src.items) (V.vec_to_array dst.items);
  V.to_vec_pts_to src.items;
  V.to_vec_pts_to dst.items;
  dst.len := src_len_runtime;
  assert (V.pts_to dst.items src_items);
  fold (cipher_suite_list_exactly src cap (Ghost.reveal suites));
  fold (cipher_suite_list_exactly dst cap (Ghost.reveal suites))
}

fn copy_signature_scheme_list_storage
  (src:u16_list_storage)
  (dst:u16_list_storage)
  (cap:nat)
  (#schemes:erased (list T.signature_scheme))
  requires signature_scheme_list_exactly src cap schemes **
           signature_scheme_list_allocated dst cap **
           pure (SZ.fits cap)
  ensures signature_scheme_list_exactly src cap schemes **
          signature_scheme_list_exactly dst cap schemes
{
  unfold (signature_scheme_list_exactly src cap (Ghost.reveal schemes));
  unfold (signature_scheme_list_allocated dst cap);
  with src_items. assert (V.pts_to src.items src_items);
  with src_len. assert (Box.pts_to src.len src_len);
  with dst_items. assert (V.pts_to dst.items dst_items);
  with dst_len. assert (Box.pts_to dst.len dst_len);
  let src_len_runtime = !src.len;
  assert (pure (src_len_runtime == src_len));
  let cap_sz = SZ.uint_to_t cap;
  V.to_array_pts_to src.items;
  V.to_array_pts_to dst.items;
  Arr.memcpy cap_sz (V.vec_to_array src.items) (V.vec_to_array dst.items);
  V.to_vec_pts_to src.items;
  V.to_vec_pts_to dst.items;
  dst.len := src_len_runtime;
  assert (V.pts_to dst.items src_items);
  fold (signature_scheme_list_exactly src cap (Ghost.reveal schemes));
  fold (signature_scheme_list_exactly dst cap (Ghost.reveal schemes))
}

fn copy_hostname_sized_bytes
  (src:sized_bytes)
  (dst:sized_bytes)
  requires sized_bytes_exactly src max_hostname_len 'src_bytes **
           sized_bytes_allocated dst max_hostname_len
  ensures sized_bytes_exactly src max_hostname_len 'src_bytes **
          sized_bytes_exactly dst max_hostname_len 'src_bytes
{
  unfold (sized_bytes_exactly src max_hostname_len (Ghost.reveal 'src_bytes));
  with src_storage src_len. _;
  unfold (sized_bytes_allocated dst max_hostname_len);
  with dst_storage dst_len. _;
  let copy_len = !src.len;
  assert (pure (copy_len == src_len));

  V.to_array_pts_to src.bytes;
  V.to_array_pts_to dst.bytes;

  assert (pure (SZ.fits max_hostname_len));
  let cap = SZ.uint_to_t max_hostname_len;
  let src_slice = Slice.from_array (V.vec_to_array src.bytes) cap;
  let dst_slice = Slice.from_array (V.vec_to_array dst.bytes) cap;

  let src_split = Slice.split src_slice copy_len;
  let dst_split = Slice.split dst_slice copy_len;

  Slice.pts_to_len (fst src_split);
  Slice.pts_to_len (fst dst_split);
  assert (pure (Slice.len (fst src_split) == copy_len));
  assert (pure (Slice.len (fst dst_split) == copy_len));
  Slice.copy (fst dst_split) (fst src_split);

  Slice.join (fst src_split) (snd src_split) src_slice;
  SeqP.lemma_split src_storage (SZ.v copy_len);
  Slice.to_array src_slice;
  V.to_vec_pts_to src.bytes;

  Slice.join (fst dst_split) (snd dst_split) dst_slice;
  Slice.to_array dst_slice;
  V.to_vec_pts_to dst.bytes;
  dst.len := copy_len;

  with copied_dst_storage. assert (V.pts_to dst.bytes copied_dst_storage);
  assert (pure (Seq.equal
    (Seq.slice copied_dst_storage 0 (SZ.v copy_len))
    (Seq.slice src_storage 0 (SZ.v copy_len))));
  assert (pure (byte_prefix_matches copied_dst_storage copy_len (Ghost.reveal 'src_bytes)));
  fold (sized_bytes_exactly dst max_hostname_len (Ghost.reveal 'src_bytes));
  fold (sized_bytes_exactly src max_hostname_len (Ghost.reveal 'src_bytes))
}

fn copy_array_to_public_key_sized_bytes
  (src:array U8.t)
  (dst:sized_bytes)
  (src_len:SZ.t)
  requires ArrPts.pts_to src 'src_bytes **
           sized_bytes_allocated dst max_public_key_len **
           pure (B.length 'src_bytes == SZ.v src_len /\
                 SZ.v src_len <= max_public_key_len)
  ensures ArrPts.pts_to src 'src_bytes **
          sized_bytes_exactly dst max_public_key_len (Ghost.reveal 'src_bytes)
{
  unfold (sized_bytes_allocated dst max_public_key_len);
  with dst_storage dst_len. _;

  ArrPts.pts_to_len src;
  V.to_array_pts_to dst.bytes;

  assert (pure (SZ.fits max_public_key_len));
  let dst_cap = SZ.uint_to_t max_public_key_len;
  let src_slice = Slice.from_array src src_len;
  let dst_slice = Slice.from_array (V.vec_to_array dst.bytes) dst_cap;

  let dst_split = Slice.split dst_slice src_len;

  Slice.pts_to_len src_slice;
  Slice.pts_to_len (fst dst_split);
  assert (pure (Slice.len src_slice == src_len));
  assert (pure (Slice.len (fst dst_split) == src_len));
  Slice.copy (fst dst_split) src_slice;

  Slice.to_array src_slice;

  Slice.join (fst dst_split) (snd dst_split) dst_slice;
  Slice.to_array dst_slice;
  V.to_vec_pts_to dst.bytes;
  dst.len := src_len;

  with copied_dst_storage. assert (V.pts_to dst.bytes copied_dst_storage);
  Seq.lemma_len_slice copied_dst_storage 0 (SZ.v src_len);
  assert (pure (Seq.equal
    (Seq.slice copied_dst_storage 0 (SZ.v src_len))
    (Ghost.reveal 'src_bytes)));
  fold (sized_bytes_exactly dst max_public_key_len (Ghost.reveal 'src_bytes))
}

fn copy_array_to_certificate_verify_input_sized_bytes
  (src:array U8.t)
  (dst:sized_bytes)
  (src_len:SZ.t)
  (#input:erased B.bytes)
  requires ArrPts.pts_to src 'src_bytes **
           sized_bytes_allocated dst max_certificate_verify_input_len **
           pure (B.length 'src_bytes == SZ.v src_len /\
                 SZ.v src_len <= max_certificate_verify_input_len /\
                 Seq.equal (Ghost.reveal 'src_bytes) (Ghost.reveal input))
  ensures ArrPts.pts_to src 'src_bytes **
          sized_bytes_exactly dst max_certificate_verify_input_len (Ghost.reveal input)
{
  unfold (sized_bytes_allocated dst max_certificate_verify_input_len);
  with dst_storage dst_len. _;

  ArrPts.pts_to_len src;
  V.to_array_pts_to dst.bytes;

  assert (pure (SZ.fits max_certificate_verify_input_len));
  let dst_cap = SZ.uint_to_t max_certificate_verify_input_len;
  let src_slice = Slice.from_array src src_len;
  let dst_slice = Slice.from_array (V.vec_to_array dst.bytes) dst_cap;

  let dst_split = Slice.split dst_slice src_len;

  Slice.pts_to_len src_slice;
  Slice.pts_to_len (fst dst_split);
  assert (pure (Slice.len src_slice == src_len));
  assert (pure (Slice.len (fst dst_split) == src_len));
  Slice.copy (fst dst_split) src_slice;

  Slice.to_array src_slice;

  Slice.join (fst dst_split) (snd dst_split) dst_slice;
  Slice.to_array dst_slice;
  V.to_vec_pts_to dst.bytes;
  dst.len := src_len;

  with copied_dst_storage. assert (V.pts_to dst.bytes copied_dst_storage);
  Seq.lemma_len_slice copied_dst_storage 0 (SZ.v src_len);
  assert (pure (Seq.equal
    (Seq.slice copied_dst_storage 0 (SZ.v src_len))
    (Ghost.reveal 'src_bytes)));
  assert (pure (Seq.equal
    (Seq.slice copied_dst_storage 0 (SZ.v src_len))
    (Ghost.reveal input)));
  fold (sized_bytes_exactly dst max_certificate_verify_input_len (Ghost.reveal input))
}

fn overwrite_optional_certificate_verify_input
  (src:array U8.t)
  (slot:optional_sized_bytes)
  (src_len:SZ.t)
  (#input:erased B.bytes)
  requires ArrPts.pts_to src 'src_bytes **
           optional_sized_bytes_exactly slot max_certificate_verify_input_len None **
           pure (B.length 'src_bytes == SZ.v src_len /\
                 SZ.v src_len <= max_certificate_verify_input_len /\
                 Seq.equal (Ghost.reveal 'src_bytes) (Ghost.reveal input))
  ensures ArrPts.pts_to src 'src_bytes **
          optional_sized_bytes_exactly
            slot
            max_certificate_verify_input_len
            (Some (Ghost.reveal input))
{
  unfold (optional_sized_bytes_exactly slot max_certificate_verify_input_len None);
  with present old_storage old_len. _;
  fold (sized_bytes_allocated slot.value max_certificate_verify_input_len);
  copy_array_to_certificate_verify_input_sized_bytes
    src
    slot.value
    src_len
    #input;
  unfold (sized_bytes_exactly slot.value max_certificate_verify_input_len (Ghost.reveal input));
  with stored len. _;
  slot.present := true;
  fold (optional_sized_bytes_exactly
    slot
    max_certificate_verify_input_len
    (Some (Ghost.reveal input)))
}

fn copy_certificate_chain_range_to_sized_bytes
  (src:V.vec U8.t)
  (dst:sized_bytes)
  (src_offset:SZ.t)
  (src_len:SZ.t)
  (#leaf:erased B.bytes)
  requires V.pts_to src 'src_bytes **
           sized_bytes_allocated dst max_handshake_flight_len **
           pure (V.is_full_vec src /\
                 V.length src == IM.max_certificate_chain_bytes /\
                 B.length 'src_bytes == IM.max_certificate_chain_bytes /\
                 Seq.length 'src_bytes == IM.max_certificate_chain_bytes /\
                 SZ.v src_offset + SZ.v src_len <= B.length 'src_bytes /\
                 SZ.v src_len <= max_handshake_flight_len /\
                 Seq.equal
                   (Ghost.reveal leaf)
                   (Seq.slice 'src_bytes (SZ.v src_offset) (SZ.v src_offset + SZ.v src_len)))
  ensures V.pts_to src 'src_bytes **
          sized_bytes_exactly dst max_handshake_flight_len (Ghost.reveal leaf)
{
  unfold (sized_bytes_allocated dst max_handshake_flight_len);
  with dst_bytes old_len. _;

  V.to_array_pts_to src;
  V.to_array_pts_to dst.bytes;

  assert (pure (SZ.fits IM.max_certificate_chain_bytes));
  assert (pure (SZ.fits max_handshake_flight_len));
  let src_cap = SZ.uint_to_t IM.max_certificate_chain_bytes;
  let dst_cap = SZ.uint_to_t max_handshake_flight_len;
  let src_slice = Slice.from_array (V.vec_to_array src) src_cap;
  let dst_slice = Slice.from_array (V.vec_to_array dst.bytes) dst_cap;

  let src_prefix_split = Slice.split src_slice src_offset;
  let src_leaf_split = Slice.split (snd src_prefix_split) src_len;
  let dst_leaf_split = Slice.split dst_slice src_len;

  Slice.pts_to_len (fst src_leaf_split);
  Slice.pts_to_len (fst dst_leaf_split);
  assert (pure (Slice.len (fst src_leaf_split) == src_len));
  assert (pure (Slice.len (fst dst_leaf_split) == src_len));
  Slice.copy (fst dst_leaf_split) (fst src_leaf_split);

  Slice.join (fst src_leaf_split) (snd src_leaf_split) (snd src_prefix_split);
  Slice.join (fst src_prefix_split) (snd src_prefix_split) src_slice;
  SeqP.lemma_split 'src_bytes (SZ.v src_offset);
  SeqP.lemma_split
    (Seq.slice 'src_bytes (SZ.v src_offset) (Seq.length 'src_bytes))
    (SZ.v src_len);
  assert (pure (Seq.equal
    (Seq.append
      (Seq.slice 'src_bytes 0 (SZ.v src_offset))
      (Seq.append
        (Seq.slice
          (Seq.slice 'src_bytes (SZ.v src_offset) (Seq.length 'src_bytes))
          0
          (SZ.v src_len))
        (Seq.slice
          (Seq.slice 'src_bytes (SZ.v src_offset) (Seq.length 'src_bytes))
          (SZ.v src_len)
          (Seq.length (Seq.slice 'src_bytes (SZ.v src_offset) (Seq.length 'src_bytes))))))
    'src_bytes));
  Slice.to_array src_slice;
  V.to_vec_pts_to src;

  Slice.join (fst dst_leaf_split) (snd dst_leaf_split) dst_slice;
  Slice.to_array dst_slice;
  V.to_vec_pts_to dst.bytes;
  dst.len := src_len;

  with stored. assert (V.pts_to dst.bytes stored);
  Seq.lemma_len_slice stored 0 (SZ.v src_len);
  assert (pure (Seq.equal
    (Seq.slice stored 0 (SZ.v src_len))
    (Seq.slice 'src_bytes (SZ.v src_offset) (SZ.v src_offset + SZ.v src_len))));
  assert (pure (Seq.equal
    (Seq.slice stored 0 (SZ.v src_len))
    (Ghost.reveal leaf)));
  fold (sized_bytes_exactly dst max_handshake_flight_len (Ghost.reveal leaf))
}

fn overwrite_optional_sized_bytes_from_certificate_chain
  (src:V.vec U8.t)
  (slot:optional_sized_bytes)
  (src_offset:SZ.t)
  (src_len:SZ.t)
  (#leaf:erased B.bytes)
  requires V.pts_to src 'src_bytes **
           optional_sized_bytes_exactly slot max_handshake_flight_len None **
           pure (V.is_full_vec src /\
                 V.length src == IM.max_certificate_chain_bytes /\
                 B.length 'src_bytes == IM.max_certificate_chain_bytes /\
                 Seq.length 'src_bytes == IM.max_certificate_chain_bytes /\
                 SZ.v src_offset + SZ.v src_len <= B.length 'src_bytes /\
                 SZ.v src_len <= max_handshake_flight_len /\
                 Seq.equal
                   (Ghost.reveal leaf)
                   (Seq.slice 'src_bytes (SZ.v src_offset) (SZ.v src_offset + SZ.v src_len)))
  ensures V.pts_to src 'src_bytes **
          optional_sized_bytes_exactly
            slot
            max_handshake_flight_len
            (Some (Ghost.reveal leaf))
{
  unfold (optional_sized_bytes_exactly slot max_handshake_flight_len None);
  with present old_storage old_len. _;
  fold (sized_bytes_allocated slot.value max_handshake_flight_len);
  copy_certificate_chain_range_to_sized_bytes
    src
    slot.value
    src_offset
    src_len
    #leaf;
  unfold (sized_bytes_exactly slot.value max_handshake_flight_len (Ghost.reveal leaf));
  with stored len. _;
  slot.present := true;
  fold (optional_sized_bytes_exactly
    slot
    max_handshake_flight_len
    (Some (Ghost.reveal leaf)))
}

let tls_decode_error : T.tls_error = T.AlertError T.DecodeError

let tls_unexpected_message_error : T.tls_error = T.AlertError T.UnexpectedMessage

let tls_hello_retry_request_rejected_error : T.tls_error = T.HelloRetryRequestRejected

let lemma_nonempty_cipher_suites_offer
  (suites:list T.cipher_suite)
  (suite:T.cipher_suite)
  : Lemma
      (requires suites <> [])
      (ensures CS.cipher_suite_offered suites suite)
=
  match suites with
  | [] -> ()
  | _ :: _ ->
    match suite with
    | T.TLS_CHACHA20_POLY1305_SHA256 -> ()

let local_fail_state (st:CS.connection_state) (err:T.tls_error) : CS.connection_state =
  {
    CS.cs_model = CS.fail_model st.CS.cs_model err;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log = st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalFail err)];
  }

let client_hello_of_start (start:CS.handshake_start) : M.client_hello =
  {
    M.random = start.CS.start_client_random;
    M.server_name = Some start.CS.start_server_name;
    M.key_share = start.CS.start_client_key_share_public;
    M.cipher_suites = start.CS.start_cipher_suites;
    M.signature_schemes = start.CS.start_signature_schemes;
  }

let started_handshake_state
  (st:CS.connection_state)
  (start:CS.handshake_start)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  {
    CS.cs_model =
      CS.with_handshake_stage
        model0
        { hs0 with CS.hs_start = Some start }
        CS.HsStarted;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalStartHandshake start)];
  }

let can_start_handshake
  (st:CS.connection_state)
  (start:CS.handshake_start)
  : GTot prop =
  st.CS.cs_model.CS.model_control == CS.ControlNew /\
  CS.start_matches_config st.CS.cs_model.CS.model_config start /\
  CS.handshake_start_key_share_consistent start /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnLocalEvent (CS.LocalStartHandshake start))

let sent_client_hello_state
  (st:CS.connection_state)
  (ch:M.client_hello)
  (raw_sent:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.ClientHello ch in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with
          CS.hs_client_hello = Some ch;
          CS.hs_buffers =
            { hs0.CS.hs_buffers with
                CS.hb_client_hello_bytes = W.serialize_handshake msg };
      }
      msg in
  {
    CS.cs_model = CS.with_handshake_stage model0 hs1 CS.HsClientHelloSent;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent raw_sent;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let can_send_client_hello
  (st:CS.connection_state)
  (ch:M.client_hello)
  (raw_sent:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsStarted /\
  st.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None /\
  (match st.CS.cs_model.CS.model_handshake.CS.hs_start with
   | Some start -> CS.client_hello_matches_start start ch
   | None -> False) /\
  B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
    B.length (W.serialize_handshake (M.ClientHello ch)) <= max_transcript_len /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    })
    raw_sent
    B.empty

let lemma_client_hello_of_start_matches
  (start:CS.handshake_start)
  : Lemma (CS.client_hello_matches_start start (client_hello_of_start start))
=
  ()

let lemma_client_hello_len_helpers_from_start
  (start:CS.handshake_start)
  (ch:M.client_hello)
  (server_name_storage:B.bytes)
  (server_name_len:SZ.t)
  (cipher_suites:Seq.seq U16.t)
  (cipher_suites_len:SZ.t)
  (signature_schemes:Seq.seq U16.t)
  (signature_schemes_len:SZ.t)
  : Lemma
      (requires ch == client_hello_of_start start /\
                B.length server_name_storage == max_hostname_len /\
                B.length start.CS.start_server_name == SZ.v server_name_len /\
                SZ.v server_name_len <= B.length server_name_storage /\
                Seq.length cipher_suites == max_cipher_suites /\
                SZ.v cipher_suites_len <= Seq.length cipher_suites /\
                IM.cipher_suites_match
                  cipher_suites
                  (SZ.v cipher_suites_len)
                  start.CS.start_cipher_suites /\
                Seq.length signature_schemes == max_signature_schemes /\
                SZ.v signature_schemes_len <= Seq.length signature_schemes /\
                IM.signature_schemes_match
                  signature_schemes
                  (SZ.v signature_schemes_len)
                  start.CS.start_signature_schemes)
      (ensures client_hello_server_name_len_for ch == server_name_len /\
               client_hello_cipher_suites_len_for ch == cipher_suites_len /\
               client_hello_signature_schemes_len_for ch == signature_schemes_len)
=
  assert (ch.M.server_name == Some start.CS.start_server_name);
  assert (B.length start.CS.start_server_name < 65536);
  lemma_bounded_u16_sizet_of_sizet
    (B.length start.CS.start_server_name)
    server_name_len;

  lemma_cipher_suites_match_length
    cipher_suites
    (SZ.v cipher_suites_len)
    start.CS.start_cipher_suites;
  assert (length start.CS.start_cipher_suites == SZ.v cipher_suites_len);
  assert (length start.CS.start_cipher_suites < 65536);
  lemma_bounded_u16_sizet_of_sizet
    (length start.CS.start_cipher_suites)
    cipher_suites_len;

  lemma_signature_schemes_match_length
    signature_schemes
    (SZ.v signature_schemes_len)
    start.CS.start_signature_schemes;
  assert (length start.CS.start_signature_schemes == SZ.v signature_schemes_len);
  assert (length start.CS.start_signature_schemes < 65536);
  lemma_bounded_u16_sizet_of_sizet
    (length start.CS.start_signature_schemes)
    signature_schemes_len

let derived_shared_secret_state
  (st:CS.connection_state)
  (shared:TLS13.Crypto.Spec.x25519_shared_secret)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let early = K.early_secret B.empty in
  let handshake = K.handshake_secret early shared in
  let master = K.master_secret handshake in
  let keys0 = hs0.CS.hs_keys in
  let keys1 =
    {
      keys0 with
        CS.ks_shared_secret = Some shared;
        CS.ks_early_secret = Some early;
        CS.ks_handshake_secret = Some handshake;
        CS.ks_master_secret = Some master;
    } in
  {
    CS.cs_model =
      CS.with_handshake_state model0 { hs0 with CS.hs_keys = keys1 };
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)];
  }

let installed_traffic_keys_state
  (st:CS.connection_state)
  (install:CS.traffic_key_install)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  {
    CS.cs_model = {
      model0 with
        CS.model_record = CS.install_record_keys model0.CS.model_record install;
        CS.model_handshake = {
          hs0 with
            CS.hs_keys = CS.update_key_schedule_with_install hs0.CS.hs_keys install;
        };
    };
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install)];
  }

let validated_certificate_state
  (st:CS.connection_state)
  (peer:X.peer_identity)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  {
    CS.cs_model =
      CS.with_handshake_stage
        model0
        { hs0 with CS.hs_validated_peer = Some peer }
        CS.HsCertificateValidated;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalValidateCertificate peer)];
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

let received_server_hello_state
  (st:CS.connection_state)
  (sh:M.server_hello)
  (raw_received:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.ServerHello sh in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with
          CS.hs_server_hello = Some sh;
          CS.hs_buffers =
            { hs0.CS.hs_buffers with
                CS.hb_server_hello_bytes = W.serialize_handshake msg };
      }
      msg in
  {
    CS.cs_model = CS.with_handshake_stage model0 hs1 CS.HsServerHelloReceived;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let received_encrypted_extensions_state
  (st:CS.connection_state)
  (ee:M.encrypted_extensions)
  (raw_received:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.EncryptedExtensions ee in
  let model1 = {
    model0 with
      CS.model_record = {
        model0.CS.model_record with
          CS.record_read = R.next_seq model0.CS.model_record.CS.record_read;
      };
  } in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with CS.hs_encrypted_extensions = Some ee }
      msg in
  {
    CS.cs_model = CS.with_handshake_stage model1 hs1 CS.HsEncryptedExtensionsReceived;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let received_certificate_state
  (st:CS.connection_state)
  (cert:M.certificate_msg)
  (raw_received:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.Certificate cert in
  let model1 = {
    model0 with
      CS.model_record = {
        model0.CS.model_record with
          CS.record_read = R.next_seq model0.CS.model_record.CS.record_read;
      };
  } in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with
          CS.hs_certificate = Some cert;
          CS.hs_buffers =
            { hs0.CS.hs_buffers with
                CS.hb_certificate_leaf_der =
                  (match cert.M.chain with
                   | leaf :: _ -> Some leaf
                   | [] -> None);
            };
      }
      msg in
  {
    CS.cs_model = CS.with_handshake_stage model1 hs1 CS.HsCertificateReceived;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let received_certificate_verify_state
  (st:CS.connection_state)
  (cv:M.certificate_verify)
  (raw_received:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.CertificateVerify cv in
  let cv_input = H.certificate_verify_input (Tr.hash hs0.CS.hs_transcript) in
  let model1 = {
    model0 with
      CS.model_record = {
        model0.CS.model_record with
          CS.record_read = R.next_seq model0.CS.model_record.CS.record_read;
      };
  } in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with
          CS.hs_certificate_verify = Some cv;
          CS.hs_buffers =
            { hs0.CS.hs_buffers with
                CS.hb_certificate_verify_input = Some cv_input;
            };
      }
      msg in
  {
    CS.cs_model = CS.with_handshake_stage model1 hs1 CS.HsCertificateVerifyReceived;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let verified_certificate_signature_state
  (st:CS.connection_state)
  (cv:M.certificate_verify)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  {
    CS.cs_model =
      CS.with_handshake_stage
        model0
        { hs0 with
            CS.hs_certificate_verify = Some cv;
            CS.hs_certificate_verify_verified = true;
        }
        CS.HsCertificateVerifyVerified;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv)];
  }

let received_server_finished_state
  (st:CS.connection_state)
  (fin:M.finished)
  (raw_received:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.Finished fin in
  let model1 = {
    model0 with
      CS.model_record = {
        model0.CS.model_record with
          CS.record_read = R.next_seq model0.CS.model_record.CS.record_read;
      };
  } in
  {
    CS.cs_model =
      CS.with_handshake_stage
        model1
        { hs0 with CS.hs_server_finished = Some fin }
        CS.HsServerFinishedReceived;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received raw_received;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let verified_server_finished_state
  (st:CS.connection_state)
  (fin:M.finished)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  {
    CS.cs_model =
      CS.with_handshake_stage
        model0
        (CS.append_handshake_to_transcript
          { hs0 with
              CS.hs_server_finished = Some fin;
              CS.hs_server_finished_verified = true;
          }
          (M.Finished fin))
        CS.HsServerFinishedVerified;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @ [CS.ConnLocalEvent (CS.LocalVerifyFinished fin)];
  }

let sent_client_finished_state
  (st:CS.connection_state)
  (fin:M.finished)
  (raw_sent:B.bytes)
  : GTot CS.connection_state =
  let model0 = st.CS.cs_model in
  let hs0 = model0.CS.model_handshake in
  let msg = M.Finished fin in
  let hs1 =
    CS.append_handshake_to_transcript
      { hs0 with CS.hs_client_finished = Some fin }
      msg in
  let model1 = {
    model0 with
      CS.model_control = CS.ControlApplicationData;
      CS.model_record =
        CS.install_client_application_write_after_finished
          model0.CS.model_record
          hs0.CS.hs_keys;
      CS.model_handshake = hs1;
  } in
  {
    CS.cs_model = model1;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent raw_sent;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake msg;
      }];
  }

let can_send_client_finished
  (st:CS.connection_state)
  (fin:M.finished)
  (raw_sent:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerFinishedVerified /\
  st.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None /\
  Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
  Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
  Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
  U64.fits (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
  B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
    B.length (W.serialize_handshake (M.Finished fin)) <= max_transcript_len /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    })
    raw_sent
    B.empty

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

let sent_close_notify_state
  (st:CS.connection_state)
  (raw_sent:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let record0 = model0.CS.model_record in
  let model1 = {
    model0 with
      CS.model_control = CS.ControlClosing;
      CS.model_record = {
        record0 with
          CS.record_write = R.next_seq record0.CS.record_write;
      };
  } in
  {
    CS.cs_model = model1;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent raw_sent;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
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

let delivered_application_data_state
  (st:CS.connection_state)
  (bytes:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let app0 = model0.CS.model_application in
  let model1 = {
    model0 with
      CS.model_application = {
        app0 with
          CS.app_log = CL.append_app_received app0.CS.app_log bytes;
      };
  } in
  {
    CS.cs_model = model1;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent B.empty;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes)];
  }

let sent_application_data_state
  (st:CS.connection_state)
  (bytes:B.bytes)
  (raw_sent:B.bytes)
  : CS.connection_state =
  let model0 = st.CS.cs_model in
  let record0 = model0.CS.model_record in
  let app0 = model0.CS.model_application in
  let model1 = {
    model0 with
      CS.model_record = {
        record0 with
          CS.record_write = R.next_seq record0.CS.record_write;
      };
      CS.model_application = {
        app0 with
          CS.app_log = CL.append_app_sent app0.CS.app_log bytes;
      };
  } in
  {
    CS.cs_model = model1;
    CS.cs_wire_log = {
      CL.raw_sent = B.append st.CS.cs_wire_log.CL.raw_sent raw_sent;
      CL.raw_received = B.append st.CS.cs_wire_log.CL.raw_received B.empty;
    };
    CS.cs_event_log =
      st.CS.cs_event_log @
      [CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsApplicationData bytes;
      }];
  }

let lemma_application_data_record_count_small
  (bytes:B.bytes)
  : Lemma
      (requires B.length bytes <= SM.max_application_data_fragment_len)
      (ensures SM.application_data_record_count bytes == 1)
=
  SM.lemma_application_data_record_count_len_small (B.length bytes)

let lemma_advance_direction_records_one (s:R.direction_state)
  : Lemma (CS.advance_direction_records s 1 == R.next_seq s)
=
  ()

let lemma_seal_application_success_next_seq
  (s:R.direction_state)
  (aad:B.bytes)
  (payload:B.bytes)
  (ciphertext:B.bytes)
  (s':R.direction_state)
  : Lemma
      (requires R.seal
                  s
                  aad
                  { R.content_type = T.ApplicationData;
                    R.fragment = payload } == Some (ciphertext, s'))
      (ensures s' == R.next_seq s)
=
  match s.R.key, s.R.static_iv with
  | Some _, Some _ -> ()
  | _, _ -> ()

let can_send_application_data
  (st:CS.connection_state)
  (bytes:B.bytes)
  (raw_sent:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
  Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
  U64.fits (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
  B.length bytes <= SM.max_application_data_fragment_len /\
  SM.application_data_record_count bytes == 1 /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsApplicationData bytes;
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsApplicationData bytes;
    })
    raw_sent
    B.empty

noextract
let close_notify_alert_fragment : B.bytes = B.of_list [2uy; 0uy]

let can_send_close_notify
  (st:CS.connection_state)
  (raw_sent:B.bytes)
  : GTot prop =
  st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
  Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
  U64.fits (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
  CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsAlert T.CloseNotify;
    }) /\
  CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsAlert T.CloseNotify;
    })
    raw_sent
    B.empty

let can_send_application_data_sizes
  (payload_len:SZ.t)
  (network_out_len:SZ.t)
  : Pure bool
      (requires True)
      (ensures fun ok ->
        ok ==> SZ.v payload_len <= SM.max_application_data_fragment_len /\
                 SZ.v payload_len + 21 <= SZ.v network_out_len)
=
  assert_norm (SM.max_application_data_fragment_len == 16384);
  let max_payload = 16384sz in
  let payload_fits = sizet_lte_plain payload_len max_payload in
  lemma_sizet_lte_plain payload_len max_payload;
  if payload_fits then
    begin
      assert (SZ.v payload_len <= SM.max_application_data_fragment_len);
      assert (SZ.fits (SZ.v payload_len + 21));
      let needed = SZ.add payload_len 21sz in
      let out_room = sizet_lte_plain needed network_out_len in
      lemma_sizet_lte_plain needed network_out_len;
      assert (out_room ==> SZ.v payload_len + 21 <= SZ.v network_out_len);
      out_room
    end
  else
    false

let can_send_close_notify_sizes
  (network_out_len:SZ.t)
  : Pure bool
      (requires True)
      (ensures fun ok ->
        ok ==> 23 <= SZ.v network_out_len)
=
  let out_room = sizet_lte_plain 23sz network_out_len in
  lemma_sizet_lte_plain 23sz network_out_len;
  out_room

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

let lemma_started_handshake_state_evolves
  (st:CS.connection_state)
  (start:CS.handshake_start)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_start_handshake st start)
      (ensures CS.connection_state_evolves
                 st
                 (started_handshake_state st start) /\
               CS.connection_state_consistent
                 (started_handshake_state st start) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalStartHandshake start);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (started_handshake_state st start))
=
  let ev = CS.ConnLocalEvent (CS.LocalStartHandshake start) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (started_handshake_state st start).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta st delta (started_handshake_state st start));
  assert (CS.connection_state_single_step st (started_handshake_state st start));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (started_handshake_state st start);
  assert (CS.connection_state_evolves st (started_handshake_state st start));
  assert (CS.connection_state_consistent (started_handshake_state st start))

let lemma_sent_client_hello_state_evolves
  (st:CS.connection_state)
  (ch:M.client_hello)
  (raw_sent:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_send_client_hello st ch raw_sent)
      (ensures CS.connection_state_evolves
                 st
                 (sent_client_hello_state st ch raw_sent) /\
               CS.connection_state_consistent
                 (sent_client_hello_state st ch raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.ClientHello ch);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_client_hello_state st ch raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_client_hello_state st ch raw_sent).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.legal_connection_delta st delta (sent_client_hello_state st ch raw_sent));
  assert (CS.connection_state_single_step st (sent_client_hello_state st ch raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (sent_client_hello_state st ch raw_sent);
  assert (CS.connection_state_evolves st (sent_client_hello_state st ch raw_sent));
  assert (CS.connection_state_consistent (sent_client_hello_state st ch raw_sent))

let lemma_derived_shared_secret_state_evolves
  (st:CS.connection_state)
  (shared:TLS13.Crypto.Spec.x25519_shared_secret)
  : Lemma
      (requires CS.connection_state_consistent st /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)))
      (ensures CS.connection_state_evolves
                 st
                 (derived_shared_secret_state st shared) /\
               CS.connection_state_consistent
                 (derived_shared_secret_state st shared) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (derived_shared_secret_state st shared))
=
  let ev = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.step_model st.CS.cs_model ev ==
          Some (derived_shared_secret_state st shared).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta st delta (derived_shared_secret_state st shared));
  assert (CS.connection_state_single_step st (derived_shared_secret_state st shared));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (derived_shared_secret_state st shared);
  assert (CS.connection_state_evolves st (derived_shared_secret_state st shared));
  assert (CS.connection_state_consistent (derived_shared_secret_state st shared))

let lemma_installed_traffic_keys_state_evolves
  (st:CS.connection_state)
  (install:CS.traffic_key_install)
  : Lemma
      (requires CS.connection_state_consistent st /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install)))
      (ensures CS.connection_state_evolves
                 st
                 (installed_traffic_keys_state st install) /\
               CS.connection_state_consistent
                 (installed_traffic_keys_state st install) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st install))
=
  let ev = CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.step_model st.CS.cs_model ev ==
          Some (installed_traffic_keys_state st install).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta st delta (installed_traffic_keys_state st install));
  assert (CS.connection_state_single_step st (installed_traffic_keys_state st install));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (installed_traffic_keys_state st install);
  assert (CS.connection_state_evolves st (installed_traffic_keys_state st install));
  assert (CS.connection_state_consistent (installed_traffic_keys_state st install))

let lemma_validated_certificate_state_evolves
  (st:CS.connection_state)
  (peer:X.peer_identity)
  : Lemma
      (requires CS.connection_state_consistent st /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalValidateCertificate peer)))
      (ensures CS.connection_state_evolves
                 st
                 (validated_certificate_state st peer) /\
               CS.connection_state_consistent
                 (validated_certificate_state st peer) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (validated_certificate_state st peer))
=
  let ev = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.step_model st.CS.cs_model ev ==
          Some (validated_certificate_state st peer).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta st delta (validated_certificate_state st peer));
  assert (CS.connection_state_single_step st (validated_certificate_state st peer));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (validated_certificate_state st peer);
  assert (CS.connection_state_evolves st (validated_certificate_state st peer));
  assert (CS.connection_state_consistent (validated_certificate_state st peer))

let lemma_client_handshake_traffic_install_legal
  (model:CS.connection_model)
  (handshake_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerHelloReceived /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
                  Some handshake_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material =
              CS.traffic_key_material_for_secret
                (K.client_handshake_traffic_secret
                  handshake_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))
=
  ()

let lemma_server_handshake_traffic_install_legal
  (model:CS.connection_model)
  (handshake_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerHelloReceived /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
                  Some handshake_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material =
              CS.traffic_key_material_for_secret
                (K.server_handshake_traffic_secret
                  handshake_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))
=
  ()

let lemma_client_application_traffic_install_legal
  (model:CS.connection_model)
  (master_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerFinishedVerified /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
                  Some master_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material =
              CS.traffic_key_material_for_secret
                (K.client_application_traffic_secret
                  master_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))
=
  ()

let lemma_server_application_traffic_install_legal
  (model:CS.connection_model)
  (master_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerFinishedVerified /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
                  Some master_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material =
              CS.traffic_key_material_for_secret
                (K.server_application_traffic_secret
                  master_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))
=
  ()

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

let lemma_received_server_hello_state_evolves
  (st:CS.connection_state)
  (sh:M.server_hello)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsClientHelloSent /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ServerHello sh);
                  }) /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ServerHello sh);
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_server_hello_state st sh raw_received) /\
               CS.connection_state_consistent
                 (received_server_hello_state st sh raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.ServerHello sh);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_server_hello_state st sh raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_server_hello_state st sh raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_server_hello_state st sh raw_received));
  assert (CS.connection_state_single_step
    st
    (received_server_hello_state st sh raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_server_hello_state st sh raw_received);
  assert (CS.connection_state_evolves
    st
    (received_server_hello_state st sh raw_received));
  assert (CS.connection_state_consistent
    (received_server_hello_state st sh raw_received))

let lemma_received_encrypted_extensions_state_evolves
  (st:CS.connection_state)
  (ee:M.encrypted_extensions)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerHelloReceived /\
                Some?
                  st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_encrypted_extensions_state st ee raw_received) /\
               CS.connection_state_consistent
                 (received_encrypted_extensions_state st ee raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_encrypted_extensions_state st ee raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_encrypted_extensions_state st ee raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_encrypted_extensions_state st ee raw_received));
  assert (CS.connection_state_single_step
    st
    (received_encrypted_extensions_state st ee raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_encrypted_extensions_state st ee raw_received);
  assert (CS.connection_state_evolves
    st
    (received_encrypted_extensions_state st ee raw_received));
  assert (CS.connection_state_consistent
    (received_encrypted_extensions_state st ee raw_received))

let lemma_received_certificate_state_evolves
  (st:CS.connection_state)
  (cert:M.certificate_msg)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
                cert.M.chain <> [] /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.Certificate cert);
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_certificate_state st cert raw_received) /\
               CS.connection_state_consistent
                 (received_certificate_state st cert raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.Certificate cert);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_certificate_state st cert raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Certificate cert);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_certificate_state st cert raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_certificate_state st cert raw_received));
  assert (CS.connection_state_single_step
    st
    (received_certificate_state st cert raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_certificate_state st cert raw_received);
  assert (CS.connection_state_evolves
    st
    (received_certificate_state st cert raw_received));
  assert (CS.connection_state_consistent
    (received_certificate_state st cert raw_received))

let lemma_received_certificate_verify_state_evolves
  (st:CS.connection_state)
  (cv:M.certificate_verify)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsCertificateValidated /\
                Some?
                  st.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_certificate_verify_state st cv raw_received) /\
               CS.connection_state_consistent
                 (received_certificate_verify_state st cv raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_certificate_verify_state st cv raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_certificate_verify_state st cv raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_certificate_verify_state st cv raw_received));
  assert (CS.connection_state_single_step
    st
    (received_certificate_verify_state st cv raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_certificate_verify_state st cv raw_received);
  assert (CS.connection_state_evolves
    st
    (received_certificate_verify_state st cv raw_received));
  assert (CS.connection_state_consistent
    (received_certificate_verify_state st cv raw_received))

let lemma_verified_certificate_signature_state_evolves
  (st:CS.connection_state)
  (cv:M.certificate_verify)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
                st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv)))
      (ensures CS.connection_state_evolves
                 st
                 (verified_certificate_signature_state st cv) /\
               CS.connection_state_consistent
                 (verified_certificate_signature_state st cv) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (verified_certificate_signature_state st cv))
=
  let ev = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.step_model st.CS.cs_model ev ==
          Some (verified_certificate_signature_state st cv).CS.cs_model);
  assert (CS.legal_connection_delta st delta (verified_certificate_signature_state st cv));
  assert (CS.connection_state_single_step st (verified_certificate_signature_state st cv));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (verified_certificate_signature_state st cv);
  assert (CS.connection_state_evolves st (verified_certificate_signature_state st cv));
  assert (CS.connection_state_consistent (verified_certificate_signature_state st cv))

let lemma_received_server_finished_state_evolves
  (st:CS.connection_state)
  (fin:M.finished)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
      CS.event_raw_delta_legal
        st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.Finished fin);
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_server_finished_state st fin raw_received) /\
               CS.connection_state_consistent
                 (received_server_finished_state st fin raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.Finished fin);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_server_finished_state st fin raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_server_finished_state st fin raw_received).CS.cs_model);
  assert (CS.legal_connection_delta st delta (received_server_finished_state st fin raw_received));
  assert (CS.connection_state_single_step st (received_server_finished_state st fin raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_server_finished_state st fin raw_received);
  assert (CS.connection_state_evolves st (received_server_finished_state st fin raw_received));
  assert (CS.connection_state_consistent (received_server_finished_state st fin raw_received))

let lemma_verified_server_finished_state_evolves
  (st:CS.connection_state)
  (fin:M.finished)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerFinishedReceived /\
                st.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some fin /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalVerifyFinished fin)))
      (ensures CS.connection_state_evolves
                 st
                 (verified_server_finished_state st fin) /\
               CS.connection_state_consistent
                 (verified_server_finished_state st fin) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalVerifyFinished fin);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (verified_server_finished_state st fin))
=
  let ev = CS.ConnLocalEvent (CS.LocalVerifyFinished fin) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.step_model st.CS.cs_model ev ==
          Some (verified_server_finished_state st fin).CS.cs_model);
  assert (CS.legal_connection_delta st delta (verified_server_finished_state st fin));
  assert (CS.connection_state_single_step st (verified_server_finished_state st fin));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (verified_server_finished_state st fin);
  assert (CS.connection_state_evolves st (verified_server_finished_state st fin));
  assert (CS.connection_state_consistent (verified_server_finished_state st fin))

let lemma_sent_client_finished_state_evolves
  (st:CS.connection_state)
  (fin:M.finished)
  (raw_sent:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_send_client_finished st fin raw_sent)
      (ensures CS.connection_state_evolves
                 st
                 (sent_client_finished_state st fin raw_sent) /\
               CS.connection_state_consistent
                 (sent_client_finished_state st fin raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.Finished fin);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_client_finished_state st fin raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_client_finished_state st fin raw_sent).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.legal_connection_delta st delta (sent_client_finished_state st fin raw_sent));
  assert (CS.connection_state_single_step st (sent_client_finished_state st fin raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (sent_client_finished_state st fin raw_sent);
  assert (CS.connection_state_evolves st (sent_client_finished_state st fin raw_sent));
  assert (CS.connection_state_consistent (sent_client_finished_state st fin raw_sent))

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

let lemma_sent_close_notify_state_evolves
  (st:CS.connection_state)
  (raw_sent:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_send_close_notify st raw_sent)
      (ensures CS.connection_state_evolves
                 st
                 (sent_close_notify_state st raw_sent) /\
               CS.connection_state_consistent
                 (sent_close_notify_state st raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsAlert T.CloseNotify;
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_close_notify_state st raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsAlert T.CloseNotify;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_close_notify_state st raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_close_notify_state st raw_sent));
  assert (CS.connection_state_single_step
    st
    (sent_close_notify_state st raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (sent_close_notify_state st raw_sent);
  assert (CS.connection_state_evolves
    st
    (sent_close_notify_state st raw_sent));
  assert (CS.connection_state_consistent
    (sent_close_notify_state st raw_sent))

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

let lemma_delivered_application_data_state_evolves
  (st:CS.connection_state)
  (bytes:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes)))
      (ensures CS.connection_state_evolves
                 st
                 (delivered_application_data_state st bytes) /\
               CS.connection_state_consistent
                 (delivered_application_data_state st bytes) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (delivered_application_data_state st bytes))
=
  let ev = CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (delivered_application_data_state st bytes).CS.cs_model);
  assert (CS.legal_connection_delta st delta (delivered_application_data_state st bytes));
  assert (CS.connection_state_single_step st (delivered_application_data_state st bytes));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (delivered_application_data_state st bytes);
  assert (CS.connection_state_evolves st (delivered_application_data_state st bytes));
  assert (CS.connection_state_consistent (delivered_application_data_state st bytes))

let lemma_sent_application_data_state_evolves
  (st:CS.connection_state)
  (bytes:B.bytes)
  (raw_sent:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_send_application_data st bytes raw_sent)
      (ensures CS.connection_state_evolves
                 st
                 (sent_application_data_state st bytes raw_sent) /\
               CS.connection_state_consistent
                 (sent_application_data_state st bytes raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsApplicationData bytes;
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_application_data_state st bytes raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsApplicationData bytes;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  lemma_application_data_record_count_small bytes;
  lemma_advance_direction_records_one st.CS.cs_model.CS.model_record.CS.record_write;
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_application_data_state st bytes raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta st delta (sent_application_data_state st bytes raw_sent));
  assert (CS.connection_state_single_step st (sent_application_data_state st bytes raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (sent_application_data_state st bytes raw_sent);
  assert (CS.connection_state_evolves st (sent_application_data_state st bytes raw_sent));
  assert (CS.connection_state_consistent (sent_application_data_state st bytes raw_sent))

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

fn get_control_snapshot
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns snapshot:control_snapshot
  ensures connection_exactly c st0 **
          pure (control_snapshot_matches snapshot st0)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  let control_tag = !c.control.control_tag;
  let handshake_stage_tag = !c.control.handshake_stage_tag;
  let failure_present = !c.control.failure_present;
  let failure_code = !c.control.failure_code;
  let failure_alert = !c.control.failure_alert;
  let snapshot = {
    snapshot_control_tag = control_tag;
    snapshot_handshake_stage_tag = handshake_stage_tag;
    snapshot_failure_present = failure_present;
    snapshot_failure_code = failure_code;
    snapshot_failure_alert = failure_alert;
  };
  assert (pure (control_snapshot_matches snapshot st0));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  snapshot
}

fn copy_certificate_leaf_der
  (c:connection_state)
  (out:array U8.t)
  (out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 max_handshake_flight_len <= SZ.v out_len /\
                 Some?
                   st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          connection_exactly c st0 **
          ArrPts.pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der with
                | Some leaf ->
                  SZ.v copied_len == B.length leaf /\
                  Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) leaf
                | None -> False))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  with parsed. _;

  let copied_len =
    copy_optional_sized_bytes_to_array
      c.handshake.buffers.certificate_leaf_der
      out
      out_len
      #(st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der);

  fold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  copied_len
}

fn copy_certificate_verify_input
  (c:connection_state)
  (out:array U8.t)
  (out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 max_certificate_verify_input_len <= SZ.v out_len /\
                 Some?
                   st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          connection_exactly c st0 **
          ArrPts.pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input with
                | Some input ->
                  SZ.v copied_len == B.length input /\
                  Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) input
                | None -> False))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  with parsed. _;

  let copied_len =
    copy_optional_sized_bytes_to_array
      c.handshake.buffers.certificate_verify_input
      out
      out_len
      #(st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);

  fold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  copied_len
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

fn can_start_handshake_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlNew /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_start == None)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start);

  let tag = !c.control.control_tag;
  let has_start = !c.handshake.start.present;
  with start_present.
    assert (Box.pts_to c.handshake.start.present start_present);
  assert (pure (has_start == start_present));

  let tag_ok = tag = 0uy;
  let start_empty = not has_start;
  let ok = tag_ok && start_empty;
  if ok {
    assert (pure (U8.v tag == 0));
    assert (pure (not start_present));
    assert (pure (start_present == false));
    rewrite (handshake_start_payload_exactly
      c.handshake.start
      start_present
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_payload_exactly
        c.handshake.start
        false
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    unfold (handshake_start_payload_exactly
      c.handshake.start
      false
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_start == None));
    fold (handshake_start_payload_exactly
      c.handshake.start
      false
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    fold (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlNew));
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    true
  } else {
    fold (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn try_start_handshake
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* start.
               connection_exactly c (started_handshake_state st0 start) **
               pure (can_start_handshake st0 start /\
                     CS.legal_connection_delta
                       st0
                       {
                         CS.delta_event =
                           CS.ConnLocalEvent (CS.LocalStartHandshake start);
                         CS.delta_raw_sent = B.empty;
                         CS.delta_raw_received = B.empty;
                       }
                       (started_handshake_state st0 start))
           else
             connection_exactly c st0)
{
  let ready = can_start_handshake_runtime c;
  if ready {
    assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlNew));
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_start == None));

    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);
    with role validation_time. _;
    unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
    with old_control_tag old_stage_tag old_failure_present old_failure_code old_failure_alert. _;
    unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    with cv_verified server_finished_verified. _;
    unfold (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    with old_start_present. _;
    let old_has_start = !c.handshake.start.present;
    assert (pure (old_has_start == old_start_present));
    if old_has_start {
      fold (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      fold (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure);
      fold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    } else {
    assert (pure (old_start_present == false));
    rewrite (handshake_start_payload_exactly
      c.handshake.start
      old_start_present
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_payload_exactly
        c.handshake.start
        false
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    unfold (handshake_start_payload_exactly
      c.handshake.start
      false
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    unfold (handshake_start_fields_allocated c.handshake.start);

    let mut client_random = [| 0uy; 32sz |];
    let random_ok = Crypto.random_bytes client_random 32sz;
    with client_random_bytes. assert (ArrPts.pts_to client_random client_random_bytes);
    assert (pure (B.length client_random_bytes == 32));

    let mut private_key = [| 0uy; 32sz |];
    let private_ok = Crypto.random_bytes private_key 32sz;
    with private_key_bytes. assert (ArrPts.pts_to private_key private_key_bytes);
    assert (pure (B.length private_key_bytes == 32));

    let entropy_ok = random_ok && private_ok;
    if entropy_ok {
    assert (pure random_ok);
    assert (pure private_ok);

    let mut public_key = [| 0uy; 32sz |];
    Crypto.x25519_public_from_private private_key public_key;
    with public_key_bytes. assert (ArrPts.pts_to public_key public_key_bytes);
    assert (pure (public_key_bytes ==
      TLS13.Crypto.Spec.x25519_public_from_private private_key_bytes));
    assert (pure (B.length public_key_bytes == 32));

    let start = Ghost.hide ({
      CS.start_server_name =
        st0.CS.cs_model.CS.model_config.CS.config_server_name;
      CS.start_client_random = client_random_bytes;
      CS.start_client_key_share_private = Some private_key_bytes;
      CS.start_client_key_share_public = public_key_bytes;
      CS.start_cipher_suites =
        st0.CS.cs_model.CS.model_config.CS.config_cipher_suites;
      CS.start_signature_schemes =
        st0.CS.cs_model.CS.model_config.CS.config_signature_schemes;
    });

    copy_hostname_sized_bytes
      c.config.server_name
      c.handshake.start.server_name;
    unfold (fixed_bytes_allocated c.handshake.start.client_random 32);
    with old_start_random. assert (V.pts_to c.handshake.start.client_random old_start_random);
    copy_fixed32_array_to_vec
      client_random
      c.handshake.start.client_random;
    fold (fixed_bytes_exactly
      c.handshake.start.client_random
      32
      client_random_bytes);
    lemma_len32_refinement_tautology();
    assert (pure (Some? (Ghost.reveal start).CS.start_client_key_share_private));
    assert (pure (Some?.v (Ghost.reveal start).CS.start_client_key_share_private == private_key_bytes));
    unfold (optional_fixed_bytes_exactly
      c.handshake.start.client_key_share_private
      32
      None);
    with old_private_present old_private_storage. _;
    copy_fixed32_array_to_vec
      private_key
      c.handshake.start.client_key_share_private.bytes;
    c.handshake.start.client_key_share_private.present := true;
    with stored_private. assert (V.pts_to c.handshake.start.client_key_share_private.bytes stored_private);
    assert (pure (stored_private == private_key_bytes));
    assert (pure ((Ghost.reveal start).CS.start_client_key_share_private == Some stored_private));
    assert (pure (optional_fixed_bytes_match
      true
      stored_private
      32
      (Ghost.reveal start).CS.start_client_key_share_private));
    fold (optional_fixed_bytes_exactly
      c.handshake.start.client_key_share_private
      32
      (Ghost.reveal start).CS.start_client_key_share_private);
    unfold (fixed_bytes_allocated c.handshake.start.client_key_share_public 32);
    with old_start_public. assert (V.pts_to c.handshake.start.client_key_share_public old_start_public);
    copy_fixed32_array_to_vec
      public_key
      c.handshake.start.client_key_share_public;
    fold (fixed_bytes_exactly
      c.handshake.start.client_key_share_public
      32
      public_key_bytes);
    assert (pure (SZ.fits max_cipher_suites));
    copy_cipher_suite_list_storage
      c.config.cipher_suites
      c.handshake.start.cipher_suites
      max_cipher_suites
      #(st0.CS.cs_model.CS.model_config.CS.config_cipher_suites);
    assert (pure (SZ.fits max_signature_schemes));
    copy_signature_scheme_list_storage
      c.config.signature_schemes
      c.handshake.start.signature_schemes
      max_signature_schemes
      #(st0.CS.cs_model.CS.model_config.CS.config_signature_schemes);

    assert (pure (CS.start_matches_config
      st0.CS.cs_model.CS.model_config
      (Ghost.reveal start)));
    assert (pure (CS.handshake_start_key_share_consistent (Ghost.reveal start)));
    assert (pure (can_start_handshake st0 (Ghost.reveal start)));
    lemma_option_some_v (Ghost.reveal start).CS.start_client_key_share_private;
    assert (pure ((Ghost.reveal start).CS.start_client_key_share_private ==
      Some (Some?.v (Ghost.reveal start).CS.start_client_key_share_private)));
    assert (pure (Some (Some?.v (Ghost.reveal start).CS.start_client_key_share_private) ==
      (Ghost.reveal start).CS.start_client_key_share_private));

    c.handshake.start.present := true;
    fold (handshake_start_fields_exactly
      c.handshake.start
      (Ghost.reveal start));
    fold (handshake_start_payload_exactly
      c.handshake.start
      true
      (Some (Ghost.reveal start)));
    fold (handshake_start_exactly
      c.handshake.start
      (Some (Ghost.reveal start)));

    c.control.control_tag := 1uy;
    c.control.handshake_stage_tag := 1uy;
    fold (control_exactly
      c.control
      (CS.ControlHandshaking CS.HsStarted)
      st0.CS.cs_model.CS.model_failure);

    fold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys));
    unfold (handshake_messages_exactly
      c.handshake.messages
      st0.CS.cs_model.CS.model_handshake);
    fold (handshake_messages_exactly
      c.handshake.messages
      (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake);
    unfold (server_key_share_exactly
      c.handshake.server_key_share
      st0.CS.cs_model.CS.model_handshake);
    fold (server_key_share_exactly
      c.handshake.server_key_share
      (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake);
    rewrite (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
      as (peer_exactly
        c.handshake.validated_peer
        (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    rewrite (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
      as (sized_bytes_exactly
        c.handshake.transcript
        max_transcript_len
        (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
    rewrite (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
      as (handshake_buffers_exactly
        c.handshake.buffers
        (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
    rewrite (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
      as (key_schedule_exactly
        c.handshake.keys
        (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (handshake_exactly
      c.handshake
      (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake);
    fold (connection_model_exactly
      c
      (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model);

    lemma_started_handshake_state_evolves st0 (Ghost.reveal start);
    MR.update c.ghost_state (started_handshake_state st0 (Ghost.reveal start));
    fold (connection_exactly c (started_handshake_state st0 (Ghost.reveal start)));
    true
    } else {
      fold (handshake_start_fields_allocated c.handshake.start);
      fold (handshake_start_payload_exactly
        c.handshake.start
        false
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      fold (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure);
      fold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    }
    }
  } else {
    false
  }
}

fn can_send_client_hello_runtime
  (c:connection_state)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsStarted /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_start /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
              <= max_transcript_len - max_client_hello_len /\
            517 <= SZ.v network_out_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (client_hello_slot_exactly
    c.handshake.messages.client_hello_present
    c.handshake.messages.client_hello
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  with ch_present ch_random ch_server_name ch_key_share
       ch_cipher_suites ch_signature_schemes.
    assert (pure True);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let has_start = !c.handshake.start.present;
  let has_client_hello = !c.handshake.messages.client_hello_present;
  let transcript_len = !c.handshake.transcript.len;
  with start_present. assert (Box.pts_to c.handshake.start.present start_present);
  assert (Box.pts_to c.handshake.messages.client_hello_present ch_present);
  assert (pure (has_start == start_present));
  assert (pure (has_client_hello == ch_present));
  assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript == SZ.v transcript_len));

  assert (pure (SZ.fits (max_transcript_len - max_client_hello_len)));
  let transcript_bound = SZ.uint_to_t (max_transcript_len - max_client_hello_len);
  let transcript_room = sizet_lte_plain transcript_len transcript_bound;
  lemma_sizet_lte_plain transcript_len transcript_bound;
  let out_room = sizet_lte_plain 517sz network_out_len;
  lemma_sizet_lte_plain 517sz network_out_len;
  let ok =
    (tag = 1uy) &&
    (stage = 1uy) &&
    has_start &&
    (not has_client_hello) &&
    transcript_room &&
    out_room;
  if ok {
    assert (pure (U8.v tag == 1));
    assert (pure (U8.v stage == 1));
    assert (pure (start_present == true));
    assert (pure (ch_present == false));
    assert (pure (SZ.v transcript_len <= max_transcript_len - max_client_hello_len));
    assert (pure (517 <= SZ.v network_out_len));
    rewrite (handshake_start_payload_exactly
      c.handshake.start
      start_present
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_payload_exactly
        c.handshake.start
        true
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    unfold (handshake_start_payload_exactly
      c.handshake.start
      true
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    with start_spec. assert (pure True);
    fold (handshake_start_payload_exactly
      c.handshake.start
      true
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    rewrite (handshake_start_payload_exactly
      c.handshake.start
      true
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_payload_exactly
        c.handshake.start
        start_present
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None));
    fold (client_hello_slot_exactly
      c.handshake.messages.client_hello_present
      c.handshake.messages.client_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    assert (pure (st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsStarted));
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    true
  } else {
    fold (client_hello_slot_exactly
      c.handshake.messages.client_hello_present
      c.handshake.messages.client_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn try_send_client_hello
  (c:connection_state)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'old_network_out == SZ.v network_out_len)
  returns written: option (n:SZ.t{SZ.v n <= SZ.v network_out_len})
  ensures (match written with
           | Some n ->
             exists* ch raw_sent network_out_bytes.
               connection_exactly c (sent_client_hello_state st0 ch raw_sent) **
               ArrPts.pts_to network_out network_out_bytes **
               pure (B.length network_out_bytes == SZ.v network_out_len /\
                     5 <= SZ.v n /\
                     SZ.v n <= B.length network_out_bytes /\
                     can_send_client_hello st0 ch raw_sent /\
                     Seq.equal raw_sent (Seq.slice network_out_bytes 0 (SZ.v n)))
           | None ->
             connection_exactly c st0 **
             ArrPts.pts_to network_out 'old_network_out)
{
  let ready = can_send_client_hello_runtime c network_out_len;
  if ready {
    assert (pure (st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsStarted));
    assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_start));
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None));
    assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      <= max_transcript_len - max_client_hello_len));
    assert (pure (517 <= SZ.v network_out_len));

    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    with old_control_tag old_stage_tag old_failure_present
         old_failure_code old_failure_alert. _;
    assert (pure (st0.CS.cs_model.CS.model_failure == None));
    unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    with cv_verified server_finished_verified. _;

    unfold (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    with start_present. _;
    let has_start = !c.handshake.start.present;
    assert (pure (has_start == start_present));
    if has_start {
    assert (pure (start_present == true));
    rewrite (handshake_start_payload_exactly
      c.handshake.start
      start_present
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_payload_exactly
        c.handshake.start
        true
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    unfold (handshake_start_payload_exactly
      c.handshake.start
      true
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    with start_spec. _;
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_start ==
      Some start_spec));
    unfold (handshake_start_fields_exactly c.handshake.start start_spec);
    unfold (sized_bytes_exactly
      c.handshake.start.server_name
      max_hostname_len
      start_spec.CS.start_server_name);
    with old_start_server_name old_start_server_name_len. _;
    unfold (fixed_bytes_exactly
      c.handshake.start.client_random
      32
      start_spec.CS.start_client_random);
    with old_start_random. _;
    unfold (fixed_bytes_exactly
      c.handshake.start.client_key_share_public
      32
      start_spec.CS.start_client_key_share_public);
    with old_start_key_share. _;
    unfold (cipher_suite_list_exactly
      c.handshake.start.cipher_suites
      max_cipher_suites
      start_spec.CS.start_cipher_suites);
    with old_start_cipher_suites old_start_cipher_suites_len. _;
    unfold (signature_scheme_list_exactly
      c.handshake.start.signature_schemes
      max_signature_schemes
      start_spec.CS.start_signature_schemes);
    with old_start_signature_schemes old_start_signature_schemes_len. _;

    unfold (handshake_messages_exactly
      c.handshake.messages
      st0.CS.cs_model.CS.model_handshake);
    unfold (client_hello_slot_exactly
      c.handshake.messages.client_hello_present
      c.handshake.messages.client_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    with old_client_hello_present old_l_random old_l_server_name
         old_l_key_share old_l_cipher_suites old_l_signature_schemes. _;
    assert (pure (old_client_hello_present == false));

    unfold (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
    with parsed. _;
    unfold (sized_bytes_exactly
      c.handshake.buffers.client_hello_bytes
      max_client_hello_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_client_hello_bytes);
    with old_client_hello_bytes old_client_hello_bytes_len. _;

    let start = Ghost.hide start_spec;
    assert (pure (Ghost.reveal start == start_spec));
    let ch = Ghost.hide (client_hello_of_start (Ghost.reveal start));
    assert (pure (Ghost.reveal ch == client_hello_of_start start_spec));
    lemma_client_hello_of_start_matches (Ghost.reveal start);
    assert (pure (CS.client_hello_matches_start start_spec (Ghost.reveal ch)));

    let written =
      Ser.serialize_client_hello_from_start
        #start
        #ch
        c.handshake.start.client_random
        c.handshake.start.server_name.bytes
        c.handshake.start.server_name.len
        c.handshake.start.client_key_share_public
        c.handshake.start.cipher_suites.items
        c.handshake.start.cipher_suites.len
        c.handshake.start.signature_schemes.items
        c.handshake.start.signature_schemes.len
        c.handshake.messages.client_hello_present
        c.handshake.messages.client_hello
        c.handshake.buffers.client_hello_bytes.bytes
        c.handshake.buffers.client_hello_bytes.len
        network_out
        network_out_len;
    with random server_name server_name_len key_share
         cipher_suites cipher_suites_len
         signature_schemes signature_schemes_len
         handshake_bytes network_out_bytes handshake_len. _;

    assert (pure (B.length network_out_bytes == SZ.v network_out_len));
    assert (pure (SZ.v written <= B.length network_out_bytes));
    assert (pure (5 <= SZ.v written));
    assert (pure (Seq.equal
      (CL.raw_slice network_out_bytes 0 (SZ.v written))
      (CS.serialized_cleartext_tls_message
        (M.TlsHandshake (M.ClientHello (Ghost.reveal ch))))));
    assert (pure (CL.raw_slice network_out_bytes 0 (SZ.v written) ==
      Seq.slice network_out_bytes 0 (SZ.v written)));
    let raw_sent = Ghost.hide (Seq.slice network_out_bytes 0 (SZ.v written));
    assert (pure (Seq.equal
      (Ghost.reveal raw_sent)
      (Seq.slice network_out_bytes 0 (SZ.v written))));
    assert (pure (Seq.equal
      (Ghost.reveal raw_sent)
      (CS.serialized_cleartext_tls_message
        (M.TlsHandshake (M.ClientHello (Ghost.reveal ch))))));
    Seq.lemma_eq_intro B.empty B.empty;
    assert (pure (CS.event_raw_delta_legal
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello (Ghost.reveal ch));
      })
      (Ghost.reveal raw_sent)
      B.empty));

    assert (pure (SZ.v handshake_len ==
      B.length (W.serialize_handshake (M.ClientHello (Ghost.reveal ch)))));
    assert (pure (SZ.v handshake_len <= max_client_hello_len));
    assert (pure (SZ.v (server_name_len) <= B.length server_name));
    lemma_client_hello_len_helpers_from_start
      start_spec
      (Ghost.reveal ch)
      server_name
      server_name_len
      cipher_suites
      cipher_suites_len
      signature_schemes
      signature_schemes_len;

    assert (pure (CL.raw_slice server_name 0 (SZ.v server_name_len) ==
      Seq.slice server_name 0 (SZ.v server_name_len)));
    assert (pure (byte_prefix_matches
      server_name
      server_name_len
      start_spec.CS.start_server_name));
    fold (sized_bytes_exactly
      c.handshake.start.server_name
      max_hostname_len
      start_spec.CS.start_server_name);
    fold (fixed_bytes_exactly
      c.handshake.start.client_random
      32
      start_spec.CS.start_client_random);
    fold (fixed_bytes_exactly
      c.handshake.start.client_key_share_public
      32
      start_spec.CS.start_client_key_share_public);
    fold (cipher_suite_list_exactly
      c.handshake.start.cipher_suites
      max_cipher_suites
      start_spec.CS.start_cipher_suites);
    fold (signature_scheme_list_exactly
      c.handshake.start.signature_schemes
      max_signature_schemes
      start_spec.CS.start_signature_schemes);
    fold (handshake_start_fields_exactly c.handshake.start start_spec);
    fold (handshake_start_payload_exactly
      c.handshake.start
      true
      (Some start_spec));
    fold (handshake_start_exactly
      c.handshake.start
      (Some start_spec));

    assert (pure (CS.client_hello_matches_start start_spec (Ghost.reveal ch)));
    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello (Ghost.reveal ch));
      })));
    assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
      B.length (W.serialize_handshake (M.ClientHello (Ghost.reveal ch))) <=
      max_transcript_len));
    assert (pure (can_send_client_hello
      st0
      (Ghost.reveal ch)
      (Ghost.reveal raw_sent)));

    unfold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    with old_transcript_storage old_transcript_len. _;
    let transcript_len = !c.handshake.transcript.len;
    let handshake_len_runtime = !c.handshake.buffers.client_hello_bytes.len;
    assert (pure (transcript_len == old_transcript_len));
    assert (pure (handshake_len_runtime == handshake_len));
    assert (pure (SZ.v transcript_len ==
      B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    assert (pure (SZ.v transcript_len + SZ.v handshake_len_runtime <= max_transcript_len));
    copy_client_hello_prefix_to_transcript
      c.handshake.buffers.client_hello_bytes.bytes
      c.handshake.transcript.bytes
      handshake_len_runtime
      transcript_len;
    with copied_client_hello_bytes copied_transcript_storage.
      assert (V.pts_to c.handshake.buffers.client_hello_bytes.bytes copied_client_hello_bytes **
              V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
    assert (pure (copied_client_hello_bytes == handshake_bytes));
    assert (pure (SZ.fits (SZ.v transcript_len + SZ.v handshake_len_runtime)));
    let new_transcript_len = SZ.add transcript_len handshake_len_runtime;
    c.handshake.transcript.len := new_transcript_len;

    assert (pure (CL.raw_slice handshake_bytes 0 (SZ.v handshake_len) ==
      Seq.slice handshake_bytes 0 (SZ.v handshake_len)));
    assert (pure (byte_prefix_matches
      handshake_bytes
      handshake_len
      (W.serialize_handshake (M.ClientHello (Ghost.reveal ch)))));
    fold (sized_bytes_exactly
      c.handshake.buffers.client_hello_bytes
      max_client_hello_len
      (W.serialize_handshake (M.ClientHello (Ghost.reveal ch))));
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (B.append
        st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
        (W.serialize_handshake (M.ClientHello (Ghost.reveal ch)))));

    fold (client_hello_slot_exactly
      c.handshake.messages.client_hello_present
      c.handshake.messages.client_hello
      (Some (Ghost.reveal ch)));
    fold (handshake_messages_exactly
      c.handshake.messages
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);

    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_start ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_start));
    rewrite (handshake_start_exactly
      c.handshake.start
      (Some start_spec))
      as (handshake_start_exactly
        c.handshake.start
        (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_start);
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
    unfold (server_key_share_exactly
      c.handshake.server_key_share
      st0.CS.cs_model.CS.model_handshake);
    fold (server_key_share_exactly
      c.handshake.server_key_share
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
    rewrite (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
      as (peer_exactly
        c.handshake.validated_peer
        (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_client_hello_bytes ==
      W.serialize_handshake (M.ClientHello (Ghost.reveal ch))));
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes));
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes));
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed));
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der));
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input));
    fold (handshake_buffers_exactly
      c.handshake.buffers
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys));
    rewrite (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
      as (key_schedule_exactly
        c.handshake.keys
        (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_keys);
    assert (pure (cv_verified ==
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
    assert (pure (server_finished_verified ==
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
    fold (handshake_exactly
      c.handshake
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);

    c.control.control_tag := 1uy;
    c.control.handshake_stage_tag := 2uy;
    c.control.failure_present := false;
    c.control.failure_code := 0uy;
    c.control.failure_alert := 0uy;
    assert (pure (control_state_matches
      1uy
      2uy
      false
      0uy
      0uy
      (CS.ControlHandshaking CS.HsClientHelloSent)));
    fold (control_exactly
      c.control
      (CS.ControlHandshaking CS.HsClientHelloSent)
      st0.CS.cs_model.CS.model_failure);

    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config ==
      st0.CS.cs_model.CS.model_config));
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record ==
      st0.CS.cs_model.CS.model_record));
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application ==
      st0.CS.cs_model.CS.model_application));
    rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
      as (connection_config_exactly
        c.config
        (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config);
    rewrite (record_layer_exactly c.records st0.CS.cs_model.CS.model_record)
      as (record_layer_exactly
        c.records
        (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record);
    rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
      as (application_exactly
        c.application
        (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application);
    fold (connection_model_exactly
      c
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model);

    lemma_sent_client_hello_state_evolves
      st0
      (Ghost.reveal ch)
      (Ghost.reveal raw_sent);
    MR.update
      c.ghost_state
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent));
    fold (connection_exactly
      c
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)));
    Some written
    } else {
      fold (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      fold (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      None
    }
  } else {
    None
  }
}

fn can_receive_server_hello
  (c:connection_state)
  (#sh:erased M.server_hello)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloSent /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              B.length (W.serialize_handshake (M.ServerHello sh)) <=
              max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ServerHello sh);
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (server_hello_slot_exactly
    c.handshake.messages.server_hello
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 2uy;

  with start_present. assert (pure True);
  let has_start = !c.handshake.start.present;
  assert (pure (has_start == start_present));

  with stored_server_hello. assert (pure True);
  let stored = !c.handshake.messages.server_hello;
  let no_server_hello = (
    match stored with
    | None -> true
    | Some _ -> false);
  assert (pure (stored == stored_server_hello));
  assert (pure (no_server_hello ==> stored == None));
  assert (pure (no_server_hello ==> stored_server_hello == None));
  assert (pure (no_server_hello ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None));

  with transcript_storage transcript_len. assert (pure True);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  W.lemma_serialize_server_hello_len sh;
  assert (pure (B.length (W.serialize_handshake (M.ServerHello sh)) == 90));
  assert (pure (SZ.fits (max_transcript_len - 90)));
  let max_start = SZ.uint_to_t (max_transcript_len - 90);
  let transcript_room = SZ.lte current_transcript_len max_start;

  if has_start {
    unfold (handshake_start_payload_exactly
      c.handshake.start
      has_start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    with start_spec. assert (pure True);
    unfold (handshake_start_fields_exactly c.handshake.start start_spec);
        unfold (cipher_suite_list_exactly
          c.handshake.start.cipher_suites
          max_cipher_suites
          start_spec.CS.start_cipher_suites);
        with cipher_items cipher_len. assert (pure True);
        let offered_len = !c.handshake.start.cipher_suites.len;
        assert (pure (offered_len == cipher_len));
        let offered_nonempty = SZ.gt offered_len 0sz;
        if offered_nonempty {
          assert (pure (SZ.v cipher_len > 0));
          assert (pure (SZ.v offered_len == SZ.v cipher_len));
          assert (pure (start_spec.CS.start_cipher_suites <> []));
          lemma_nonempty_cipher_suites_offer
            start_spec.CS.start_cipher_suites
            sh.M.cipher_suite;
          assert (pure (CS.cipher_suite_offered
            start_spec.CS.start_cipher_suites
            sh.M.cipher_suite));
          assert (pure (H.is_supported_cipher_suite sh.M.cipher_suite));

          let control_ok = tag_ok && stage_ok;
          let ok = control_ok && no_server_hello && transcript_room;
          assert (pure (ok ==> U8.v tag == 1));
          assert (pure (ok ==> U8.v stage == 2));
          assert (pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloSent));
          assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None));
          assert (pure (ok ==> SZ.v current_transcript_len <= max_transcript_len - 90));
          assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
            SZ.v current_transcript_len));
          assert (pure (ok ==>
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              B.length (W.serialize_handshake (M.ServerHello sh)) <=
              max_transcript_len));
          assert (pure (ok ==> CS.legal_event
            st0.CS.cs_model
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            })));

          fold (cipher_suite_list_exactly
            c.handshake.start.cipher_suites
            max_cipher_suites
            start_spec.CS.start_cipher_suites);
          fold (handshake_start_fields_exactly c.handshake.start start_spec);
          fold (handshake_start_payload_exactly
            c.handshake.start
            has_start
            st0.CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (sized_bytes_exactly
            c.handshake.transcript
            max_transcript_len
            st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
          fold (server_hello_slot_exactly
            c.handshake.messages.server_hello
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
          fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
          fold (handshake_start_exactly
            c.handshake.start
            st0.CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
          fold (control_exactly
            c.control
            st0.CS.cs_model.CS.model_control
            st0.CS.cs_model.CS.model_failure);
          fold (connection_model_exactly c st0.CS.cs_model);
          fold (connection_exactly c st0);
          ok
        } else {
          fold (cipher_suite_list_exactly
            c.handshake.start.cipher_suites
            max_cipher_suites
            start_spec.CS.start_cipher_suites);
          fold (handshake_start_fields_exactly c.handshake.start start_spec);
          fold (handshake_start_payload_exactly
            c.handshake.start
            has_start
            st0.CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (sized_bytes_exactly
            c.handshake.transcript
            max_transcript_len
            st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
          fold (server_hello_slot_exactly
            c.handshake.messages.server_hello
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
          fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
          fold (handshake_start_exactly
            c.handshake.start
            st0.CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
          fold (control_exactly
            c.control
            st0.CS.cs_model.CS.model_control
            st0.CS.cs_model.CS.model_failure);
          fold (connection_model_exactly c st0.CS.cs_model);
          fold (connection_exactly c st0);
          false
        }
  } else {
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (server_hello_slot_exactly
      c.handshake.messages.server_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
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

fn can_deliver_application_data
  (c:connection_state)
  (payload_len:SZ.t)
  (app_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            SZ.v payload_len <= SZ.v app_out_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  let tag = !c.control.control_tag;
  let control_ok = tag = 2uy;
  let output_ok = sizet_lte_plain payload_len app_out_len;
  lemma_sizet_lte_plain payload_len app_out_len;
  let ok = control_ok && output_ok;

  assert (pure (ok ==> U8.v tag == 2));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (ok ==> SZ.v payload_len <= SZ.v app_out_len));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn try_derive_shared_secret
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* shared.
               connection_exactly c (derived_shared_secret_state st0 shared) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (derived_shared_secret_state st0 shared))
           else
             connection_exactly c st0)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (server_key_share_exactly
    c.handshake.server_key_share
    st0.CS.cs_model.CS.model_handshake);
  unfold (optional_fixed_bytes_exactly
    c.handshake.server_key_share
    32
    (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
     | Some sh -> Some sh.M.key_share
     | None -> None));
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 3uy;

  with start_present. assert (pure True);
  let has_start = !c.handshake.start.present;
  assert (pure (has_start == start_present));

  let has_server_share = !c.handshake.server_key_share.present;
  with server_share_present.
    assert (Box.pts_to c.handshake.server_key_share.present server_share_present);
  with server_share_storage.
    assert (V.pts_to c.handshake.server_key_share.bytes server_share_storage);
  let server_share_storage_e = Ghost.hide server_share_storage;
  assert (pure (has_server_share == server_share_present));

  let ready = tag_ok && stage_ok && has_start && has_server_share;

  if ready {
    assert (pure (U8.v tag == 1));
    assert (pure (U8.v stage == 3));
    assert (pure has_start);
    assert (pure has_server_share);
    assert (pure server_share_present);
    lemma_optional_fixed_bytes_match_some
      server_share_present
      server_share_storage
      32
      (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
       | Some sh -> Some sh.M.key_share
       | None -> None);
    lemma_server_key_share_option_some
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello
      server_share_storage;
    let sh = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
    assert (pure (st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerHelloReceived));
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some (Ghost.reveal sh)));
    assert (pure (server_share_storage == (Ghost.reveal sh).M.key_share));

    if has_start {
    unfold (handshake_start_payload_exactly
      c.handshake.start
      has_start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    with start_spec. assert (pure True);
    unfold (handshake_start_fields_exactly c.handshake.start start_spec);
    lemma_len32_refinement_tautology();
    unfold (optional_fixed_bytes_exactly
      c.handshake.start.client_key_share_private
      32
      start_spec.CS.start_client_key_share_private);

    with private_present private_storage. _;
    let private_storage_e = Ghost.hide private_storage;
    let has_private = !c.handshake.start.client_key_share_private.present;
    assert (pure (has_private == private_present));

    if has_private {
      assert (pure private_present);
      lemma_optional_fixed_bytes_match_some
        private_present
        (Ghost.reveal private_storage_e)
        32
        start_spec.CS.start_client_key_share_private;
      assert (pure (start_spec.CS.start_client_key_share_private == Some (Ghost.reveal private_storage_e)));
      let private_spec = private_storage_e;
      assert (pure (B.length (Ghost.reveal private_storage_e) == 32));
      assert (pure (B.length (Ghost.reveal server_share_storage_e) == 32));
      lemma_len32_refinement_tautology();

        V.to_array_pts_to c.handshake.start.client_key_share_private.bytes;
        V.to_array_pts_to c.handshake.server_key_share.bytes;
        let mut shared_out = [| 0uy; 32sz |];
        let crypto_ok =
          Crypto.x25519_shared_runtime
            (V.vec_to_array c.handshake.start.client_key_share_private.bytes)
            (V.vec_to_array c.handshake.server_key_share.bytes)
            shared_out;
        V.to_vec_pts_to c.handshake.start.client_key_share_private.bytes;
        V.to_vec_pts_to c.handshake.server_key_share.bytes;

        if crypto_ok {
          with shared. assert (ArrPts.pts_to shared_out shared);
          ArrPts.pts_to_len shared_out;
          assert (pure (B.length shared == 32));
          assert (pure (Crypto.x25519_shared_call (Ghost.reveal private_storage_e) (Ghost.reveal server_share_storage_e) shared crypto_ok));
          Crypto.lemma_x25519_shared_call_success (Ghost.reveal private_storage_e) (Ghost.reveal server_share_storage_e) shared crypto_ok;
          assert (pure (Some? (TLS13.Crypto.Spec.x25519_shared (Ghost.reveal private_storage_e) (Ghost.reveal server_share_storage_e))));
          assert (pure (Some?.v (TLS13.Crypto.Spec.x25519_shared (Ghost.reveal private_storage_e) (Ghost.reveal server_share_storage_e)) == shared));
          let shared_secret = Ghost.hide (Some?.v (TLS13.Crypto.Spec.x25519_shared (Ghost.reveal private_storage_e) (Ghost.reveal server_share_storage_e)));
          assert (pure (Ghost.reveal shared_secret == shared));
          assert (pure (TLS13.Crypto.Spec.x25519_shared (Ghost.reveal private_storage_e) (Ghost.reveal server_share_storage_e) == Some (Ghost.reveal shared_secret)));
          assert (pure (TLS13.Crypto.Spec.x25519_shared (Ghost.reveal private_spec) (Ghost.reveal sh).M.key_share == Some (Ghost.reveal shared_secret)));
          assert (pure (CS.legal_event
            st0.CS.cs_model
            (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret (Ghost.reveal shared_secret)))));

          let mut early_out = [| 0uy; 32sz |];
          KS.early_secret_empty early_out;
          let mut handshake_out = [| 0uy; 32sz |];
          KS.handshake_secret early_out shared_out 32sz handshake_out;
          let mut master_out = [| 0uy; 32sz |];
          KS.master_secret handshake_out master_out;

          store_optional_secret c.handshake.keys.shared_secret shared_out #shared_secret;
          store_optional_secret
            c.handshake.keys.early_secret
            early_out
            #(K.early_secret B.empty);
          store_optional_secret
            c.handshake.keys.handshake_secret
            handshake_out
            #(K.handshake_secret (K.early_secret B.empty) (Ghost.reveal shared_secret));
          store_optional_secret
            c.handshake.keys.master_secret
            master_out
            #(K.master_secret (K.handshake_secret (K.early_secret B.empty) (Ghost.reveal shared_secret)));

          fold (key_schedule_exactly
            c.handshake.keys
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_handshake.CS.hs_keys);

          fold (optional_fixed_bytes_exactly
            c.handshake.start.client_key_share_private
            32
            start_spec.CS.start_client_key_share_private);
          fold (handshake_start_fields_exactly c.handshake.start start_spec);
          fold (handshake_start_payload_exactly
            c.handshake.start
            has_start
            st0.CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (handshake_start_exactly
            c.handshake.start
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (optional_fixed_bytes_exactly
            c.handshake.server_key_share
            32
            (match (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_handshake.CS.hs_server_hello with
             | Some sh -> Some sh.M.key_share
             | None -> None));
          fold (server_key_share_exactly
            c.handshake.server_key_share
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_handshake);
          fold (handshake_messages_exactly
            c.handshake.messages
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_handshake);
          fold (handshake_exactly
            c.handshake
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_handshake);
          fold (control_exactly
            c.control
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_control
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_failure);
          fold (connection_model_exactly
            c
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model);

          lemma_derived_shared_secret_state_evolves st0 (Ghost.reveal shared_secret);
          MR.update c.ghost_state (derived_shared_secret_state st0 (Ghost.reveal shared_secret));
          fold (connection_exactly c (derived_shared_secret_state st0 (Ghost.reveal shared_secret)));
          true
        } else {
          with shared_old. assert (ArrPts.pts_to shared_out shared_old);
          fold (optional_fixed_bytes_exactly
            c.handshake.start.client_key_share_private
            32
            start_spec.CS.start_client_key_share_private);
          fold (handshake_start_fields_exactly c.handshake.start start_spec);
          fold (handshake_start_payload_exactly
            c.handshake.start
            has_start
            st0.CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (handshake_start_exactly
            c.handshake.start
            st0.CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (optional_fixed_bytes_exactly
            c.handshake.server_key_share
            32
            (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
             | Some sh -> Some sh.M.key_share
             | None -> None));
          fold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
          fold (key_schedule_exactly
            c.handshake.keys
            st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
          fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
          fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
          fold (control_exactly
            c.control
            st0.CS.cs_model.CS.model_control
            st0.CS.cs_model.CS.model_failure);
          fold (connection_model_exactly c st0.CS.cs_model);
          fold (connection_exactly c st0);
          false
        }
    } else {
      fold (optional_fixed_bytes_exactly
        c.handshake.start.client_key_share_private
        32
        start_spec.CS.start_client_key_share_private);
      fold (handshake_start_fields_exactly c.handshake.start start_spec);
      fold (handshake_start_payload_exactly
        c.handshake.start
        has_start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (optional_fixed_bytes_exactly
        c.handshake.server_key_share
        32
        (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
         | Some sh -> Some sh.M.key_share
         | None -> None));
      fold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
      fold (key_schedule_exactly c.handshake.keys st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
      fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      fold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    }
    } else {
      fold (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (optional_fixed_bytes_exactly
        c.handshake.server_key_share
        32
        (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
         | Some sh -> Some sh.M.key_share
         | None -> None));
      fold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
      fold (key_schedule_exactly c.handshake.keys st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
      fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      fold (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    }
  } else {
      fold (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (optional_fixed_bytes_exactly
        c.handshake.server_key_share
        32
        (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
         | Some sh -> Some sh.M.key_share
         | None -> None));
      fold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
      fold (key_schedule_exactly c.handshake.keys st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
      fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_install_handshake_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerHelloReceived /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (optional_secret_exactly
    c.handshake.keys.handshake_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let present = !c.handshake.keys.handshake_secret.present;
  with stored_present.
    assert (Box.pts_to c.handshake.keys.handshake_secret.present stored_present);
  with stored_secret.
    assert (V.pts_to c.handshake.keys.handshake_secret.secret stored_secret);
  assert (pure (present == stored_present));

  let ok = (tag = 1uy) && (stage = 3uy) && present;
  if ok {
    assert (pure (U8.v tag == 1));
    assert (pure (U8.v stage == 3));
    assert (pure stored_present);
    lemma_optional_fixed_bytes_match_some
      stored_present
      stored_secret
      32
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret;
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret));
    assert (pure (st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerHelloReceived));
    fold (optional_secret_exactly
      c.handshake.keys.handshake_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    true
  } else {
    fold (optional_secret_exactly
      c.handshake.keys.handshake_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_install_application_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerFinishedVerified /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let present = !c.handshake.keys.master_secret.present;
  with stored_present.
    assert (Box.pts_to c.handshake.keys.master_secret.present stored_present);
  with stored_secret.
    assert (V.pts_to c.handshake.keys.master_secret.secret stored_secret);
  assert (pure (present == stored_present));

  let ok = (tag = 1uy) && (stage = 10uy) && present;
  if ok {
    assert (pure (U8.v tag == 1));
    assert (pure (U8.v stage == 10));
    assert (pure stored_present);
    lemma_optional_fixed_bytes_match_some
      stored_present
      stored_secret
      32
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret;
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret));
    assert (pure (st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerFinishedVerified));
    fold (optional_secret_exactly
      c.handshake.keys.master_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    true
  } else {
    fold (optional_secret_exactly
      c.handshake.keys.master_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn try_install_client_handshake_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* material.
               connection_exactly c
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficHandshake;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = material;
                 }) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent
                       (CS.LocalInstallTrafficKeys {
                         CS.install_epoch = CS.TrafficHandshake;
                         CS.install_direction = CS.TrafficWrite;
                         CS.install_material = material;
                       });
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficHandshake;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = material;
                 }))
           else
             connection_exactly c st0)
{
  let ready = can_install_handshake_traffic_keys c;
  if ready {
    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
    unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    unfold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    unfold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    unfold (optional_secret_exactly
      c.handshake.keys.handshake_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);

    with transcript_storage.
      assert (V.pts_to c.handshake.transcript.bytes transcript_storage);
    with transcript_len.
      assert (Box.pts_to c.handshake.transcript.len transcript_len);
    let transcript_len_runtime = !c.handshake.transcript.len;
    assert (pure (transcript_len_runtime == transcript_len));
    with hs_present.
      assert (Box.pts_to c.handshake.keys.handshake_secret.present hs_present);
    with hs_secret_storage.
      assert (V.pts_to c.handshake.keys.handshake_secret.secret hs_secret_storage);
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret));
    lemma_optional_fixed_bytes_match_present_of_some
      hs_present
      hs_secret_storage
      32
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret;
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
      Some hs_secret_storage));
    let hs_secret = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
    assert (pure (Ghost.reveal hs_secret == hs_secret_storage));

    assert (pure (byte_prefix_matches
      transcript_storage
      transcript_len_runtime
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    assert (pure (Seq.equal
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
    Seq.lemma_eq_intro
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

    V.to_array_pts_to c.handshake.transcript.bytes;
    let mut transcript_hash = [| 0uy; 32sz |];
    Crypto.sha256_prefix
      (V.vec_to_array c.handshake.transcript.bytes)
      transcript_len_runtime
      transcript_hash;
    V.to_vec_pts_to c.handshake.transcript.bytes;
    with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
    assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

    V.to_array_pts_to c.handshake.keys.handshake_secret.secret;
    let mut traffic_secret_out = [| 0uy; 32sz |];
    KS.client_handshake_traffic_secret
      (V.vec_to_array c.handshake.keys.handshake_secret.secret)
      transcript_hash
      traffic_secret_out;
    V.to_vec_pts_to c.handshake.keys.handshake_secret.secret;
    with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
    assert (pure (traffic_secret_bytes ==
      K.client_handshake_traffic_secret
        (Ghost.reveal hs_secret)
        (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

    let mut traffic_key_out = [| 0uy; 32sz |];
    KS.derive_traffic_key traffic_secret_out traffic_key_out;
    let mut traffic_iv_out = [| 0uy; 12sz |];
    KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
    with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
    with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

    let traffic_secret = Ghost.hide traffic_secret_bytes;
    let material = Ghost.hide (CS.traffic_key_material_for_secret (Ghost.reveal traffic_secret));
    assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));
    let install = Ghost.hide ({
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = Ghost.reveal material;
    });

    lemma_client_handshake_traffic_install_legal
      st0.CS.cs_model
      (Ghost.reveal hs_secret);
    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys (Ghost.reveal install)))));

    store_traffic_key_material
      c.handshake.keys.client_handshake_traffic
      traffic_secret_out
      traffic_key_out
      traffic_iv_out
      #material;
    fold (optional_secret_exactly
      c.handshake.keys.handshake_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_keys);

    Rec.install_handshake_keys_runtime c.records.write traffic_key_out traffic_iv_out;
    assert (pure ((Ghost.reveal install).CS.install_epoch == CS.TrafficHandshake));
    assert (pure ((Ghost.reveal install).CS.install_direction == CS.TrafficWrite));
    assert (pure ((Ghost.reveal install).CS.install_material == Ghost.reveal material));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read ==
      st0.CS.cs_model.CS.model_record.CS.record_read));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write ==
      R.install_keys
        st0.CS.cs_model.CS.model_record.CS.record_write
        R.Handshake
        (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv));
    rewrite (Rec.is_record_state c.records.read st0.CS.cs_model.CS.model_record.CS.record_read)
      as (Rec.is_record_state
        c.records.read
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read);
    rewrite (Rec.is_record_state
      c.records.write
      (R.install_keys
        st0.CS.cs_model.CS.model_record.CS.record_write
        R.Handshake
        (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv))
      as (Rec.is_record_state
        c.records.write
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write);
    fold (record_layer_exactly
      c.records
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record);

    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_start));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    rewrite (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_exactly
        c.handshake.start
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start);
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
    unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_messages_exactly
      c.handshake.messages
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
    fold (server_key_share_exactly
      c.handshake.server_key_share
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    rewrite (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
      as (peer_exactly
        c.handshake.validated_peer
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    rewrite (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
      as (handshake_buffers_exactly
        c.handshake.buffers
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_exactly
      c.handshake
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_failure);
    fold (connection_model_exactly
      c
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model);

    lemma_installed_traffic_keys_state_evolves st0 (Ghost.reveal install);
    assert (pure (CS.connection_state_evolves
      st0
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    assert (pure (CS.connection_state_consistent
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    MR.update c.ghost_state (installed_traffic_keys_state st0 (Ghost.reveal install));
    fold (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)));
    assert (pure (Ghost.reveal install == {
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = Ghost.reveal material;
    }));
    rewrite (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)))
      as (connection_exactly c (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = Ghost.reveal material;
      }));
    assert (pure (CS.legal_connection_delta
      st0
      {
        CS.delta_event =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = Ghost.reveal material;
            });
        CS.delta_raw_sent = B.empty;
        CS.delta_raw_received = B.empty;
      }
      (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = Ghost.reveal material;
      })));
    true
  } else {
    false
  }
}

fn try_install_server_handshake_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* material.
               connection_exactly c
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficHandshake;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = material;
                 }) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent
                       (CS.LocalInstallTrafficKeys {
                         CS.install_epoch = CS.TrafficHandshake;
                         CS.install_direction = CS.TrafficRead;
                         CS.install_material = material;
                       });
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficHandshake;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = material;
                 }))
           else
             connection_exactly c st0)
{
  let ready = can_install_handshake_traffic_keys c;
  if ready {
    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
    unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    unfold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    unfold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    unfold (optional_secret_exactly
      c.handshake.keys.handshake_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);

    with transcript_storage.
      assert (V.pts_to c.handshake.transcript.bytes transcript_storage);
    with transcript_len.
      assert (Box.pts_to c.handshake.transcript.len transcript_len);
    let transcript_len_runtime = !c.handshake.transcript.len;
    assert (pure (transcript_len_runtime == transcript_len));
    with hs_present.
      assert (Box.pts_to c.handshake.keys.handshake_secret.present hs_present);
    with hs_secret_storage.
      assert (V.pts_to c.handshake.keys.handshake_secret.secret hs_secret_storage);
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret));
    lemma_optional_fixed_bytes_match_present_of_some
      hs_present
      hs_secret_storage
      32
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret;
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
      Some hs_secret_storage));
    let hs_secret = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
    assert (pure (Ghost.reveal hs_secret == hs_secret_storage));

    assert (pure (byte_prefix_matches
      transcript_storage
      transcript_len_runtime
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    assert (pure (Seq.equal
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
    Seq.lemma_eq_intro
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

    V.to_array_pts_to c.handshake.transcript.bytes;
    let mut transcript_hash = [| 0uy; 32sz |];
    Crypto.sha256_prefix
      (V.vec_to_array c.handshake.transcript.bytes)
      transcript_len_runtime
      transcript_hash;
    V.to_vec_pts_to c.handshake.transcript.bytes;
    with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
    assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

    V.to_array_pts_to c.handshake.keys.handshake_secret.secret;
    let mut traffic_secret_out = [| 0uy; 32sz |];
    KS.server_handshake_traffic_secret
      (V.vec_to_array c.handshake.keys.handshake_secret.secret)
      transcript_hash
      traffic_secret_out;
    V.to_vec_pts_to c.handshake.keys.handshake_secret.secret;
    with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
    assert (pure (traffic_secret_bytes ==
      K.server_handshake_traffic_secret
        (Ghost.reveal hs_secret)
        (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

    let mut traffic_key_out = [| 0uy; 32sz |];
    KS.derive_traffic_key traffic_secret_out traffic_key_out;
    let mut traffic_iv_out = [| 0uy; 12sz |];
    KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
    with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
    with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

    let traffic_secret = Ghost.hide traffic_secret_bytes;
    let material = Ghost.hide (CS.traffic_key_material_for_secret (Ghost.reveal traffic_secret));
    assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));
    let install = Ghost.hide ({
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = Ghost.reveal material;
    });

    lemma_server_handshake_traffic_install_legal
      st0.CS.cs_model
      (Ghost.reveal hs_secret);
    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys (Ghost.reveal install)))));

    store_traffic_key_material
      c.handshake.keys.server_handshake_traffic
      traffic_secret_out
      traffic_key_out
      traffic_iv_out
      #material;
    fold (optional_secret_exactly
      c.handshake.keys.handshake_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_keys);

    Rec.install_handshake_keys_runtime c.records.read traffic_key_out traffic_iv_out;
    assert (pure ((Ghost.reveal install).CS.install_epoch == CS.TrafficHandshake));
    assert (pure ((Ghost.reveal install).CS.install_direction == CS.TrafficRead));
    assert (pure ((Ghost.reveal install).CS.install_material == Ghost.reveal material));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write ==
      st0.CS.cs_model.CS.model_record.CS.record_write));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read ==
      R.install_keys
        st0.CS.cs_model.CS.model_record.CS.record_read
        R.Handshake
        (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv));
    rewrite (Rec.is_record_state c.records.write st0.CS.cs_model.CS.model_record.CS.record_write)
      as (Rec.is_record_state
        c.records.write
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write);
    rewrite (Rec.is_record_state
      c.records.read
      (R.install_keys
        st0.CS.cs_model.CS.model_record.CS.record_read
        R.Handshake
        (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv))
      as (Rec.is_record_state
        c.records.read
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read);
    fold (record_layer_exactly
      c.records
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record);

    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_start));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    rewrite (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_exactly
        c.handshake.start
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start);
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
    unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_messages_exactly
      c.handshake.messages
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
    fold (server_key_share_exactly
      c.handshake.server_key_share
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    rewrite (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
      as (peer_exactly
        c.handshake.validated_peer
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    rewrite (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
      as (handshake_buffers_exactly
        c.handshake.buffers
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_exactly
      c.handshake
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_failure);
    fold (connection_model_exactly
      c
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model);

    lemma_installed_traffic_keys_state_evolves st0 (Ghost.reveal install);
    assert (pure (CS.connection_state_evolves
      st0
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    assert (pure (CS.connection_state_consistent
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    MR.update c.ghost_state (installed_traffic_keys_state st0 (Ghost.reveal install));
    fold (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)));
    assert (pure (Ghost.reveal install == {
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = Ghost.reveal material;
    }));
    rewrite (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)))
      as (connection_exactly c (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = Ghost.reveal material;
      }));
    assert (pure (CS.legal_connection_delta
      st0
      {
        CS.delta_event =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = Ghost.reveal material;
            });
        CS.delta_raw_sent = B.empty;
        CS.delta_raw_received = B.empty;
      }
      (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = Ghost.reveal material;
      })));
    true
  } else {
    false
  }
}

fn try_install_client_application_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* material.
               connection_exactly c
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = material;
                 }) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent
                       (CS.LocalInstallTrafficKeys {
                         CS.install_epoch = CS.TrafficApplication;
                         CS.install_direction = CS.TrafficWrite;
                         CS.install_material = material;
                       });
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = material;
                 }))
           else
             connection_exactly c st0)
{
  let ready = can_install_application_traffic_keys c;
  if ready {
    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
    unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    unfold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    unfold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    unfold (optional_secret_exactly
      c.handshake.keys.master_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);

    with transcript_storage.
      assert (V.pts_to c.handshake.transcript.bytes transcript_storage);
    with transcript_len.
      assert (Box.pts_to c.handshake.transcript.len transcript_len);
    let transcript_len_runtime = !c.handshake.transcript.len;
    assert (pure (transcript_len_runtime == transcript_len));
    with ms_present.
      assert (Box.pts_to c.handshake.keys.master_secret.present ms_present);
    with ms_secret_storage.
      assert (V.pts_to c.handshake.keys.master_secret.secret ms_secret_storage);
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret));
    lemma_optional_fixed_bytes_match_present_of_some
      ms_present
      ms_secret_storage
      32
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret;
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
      Some ms_secret_storage));
    let ms_secret = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
    assert (pure (Ghost.reveal ms_secret == ms_secret_storage));

    assert (pure (byte_prefix_matches
      transcript_storage
      transcript_len_runtime
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    assert (pure (Seq.equal
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
    Seq.lemma_eq_intro
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

    V.to_array_pts_to c.handshake.transcript.bytes;
    let mut transcript_hash = [| 0uy; 32sz |];
    Crypto.sha256_prefix
      (V.vec_to_array c.handshake.transcript.bytes)
      transcript_len_runtime
      transcript_hash;
    V.to_vec_pts_to c.handshake.transcript.bytes;
    with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
    assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

    V.to_array_pts_to c.handshake.keys.master_secret.secret;
    let mut traffic_secret_out = [| 0uy; 32sz |];
    KS.client_application_traffic_secret
      (V.vec_to_array c.handshake.keys.master_secret.secret)
      transcript_hash
      traffic_secret_out;
    V.to_vec_pts_to c.handshake.keys.master_secret.secret;
    with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
    assert (pure (traffic_secret_bytes ==
      K.client_application_traffic_secret
        (Ghost.reveal ms_secret)
        (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

    let mut traffic_key_out = [| 0uy; 32sz |];
    KS.derive_traffic_key traffic_secret_out traffic_key_out;
    let mut traffic_iv_out = [| 0uy; 12sz |];
    KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
    with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
    with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

    let traffic_secret = Ghost.hide traffic_secret_bytes;
    let material = Ghost.hide (CS.traffic_key_material_for_secret (Ghost.reveal traffic_secret));
    assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));
    let install = Ghost.hide ({
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = Ghost.reveal material;
    });

    lemma_client_application_traffic_install_legal
      st0.CS.cs_model
      (Ghost.reveal ms_secret);
    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys (Ghost.reveal install)))));

    store_traffic_key_material
      c.handshake.keys.client_application_traffic
      traffic_secret_out
      traffic_key_out
      traffic_iv_out
      #material;
    fold (optional_secret_exactly
      c.handshake.keys.master_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_keys);

    assert (pure ((Ghost.reveal install).CS.install_epoch == CS.TrafficApplication));
    assert (pure ((Ghost.reveal install).CS.install_direction == CS.TrafficWrite));
    assert (pure ((Ghost.reveal install).CS.install_material == Ghost.reveal material));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read ==
      st0.CS.cs_model.CS.model_record.CS.record_read));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write ==
      st0.CS.cs_model.CS.model_record.CS.record_write));
    rewrite (Rec.is_record_state c.records.read st0.CS.cs_model.CS.model_record.CS.record_read)
      as (Rec.is_record_state
        c.records.read
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read);
    rewrite (Rec.is_record_state c.records.write st0.CS.cs_model.CS.model_record.CS.record_write)
      as (Rec.is_record_state
        c.records.write
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write);
    fold (record_layer_exactly
      c.records
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record);

    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_start));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    rewrite (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_exactly
        c.handshake.start
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start);
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
    unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_messages_exactly
      c.handshake.messages
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
    fold (server_key_share_exactly
      c.handshake.server_key_share
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    rewrite (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
      as (peer_exactly
        c.handshake.validated_peer
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    rewrite (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
      as (handshake_buffers_exactly
        c.handshake.buffers
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_exactly
      c.handshake
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_failure);
    fold (connection_model_exactly
      c
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model);

    lemma_installed_traffic_keys_state_evolves st0 (Ghost.reveal install);
    assert (pure (CS.connection_state_evolves
      st0
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    assert (pure (CS.connection_state_consistent
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    MR.update c.ghost_state (installed_traffic_keys_state st0 (Ghost.reveal install));
    fold (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)));
    assert (pure (Ghost.reveal install == {
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = Ghost.reveal material;
    }));
    rewrite (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)))
      as (connection_exactly c (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = Ghost.reveal material;
      }));
    assert (pure (CS.legal_connection_delta
      st0
      {
        CS.delta_event =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = Ghost.reveal material;
            });
        CS.delta_raw_sent = B.empty;
        CS.delta_raw_received = B.empty;
      }
      (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = Ghost.reveal material;
      })));
    true
  } else {
    false
  }
}

fn try_install_server_application_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* material.
               connection_exactly c
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = material;
                 }) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent
                       (CS.LocalInstallTrafficKeys {
                         CS.install_epoch = CS.TrafficApplication;
                         CS.install_direction = CS.TrafficRead;
                         CS.install_material = material;
                       });
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = material;
                 }))
           else
             connection_exactly c st0)
{
  let ready = can_install_application_traffic_keys c;
  if ready {
    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
    unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    unfold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    unfold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    unfold (optional_secret_exactly
      c.handshake.keys.master_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);

    with transcript_storage.
      assert (V.pts_to c.handshake.transcript.bytes transcript_storage);
    with transcript_len.
      assert (Box.pts_to c.handshake.transcript.len transcript_len);
    let transcript_len_runtime = !c.handshake.transcript.len;
    assert (pure (transcript_len_runtime == transcript_len));
    with ms_present.
      assert (Box.pts_to c.handshake.keys.master_secret.present ms_present);
    with ms_secret_storage.
      assert (V.pts_to c.handshake.keys.master_secret.secret ms_secret_storage);
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret));
    lemma_optional_fixed_bytes_match_present_of_some
      ms_present
      ms_secret_storage
      32
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret;
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
      Some ms_secret_storage));
    let ms_secret = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
    assert (pure (Ghost.reveal ms_secret == ms_secret_storage));

    assert (pure (byte_prefix_matches
      transcript_storage
      transcript_len_runtime
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    assert (pure (Seq.equal
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
    Seq.lemma_eq_intro
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

    V.to_array_pts_to c.handshake.transcript.bytes;
    let mut transcript_hash = [| 0uy; 32sz |];
    Crypto.sha256_prefix
      (V.vec_to_array c.handshake.transcript.bytes)
      transcript_len_runtime
      transcript_hash;
    V.to_vec_pts_to c.handshake.transcript.bytes;
    with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
    assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

    V.to_array_pts_to c.handshake.keys.master_secret.secret;
    let mut traffic_secret_out = [| 0uy; 32sz |];
    KS.server_application_traffic_secret
      (V.vec_to_array c.handshake.keys.master_secret.secret)
      transcript_hash
      traffic_secret_out;
    V.to_vec_pts_to c.handshake.keys.master_secret.secret;
    with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
    assert (pure (traffic_secret_bytes ==
      K.server_application_traffic_secret
        (Ghost.reveal ms_secret)
        (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

    let mut traffic_key_out = [| 0uy; 32sz |];
    KS.derive_traffic_key traffic_secret_out traffic_key_out;
    let mut traffic_iv_out = [| 0uy; 12sz |];
    KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
    with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
    with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

    let traffic_secret = Ghost.hide traffic_secret_bytes;
    let material = Ghost.hide (CS.traffic_key_material_for_secret (Ghost.reveal traffic_secret));
    assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));
    let install = Ghost.hide ({
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = Ghost.reveal material;
    });

    lemma_server_application_traffic_install_legal
      st0.CS.cs_model
      (Ghost.reveal ms_secret);
    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys (Ghost.reveal install)))));

    store_traffic_key_material
      c.handshake.keys.server_application_traffic
      traffic_secret_out
      traffic_key_out
      traffic_iv_out
      #material;
    fold (optional_secret_exactly
      c.handshake.keys.master_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_keys);

    Rec.install_application_keys_runtime c.records.read traffic_key_out traffic_iv_out;
    assert (pure ((Ghost.reveal install).CS.install_epoch == CS.TrafficApplication));
    assert (pure ((Ghost.reveal install).CS.install_direction == CS.TrafficRead));
    assert (pure ((Ghost.reveal install).CS.install_material == Ghost.reveal material));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write ==
      st0.CS.cs_model.CS.model_record.CS.record_write));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read ==
      R.install_keys
        st0.CS.cs_model.CS.model_record.CS.record_read
        R.Application
        (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv));
    rewrite (Rec.is_record_state c.records.write st0.CS.cs_model.CS.model_record.CS.record_write)
      as (Rec.is_record_state
        c.records.write
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write);
    rewrite (Rec.is_record_state
      c.records.read
      (R.install_keys
        st0.CS.cs_model.CS.model_record.CS.record_read
        R.Application
        (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv))
      as (Rec.is_record_state
        c.records.read
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read);
    fold (record_layer_exactly
      c.records
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record);

    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_start));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    rewrite (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_exactly
        c.handshake.start
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start);
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
    unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_messages_exactly
      c.handshake.messages
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
    fold (server_key_share_exactly
      c.handshake.server_key_share
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    rewrite (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
      as (peer_exactly
        c.handshake.validated_peer
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    rewrite (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
      as (handshake_buffers_exactly
        c.handshake.buffers
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_exactly
      c.handshake
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_failure);
    fold (connection_model_exactly
      c
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model);

    lemma_installed_traffic_keys_state_evolves st0 (Ghost.reveal install);
    assert (pure (CS.connection_state_evolves
      st0
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    assert (pure (CS.connection_state_consistent
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    MR.update c.ghost_state (installed_traffic_keys_state st0 (Ghost.reveal install));
    fold (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)));
    assert (pure (Ghost.reveal install == {
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = Ghost.reveal material;
    }));
    rewrite (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)))
      as (connection_exactly c (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = Ghost.reveal material;
      }));
    assert (pure (CS.legal_connection_delta
      st0
      {
        CS.delta_event =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = Ghost.reveal material;
            });
        CS.delta_raw_sent = B.empty;
        CS.delta_raw_received = B.empty;
      }
      (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = Ghost.reveal material;
      })));
    true
  } else {
    false
  }
}

fn can_receive_encrypted_extensions
  (c:connection_state)
  (#ee:erased M.encrypted_extensions)
  (fragment_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerHelloReceived /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v fragment_len <= max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (encrypted_extensions_slot_exactly
    c.handshake.messages.encrypted_extensions
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 3uy;

  with stored_ee. assert (Box.pts_to c.handshake.messages.encrypted_extensions stored_ee);
  let stored = !c.handshake.messages.encrypted_extensions;
  let no_encrypted_extensions = (
    match stored with
    | None -> true
    | Some _ -> false);
  assert (pure (stored == stored_ee));
  assert (pure (no_encrypted_extensions ==> stored == None));
  assert (pure (no_encrypted_extensions ==> stored_ee == None));
  assert (pure (no_encrypted_extensions ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == None));

  with transcript_storage transcript_len. assert (pure True);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  with server_hs_present.
    assert (Box.pts_to c.handshake.keys.server_handshake_traffic.present server_hs_present);
  with server_hs_secret.
    assert (V.pts_to c.handshake.keys.server_handshake_traffic.traffic_secret server_hs_secret);
  with server_hs_key.
    assert (V.pts_to c.handshake.keys.server_handshake_traffic.traffic_key server_hs_key);
  with server_hs_iv.
    assert (V.pts_to c.handshake.keys.server_handshake_traffic.traffic_iv server_hs_iv);
  let has_server_handshake_keys = !c.handshake.keys.server_handshake_traffic.present;
  assert (pure (has_server_handshake_keys == server_hs_present));

  let seq_ok = Rec.can_advance_seq c.records.read;

  assert (pure (SZ.fits max_transcript_len));
  let max_len = SZ.uint_to_t max_transcript_len;
  let fragment_fits = SZ.lte fragment_len max_len;
  if fragment_fits {
    let max_start = SZ.sub max_len fragment_len;
    let transcript_room = sizet_lte_plain current_transcript_len max_start;
    lemma_sizet_lte_plain current_transcript_len max_start;

    let control_ok = tag_ok && stage_ok;
    let ok =
      control_ok &&
      no_encrypted_extensions &&
      has_server_handshake_keys &&
      seq_ok &&
      transcript_room;

    assert (pure (ok ==> U8.v tag == 1));
    assert (pure (ok ==> U8.v stage == 3));
    assert (pure (ok ==>
      st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerHelloReceived));
    assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == None));
    assert (pure (ok ==> server_hs_present));
    assert (pure (ok ==> Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
    assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
    assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      SZ.v current_transcript_len));
    assert (pure (ok ==> SZ.v current_transcript_len <= SZ.v max_start));
    assert (pure (ok ==> SZ.v current_transcript_len + SZ.v fragment_len <= max_transcript_len));
    assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
      SZ.v fragment_len <= max_transcript_len));
    assert (pure (ok ==> CS.legal_event
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      })));

    fold (traffic_key_material_exactly
      c.handshake.keys.server_handshake_traffic
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (encrypted_extensions_slot_exactly
      c.handshake.messages.encrypted_extensions
      st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    ok
  } else {
    fold (traffic_key_material_exactly
      c.handshake.keys.server_handshake_traffic
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (encrypted_extensions_slot_exactly
      c.handshake.messages.encrypted_extensions
      st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_receive_certificate
  (c:connection_state)
  (lcert:IM.certificate_msg)
  (#cert:erased M.certificate_msg)
  (fragment_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           IM.is_valid_certificate_msg lcert cert
  returns ok: bool
  ensures connection_exactly c st0 **
          IM.is_valid_certificate_msg lcert cert **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
            (Ghost.reveal cert).M.chain <> [] /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v fragment_len <= max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_slot_exactly
    c.handshake.messages.certificate
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  unfold (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_leaf_der
    max_handshake_flight_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der);
  unfold (IM.is_valid_certificate_msg lcert (Ghost.reveal cert));

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 4uy;

  with stored_cert. assert (Box.pts_to c.handshake.messages.certificate stored_cert);
  let stored = !c.handshake.messages.certificate;
  let no_certificate = (
    match stored with
    | None -> true
    | Some _ -> false);
  assert (pure (stored == stored_cert));
  assert (pure (no_certificate ==> stored == None));
  assert (pure (no_certificate ==> stored_cert == None));
  assert (pure (no_certificate ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None));

  with transcript_storage transcript_len. assert (pure True);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  with parsed leaf_present leaf_storage leaf_len. assert (pure True);
  let leaf_present_runtime = !c.handshake.buffers.certificate_leaf_der.present;
  let no_leaf = not leaf_present_runtime;
  assert (pure (leaf_present_runtime == leaf_present));
  assert (pure (no_leaf ==> not leaf_present));
  assert (pure (no_leaf ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None));

  let seq_ok = Rec.can_advance_seq c.records.read;

  with chain_bytes offsets lens. assert (pure True);
  let cert_count = lcert.IM.certificate_msg_cert_count;
  let cert_count_nat = SZ.v cert_count;
  let chain_bytes_len_nat = SZ.v lcert.IM.certificate_msg_chain_bytes_len;
  let has_certificate = SZ.gt cert_count 0sz;

  assert (pure (SZ.fits max_transcript_len));
  let max_len = SZ.uint_to_t max_transcript_len;
  let fragment_fits = SZ.lte fragment_len max_len;
  if fragment_fits {
    let max_start = SZ.sub max_len fragment_len;
    let transcript_room = sizet_lte_plain current_transcript_len max_start;
    lemma_sizet_lte_plain current_transcript_len max_start;

    if has_certificate {
      assert (pure has_certificate);
      assert (pure (cert_count_nat > 0));
      assert (pure ((Ghost.reveal cert).M.chain <> []));
      let control_ok = tag_ok && stage_ok;
      let ok =
        control_ok &&
        no_certificate &&
        no_leaf &&
        seq_ok &&
        transcript_room;

      assert (pure (ok ==> U8.v tag == 1));
      assert (pure (ok ==> U8.v stage == 4));
      assert (pure (ok ==>
        st0.CS.cs_model.CS.model_control ==
          CS.ControlHandshaking CS.HsEncryptedExtensionsReceived));
      assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None));
      assert (pure (ok ==>
        st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None));
      assert (pure (ok ==> (Ghost.reveal cert).M.chain <> []));
      assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
      assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
        SZ.v current_transcript_len));
      assert (pure (ok ==> SZ.v current_transcript_len <= SZ.v max_start));
      assert (pure (ok ==> SZ.v current_transcript_len + SZ.v fragment_len <= max_transcript_len));
      assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
        SZ.v fragment_len <= max_transcript_len));
      assert (pure (ok ==> CS.legal_event
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
        })));

      fold (IM.is_valid_certificate_msg lcert (Ghost.reveal cert));
      fold (sized_bytes_exactly
        c.handshake.transcript
        max_transcript_len
        st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
      fold (optional_sized_bytes_exactly
        c.handshake.buffers.certificate_leaf_der
        max_handshake_flight_len
        st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der);
      fold (handshake_buffers_exactly
        c.handshake.buffers
        st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
      fold (certificate_slot_exactly
        c.handshake.messages.certificate
        st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
      fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
      fold (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      ok
    } else {
      fold (IM.is_valid_certificate_msg lcert (Ghost.reveal cert));
      fold (sized_bytes_exactly
        c.handshake.transcript
        max_transcript_len
        st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
      fold (optional_sized_bytes_exactly
        c.handshake.buffers.certificate_leaf_der
        max_handshake_flight_len
        st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der);
      fold (handshake_buffers_exactly
        c.handshake.buffers
        st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
      fold (certificate_slot_exactly
        c.handshake.messages.certificate
        st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
      fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
      fold (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    }
  } else {
    fold (IM.is_valid_certificate_msg lcert (Ghost.reveal cert));
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (optional_sized_bytes_exactly
      c.handshake.buffers.certificate_leaf_der
      max_handshake_flight_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der);
    fold (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
    fold (certificate_slot_exactly
      c.handshake.messages.certificate
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_validate_certificate
  (c:connection_state)
  (payload_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsCertificateReceived /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None /\
            SZ.v payload_len <= max_public_key_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 5uy;

  with peer_present peer_hostname peer_hostname_len peer_public_key peer_public_key_len peer_schemes peer_schemes_len.
    assert (pure True);
  let stored_peer_present = !c.handshake.validated_peer.present;
  let no_peer = not stored_peer_present;
  assert (pure (stored_peer_present == peer_present));
  assert (pure (no_peer ==> not peer_present));
  assert (pure (no_peer ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None));

  assert (pure (SZ.fits max_public_key_len));
  let max_pk_len = SZ.uint_to_t max_public_key_len;
  let payload_fits = SZ.lte payload_len max_pk_len;
  let ok = tag_ok && stage_ok && no_peer && payload_fits;

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 5));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsCertificateReceived));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None));
  assert (pure (ok ==> SZ.v payload_len <= max_public_key_len));

  fold (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_receive_certificate_verify
  (c:connection_state)
  (#cv:erased M.certificate_verify)
  (fragment_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsCertificateValidated /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v fragment_len <= max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  unfold (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  unfold (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_verify_input
    max_certificate_verify_input_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 6uy;

  with stored_cv. assert (Box.pts_to c.handshake.messages.certificate_verify stored_cv);
  let stored = !c.handshake.messages.certificate_verify;
  let no_cv = (
    match stored with
    | None -> true
    | Some _ -> false);
  assert (pure (stored == stored_cv));
  assert (pure (no_cv ==> stored == None));
  assert (pure (no_cv ==> stored_cv == None));
  assert (pure (no_cv ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None));

  with peer_present peer_hostname peer_hostname_len peer_public_key peer_public_key_len peer_schemes peer_schemes_len.
    assert (pure True);
  let peer_is_present = !c.handshake.validated_peer.present;
  assert (pure (peer_is_present == peer_present));
  assert (pure (peer_is_present ==> peer_present));
  assert (pure (peer_is_present ==>
    Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));

  with transcript_storage transcript_len. assert (pure True);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  with parsed cv_input_present cv_input_storage cv_input_len. assert (pure True);
  let stored_cv_input_present = !c.handshake.buffers.certificate_verify_input.present;
  let no_cv_input = not stored_cv_input_present;
  assert (pure (stored_cv_input_present == cv_input_present));
  assert (pure (no_cv_input ==> not cv_input_present));
  assert (pure (no_cv_input ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None));

  let seq_ok = Rec.can_advance_seq c.records.read;

  assert (pure (SZ.fits max_transcript_len));
  let max_len = SZ.uint_to_t max_transcript_len;
  let fragment_fits = SZ.lte fragment_len max_len;
  if fragment_fits {
    let max_start = SZ.sub max_len fragment_len;
    let transcript_room = sizet_lte_plain current_transcript_len max_start;
    lemma_sizet_lte_plain current_transcript_len max_start;

    let control_ok = tag_ok && stage_ok;
    let ok =
      control_ok &&
      no_cv &&
      peer_is_present &&
      no_cv_input &&
      seq_ok &&
      transcript_room;

    assert (pure (ok ==> U8.v tag == 1));
    assert (pure (ok ==> U8.v stage == 6));
    assert (pure (ok ==>
      st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsCertificateValidated));
    assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None));
    assert (pure (ok ==>
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None));
    assert (pure (ok ==> Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
    assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
    assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      SZ.v current_transcript_len));
    assert (pure (ok ==> SZ.v current_transcript_len <= SZ.v max_start));
    assert (pure (ok ==> SZ.v current_transcript_len + SZ.v fragment_len <= max_transcript_len));
    assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
      SZ.v fragment_len <= max_transcript_len));
    assert (pure (ok ==> CS.legal_event
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
      })));

    fold (optional_sized_bytes_exactly
      c.handshake.buffers.certificate_verify_input
      max_certificate_verify_input_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);
    fold (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    fold (certificate_verify_slot_exactly
      c.handshake.messages.certificate_verify
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    ok
  } else {
    fold (optional_sized_bytes_exactly
      c.handshake.buffers.certificate_verify_input
      max_certificate_verify_input_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);
    fold (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    fold (certificate_verify_slot_exactly
      c.handshake.messages.certificate_verify
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_verify_certificate_signature
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. assert (pure True);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  unfold (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  unfold (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_verify_input
    max_certificate_verify_input_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 7uy;

  with stored_cv. assert (Box.pts_to c.handshake.messages.certificate_verify stored_cv);
  let stored = !c.handshake.messages.certificate_verify;
  let has_cv = (
    match stored with
    | Some _ -> true
    | None -> false);
  assert (pure (stored == stored_cv));
  assert (pure (has_cv ==>
    option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)));

  with peer_present peer_hostname peer_hostname_len peer_public_key peer_public_key_len peer_schemes peer_schemes_len.
    assert (pure True);
  let peer_is_present = !c.handshake.validated_peer.present;
  assert (pure (peer_is_present == peer_present));
  assert (pure (peer_is_present ==>
    option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)));

  with parsed input_present input_storage input_len. assert (pure True);
  let cv_input_present = !c.handshake.buffers.certificate_verify_input.present;
  assert (pure (cv_input_present == input_present));
  assert (pure (cv_input_present ==>
    option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)));

  let already_verified = !c.handshake.certificate_verify_verified;
  assert (pure (already_verified == cv_verified));
  let not_verified = not already_verified;
  assert (pure (not_verified ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false));

  let ok =
    tag_ok &&
    stage_ok &&
    has_cv &&
    peer_is_present &&
    cv_input_present &&
    not_verified;

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 7));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsCertificateVerifyReceived));
  assert (pure (ok ==>
    option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)));
  assert (pure (ok ==>
    option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)));
  assert (pure (ok ==>
    option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false));
  lemma_option_is_some_some_imp
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer
    ok;
  lemma_option_is_some_some_imp
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify
    ok;
  lemma_option_is_some_some_imp
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input
    ok;

  fold (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_verify_input
    max_certificate_verify_input_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  fold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_receive_server_finished
  (c:connection_state)
  (#fin:erased M.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished == None /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.server_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 8uy;

  with stored_fin. assert (Box.pts_to c.handshake.messages.server_finished stored_fin);
  let stored = !c.handshake.messages.server_finished;
  let no_fin = (
    match stored with
    | None -> true
    | Some _ -> false);
  assert (pure (stored == stored_fin));
  assert (pure (no_fin ==> stored == None));
  assert (pure (no_fin ==> stored_fin == None));
  assert (pure (no_fin ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished == None));

  with server_hs_present.
    assert (Box.pts_to c.handshake.keys.server_handshake_traffic.present server_hs_present);
  with server_hs_secret.
    assert (V.pts_to c.handshake.keys.server_handshake_traffic.traffic_secret server_hs_secret);
  with server_hs_key.
    assert (V.pts_to c.handshake.keys.server_handshake_traffic.traffic_key server_hs_key);
  with server_hs_iv.
    assert (V.pts_to c.handshake.keys.server_handshake_traffic.traffic_iv server_hs_iv);
  let has_server_handshake_keys = !c.handshake.keys.server_handshake_traffic.present;
  assert (pure (has_server_handshake_keys == server_hs_present));

  let seq_ok = Rec.can_advance_seq c.records.read;
  let ok = tag_ok && stage_ok && no_fin && has_server_handshake_keys && seq_ok;

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 8));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsCertificateVerifyVerified));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished == None));
  assert (pure (ok ==> server_hs_present));
  assert (pure (ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
  assert (pure (ok ==>
    U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert (pure (ok ==> CS.legal_event
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })));

  fold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (finished_slot_exactly
    c.handshake.messages.server_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_verify_server_finished
  (c:connection_state)
  (payload_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerFinishedReceived /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v payload_len <= max_transcript_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. assert (pure True);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.server_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 9uy;

  with stored_fin. assert (Box.pts_to c.handshake.messages.server_finished stored_fin);
  let stored = !c.handshake.messages.server_finished;
  let has_fin = (
    match stored with
    | Some _ -> true
    | None -> false);
  assert (pure (stored == stored_fin));
  assert (pure (has_fin ==>
    option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished)));

  with transcript_storage transcript_len. assert (pure True);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  let already_verified = !c.handshake.server_finished_verified;
  assert (pure (already_verified == server_finished_verified));
  let not_verified = not already_verified;
  assert (pure (not_verified ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false));

  assert (pure (SZ.fits max_transcript_len));
  let max_len = SZ.uint_to_t max_transcript_len;
  let payload_fits = SZ.lte payload_len max_len;
  if payload_fits {
    let max_start = SZ.sub max_len payload_len;
    let transcript_room = sizet_lte_plain current_transcript_len max_start;
    lemma_sizet_lte_plain current_transcript_len max_start;

    let ok =
      tag_ok &&
      stage_ok &&
      has_fin &&
      not_verified &&
      transcript_room;

    assert (pure (ok ==> U8.v tag == 1));
    assert (pure (ok ==> U8.v stage == 9));
    assert (pure (ok ==>
      st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerFinishedReceived));
    assert (pure (ok ==>
      option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished)));
    lemma_option_is_some_some_imp
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished
      ok;
    assert (pure (ok ==>
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false));
    assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      SZ.v current_transcript_len));
    assert (pure (ok ==> SZ.v current_transcript_len <= SZ.v max_start));
    assert (pure (ok ==> SZ.v current_transcript_len + SZ.v payload_len <= max_transcript_len));
    assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
      SZ.v payload_len <= max_transcript_len));

    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (finished_slot_exactly
      c.handshake.messages.server_finished
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    ok
  } else {
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (finished_slot_exactly
      c.handshake.messages.server_finished
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_send_client_finished_runtime
  (c:connection_state)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerFinishedVerified /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <= max_transcript_len /\
            58 <= SZ.v network_out_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 10uy;

  with client_finished_stored. assert (Box.pts_to c.handshake.messages.client_finished client_finished_stored);
  let client_finished_value = !c.handshake.messages.client_finished;
  assert (pure (client_finished_value == client_finished_stored));
  let client_finished_absent = (
    match client_finished_value with
    | None -> true
    | Some _ -> false);

  with ch_present. assert (Box.pts_to c.handshake.keys.client_handshake_traffic.present ch_present);
  let client_hs_present = !c.handshake.keys.client_handshake_traffic.present;
  assert (pure (client_hs_present == ch_present));

  with ca_present. assert (Box.pts_to c.handshake.keys.client_application_traffic.present ca_present);
  let client_app_present = !c.handshake.keys.client_application_traffic.present;
  assert (pure (client_app_present == ca_present));

  with sa_present. assert (Box.pts_to c.handshake.keys.server_application_traffic.present sa_present);
  let server_app_present = !c.handshake.keys.server_application_traffic.present;
  assert (pure (server_app_present == sa_present));

  with transcript_len. assert (Box.pts_to c.handshake.transcript.len transcript_len);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);

  let seq_ok = Rec.can_advance_seq c.records.write;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  assert (pure (SZ.fits max_transcript_len));
  let max_len = SZ.uint_to_t max_transcript_len;
  let finished_len = 36sz;
  let transcript_room = (
    if SZ.lte finished_len max_len then
      let max_start = SZ.sub max_len finished_len in
      sizet_lte_plain current_transcript_len max_start
    else
      false);
  let out_room = sizet_lte_plain 58sz network_out_len;

  let ok =
    tag_ok &&
    stage_ok &&
    client_finished_absent &&
    client_hs_present &&
    client_app_present &&
    server_app_present &&
    seq_ok &&
    transcript_room &&
    out_room;

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 10));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerFinishedVerified));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None));
  assert (pure (ok ==> Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic));
  assert (pure (ok ==> Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
  assert (pure (ok ==> Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
  lemma_sizet_lte_plain 58sz network_out_len;
  assert (pure (ok ==> 58 <= SZ.v network_out_len));
  assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    SZ.v current_transcript_len));
  assert (pure (ok ==> SZ.v current_transcript_len + 36 <= max_transcript_len));
  assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <= max_transcript_len));

  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_send_application_data_runtime
  (c:connection_state)
  (payload_len:SZ.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            SZ.v payload_len <= SM.max_application_data_fragment_len /\
            SZ.v payload_len + 21 <= SZ.v network_out_len)
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
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);

  let tag = !c.control.control_tag;
  let control_ok = tag = 2uy;
  let client_app_present = !c.handshake.keys.client_application_traffic.present;

  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  let seq_ok = Rec.can_advance_seq c.records.write;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let size_ok =
    can_send_application_data_sizes payload_len network_out_len;

  let ok =
    control_ok &&
    client_app_present &&
    seq_ok &&
    size_ok;

  assert (pure (ok ==> U8.v tag == 2));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
  assert (pure (ok ==> SZ.v payload_len <= SM.max_application_data_fragment_len));
  assert (pure (ok ==> SZ.v payload_len + 21 <= SZ.v network_out_len));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_send_close_notify_runtime
  (c:connection_state)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            23 <= SZ.v network_out_len)
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
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);

  let tag = !c.control.control_tag;
  let control_ok = tag = 2uy;
  let client_app_present = !c.handshake.keys.client_application_traffic.present;

  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  let seq_ok = Rec.can_advance_seq c.records.write;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let size_ok =
    can_send_close_notify_sizes network_out_len;

  let ok =
    control_ok &&
    client_app_present &&
    seq_ok &&
    size_ok;

  assert (pure (ok ==> U8.v tag == 2));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
  assert (pure (ok ==> 23 <= SZ.v network_out_len));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn write_close_notify_alert
  (alert:array U8.t)
  requires ArrPts.pts_to alert (Seq.create 2 0uy)
  ensures exists* alert_bytes.
            ArrPts.pts_to alert alert_bytes **
            pure (B.length alert_bytes == 2 /\
                  Seq.equal alert_bytes close_notify_alert_fragment)
{
  alert.(0sz) <- 2uy;
  alert.(1sz) <- 0uy;
  with alert_bytes.
    assert (ArrPts.pts_to alert alert_bytes);
  assert_norm (close_notify_alert_fragment == B.of_list [2uy; 0uy]);
  assert_norm (B.length close_notify_alert_fragment == 2);
  assert_norm (Seq.index close_notify_alert_fragment 0 == 2uy);
  assert_norm (Seq.index close_notify_alert_fragment 1 == 0uy);
  assert (pure (B.length alert_bytes == 2));
  assert (pure (Seq.index alert_bytes 0 == 2uy));
  assert (pure (Seq.index alert_bytes 1 == 0uy));
  Seq.lemma_eq_intro alert_bytes close_notify_alert_fragment;
  assert (pure (Seq.equal alert_bytes close_notify_alert_fragment))
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
  (#alert:erased T.alert_description)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (Ghost.reveal alert <> T.CloseNotify /\
                 alert_tag_matches alert_wire (Ghost.reveal alert) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsAlert (Ghost.reveal alert);
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_alert_failure_state st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
{
  assert (pure (Ghost.reveal alert <> T.CloseNotify));
  assert (pure (alert_tag_matches alert_wire (Ghost.reveal alert)));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsAlert (Ghost.reveal alert);
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

  assert (pure (tls_error_code_matches 0uy alert_wire (T.AlertError (Ghost.reveal alert))));
  assert (pure (control_state_matches
    5uy
    0uy
    true
    0uy
    alert_wire
    (CS.ControlFailed (T.AlertError (Ghost.reveal alert)))));
  fold (control_exactly
    c.control
    (CS.ControlFailed (T.AlertError (Ghost.reveal alert)))
    (Some (T.AlertError (Ghost.reveal alert))));
  assert (pure ((CS.fail_model st0.CS.cs_model (T.AlertError (Ghost.reveal alert))).CS.model_control ==
                CS.ControlFailed (T.AlertError (Ghost.reveal alert))));
  assert (pure ((CS.fail_model st0.CS.cs_model (T.AlertError (Ghost.reveal alert))).CS.model_failure ==
                Some (T.AlertError (Ghost.reveal alert))));
  fold (connection_model_exactly c (CS.fail_model st0.CS.cs_model (T.AlertError (Ghost.reveal alert))));

  lemma_received_alert_failure_state_evolves st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes);
  MR.update c.ghost_state (received_alert_failure_state st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes));
  fold (connection_exactly c (received_alert_failure_state st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes)))
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

fn mark_received_server_hello
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lsh:IM.server_hello)
  (#sh:erased M.server_hello)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
           IM.is_valid_server_hello lsh sh **
           pure (st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsClientHelloSent /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 Seq.equal
                   (Ghost.reveal 'fragment_bytes)
                   (W.serialize_handshake (M.ServerHello sh)) /\
                 st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
                 B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   B.length (W.serialize_handshake (M.ServerHello sh)) <=
                   max_transcript_len /\
                 CS.legal_event
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake (M.ServerHello sh);
                   }) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake (M.ServerHello sh);
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloSent));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    })));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));

  W.lemma_serialize_server_hello_len sh;
  assert (pure (B.length (W.serialize_handshake (M.ServerHello sh)) == 90));
  assert (pure (SZ.v fragment_len == 90));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly
    c.handshake.server_key_share
    st0.CS.cs_model.CS.model_handshake);
  unfold (optional_fixed_bytes_exactly
    c.handshake.server_key_share
    32
    (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
     | Some sh -> Some sh.M.key_share
     | None -> None));
  with old_server_key_share_present old_server_key_share_storage. _;

  c.control.handshake_stage_tag := 3uy;

  assert (pure (control_state_matches
    1uy
    3uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsServerHelloReceived)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsServerHelloReceived)
    st0.CS.cs_model.CS.model_failure);

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (server_hello_slot_exactly
    c.handshake.messages.server_hello
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
  with stored_server_hello. _;
  drop_ (match stored_server_hello, st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_server_hello old_l old_m
    | _, _ -> pure False);
  c.handshake.messages.server_hello := Some lsh;

  unfold (IM.is_valid_server_hello lsh sh);
  with lsh_random lsh_key_share. _;
  V.to_array_pts_to lsh.IM.server_hello_key_share;
  V.to_array_pts_to c.handshake.server_key_share.bytes;
  Arr.memcpy
    32sz
    (V.vec_to_array lsh.IM.server_hello_key_share)
    (V.vec_to_array c.handshake.server_key_share.bytes);
  V.to_vec_pts_to lsh.IM.server_hello_key_share;
  V.to_vec_pts_to c.handshake.server_key_share.bytes;
  c.handshake.server_key_share.present := true;
  with copied_server_key_share. assert (V.pts_to c.handshake.server_key_share.bytes copied_server_key_share);
  assert (pure (Seq.equal copied_server_key_share (Ghost.reveal sh).M.key_share));
  assert (pure (optional_fixed_bytes_match true copied_server_key_share 32 (Some (Ghost.reveal sh).M.key_share)));
  fold (optional_fixed_bytes_exactly
    c.handshake.server_key_share
    32
    (Some (Ghost.reveal sh).M.key_share));
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (IM.is_valid_server_hello lsh sh);

  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  unfold (sized_bytes_exactly
    c.handshake.buffers.server_hello_bytes
    max_server_hello_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes);

  with old_server_hello_storage old_server_hello_len. _;
  V.to_array_pts_to c.handshake.buffers.server_hello_bytes.bytes;
  ArrPts.pts_to_len fragment;
  ArrPts.pts_to_len (V.vec_to_array c.handshake.buffers.server_hello_bytes.bytes);
  Arr.memcpy_l fragment_len fragment (V.vec_to_array c.handshake.buffers.server_hello_bytes.bytes);
  V.to_vec_pts_to c.handshake.buffers.server_hello_bytes.bytes;
  with server_hello_storage. assert (V.pts_to c.handshake.buffers.server_hello_bytes.bytes server_hello_storage);
  Seq.lemma_len_slice server_hello_storage 0 (SZ.v fragment_len);
  assert (pure (Seq.equal
    (Seq.slice server_hello_storage 0 (SZ.v fragment_len))
    (Ghost.reveal 'fragment_bytes)));
  assert (pure (Seq.equal
    (Seq.slice server_hello_storage 0 (SZ.v fragment_len))
    (W.serialize_handshake (M.ServerHello sh))));

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v fragment_len <= max_transcript_len));

  copy_server_hello_prefix_to_transcript
    c.handshake.buffers.server_hello_bytes.bytes
    c.handshake.transcript.bytes
    fragment_len
    transcript_len;

  with copied_server_hello_storage copied_transcript_storage.
    assert (V.pts_to c.handshake.buffers.server_hello_bytes.bytes copied_server_hello_storage **
            V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (copied_server_hello_storage == server_hello_storage));

  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v fragment_len)));
  let new_transcript_len = SZ.add transcript_len fragment_len;
  c.handshake.buffers.server_hello_bytes.len := fragment_len;
  c.handshake.transcript.len := new_transcript_len;

  fold (sized_bytes_exactly
    c.handshake.buffers.server_hello_bytes
    max_server_hello_len
    (W.serialize_handshake (M.ServerHello sh)));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.ServerHello sh))));

  fold (server_hello_slot_exactly
    c.handshake.messages.server_hello
    (Some (Ghost.reveal sh)));
  fold (handshake_messages_exactly
    c.handshake.messages
    (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (handshake_exactly
    c.handshake
    (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_server_hello_state_evolves
    st0
    sh
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)))
}

fn mark_received_encrypted_extensions
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lee:IM.encrypted_extensions)
  (#ee:erased M.encrypted_extensions)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
           IM.is_valid_encrypted_extensions lee ee **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerHelloReceived /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
                  Some?
                    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                  U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                  B.length 'fragment_bytes == SZ.v fragment_len /\
                  Seq.equal
                    (Ghost.reveal 'fragment_bytes)
                    (W.serialize_handshake (M.EncryptedExtensions ee)) /\
                  B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v fragment_len <= max_transcript_len /\
                  CS.event_raw_delta_legal
                    st0.CS.cs_model
                    (CS.ConnNetworkEvent {
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                    })
                    B.empty
                    (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerHelloReceived));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == None));
  assert (pure (Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  c.control.handshake_stage_tag := 4uy;
  assert (pure (control_state_matches
    1uy
    4uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsEncryptedExtensionsReceived)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsEncryptedExtensionsReceived)
    st0.CS.cs_model.CS.model_failure);

  Rec.advance_seq c.records.read;
  fold (record_layer_exactly
    c.records
    { st0.CS.cs_model.CS.model_record with
        CS.record_read = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_read });

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (encrypted_extensions_slot_exactly
    c.handshake.messages.encrypted_extensions
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions);
  with stored_encrypted_extensions. _;
  drop_ (match stored_encrypted_extensions, st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_encrypted_extensions old_l old_m
    | _, _ -> pure False);
  c.handshake.messages.encrypted_extensions := Some lee;
  fold (encrypted_extensions_slot_exactly
    c.handshake.messages.encrypted_extensions
    (Some (Ghost.reveal ee)));

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v fragment_len <= max_transcript_len));

  copy_array_to_transcript
    fragment
    c.handshake.transcript.bytes
    fragment_len
    transcript_len;

  with copied_transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v fragment_len)));
  let new_transcript_len = SZ.add transcript_len fragment_len;
  c.handshake.transcript.len := new_transcript_len;

  assert (pure (Seq.equal
    (Ghost.reveal 'fragment_bytes)
    (W.serialize_handshake (M.EncryptedExtensions ee))));
  assert (pure (Seq.equal
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Ghost.reveal 'fragment_bytes))
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.EncryptedExtensions ee)))));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.EncryptedExtensions ee))));

  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_messages_exactly
    c.handshake.messages
    (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (handshake_exactly
    c.handshake
    (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_encrypted_extensions_state_evolves
    st0
    ee
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)))
}

fn mark_received_certificate
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lcert:IM.certificate_msg)
  (#cert:erased M.certificate_msg)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
           IM.is_valid_certificate_msg lcert cert **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
           st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
           (Ghost.reveal cert).M.chain <> [] /\
                  U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                  B.length 'fragment_bytes == SZ.v fragment_len /\
                  Seq.equal
                    (Ghost.reveal 'fragment_bytes)
                    (W.serialize_handshake (M.Certificate (Ghost.reveal cert))) /\
                  B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v fragment_len <= max_transcript_len /\
                  CS.event_raw_delta_legal
                    st0.CS.cs_model
                    (CS.ConnNetworkEvent {
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
                    })
                    B.empty
                    (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsEncryptedExtensionsReceived));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None));
  assert (pure ((Ghost.reveal cert).M.chain <> []));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  c.control.handshake_stage_tag := 5uy;
  assert (pure (control_state_matches
    1uy
    5uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsCertificateReceived)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsCertificateReceived)
    st0.CS.cs_model.CS.model_failure);

  Rec.advance_seq c.records.read;
  fold (record_layer_exactly
    c.records
    { st0.CS.cs_model.CS.model_record with
        CS.record_read = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_read });

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_slot_exactly
    c.handshake.messages.certificate
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
  with stored_certificate. _;
  drop_ (match stored_certificate, st0.CS.cs_model.CS.model_handshake.CS.hs_certificate with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_certificate_msg old_l old_m
    | _, _ -> pure False);
  c.handshake.messages.certificate := Some lcert;

  unfold (IM.is_valid_certificate_msg lcert (Ghost.reveal cert));
  with chain_bytes offsets lens. _;
  V.pts_to_len lcert.IM.certificate_msg_chain_bytes;
  V.pts_to_len lcert.IM.certificate_msg_cert_offsets;
  V.pts_to_len lcert.IM.certificate_msg_cert_lens;
  assert (pure (B.length chain_bytes == IM.max_certificate_chain_bytes));
  assert (pure (Seq.length offsets == IM.max_certificate_chain_entries));
  assert (pure (Seq.length lens == IM.max_certificate_chain_entries));
  assert (pure (SZ.v lcert.IM.certificate_msg_cert_count > 0));
  lemma_certificate_chain_matches_head
    chain_bytes
    (SZ.v lcert.IM.certificate_msg_chain_bytes_len)
    offsets
    lens
    (SZ.v lcert.IM.certificate_msg_cert_count)
    (Ghost.reveal cert).M.chain;

  assert (pure (SZ.v 0sz < IM.max_certificate_chain_entries));
  V.to_array_pts_to lcert.IM.certificate_msg_cert_offsets;
  let first_offset = (V.vec_to_array lcert.IM.certificate_msg_cert_offsets).(0sz);
  V.to_vec_pts_to lcert.IM.certificate_msg_cert_offsets;
  V.to_array_pts_to lcert.IM.certificate_msg_cert_lens;
  let first_len = (V.vec_to_array lcert.IM.certificate_msg_cert_lens).(0sz);
  V.to_vec_pts_to lcert.IM.certificate_msg_cert_lens;
  assert (pure (first_offset == Seq.index offsets 0));
  assert (pure (first_len == Seq.index lens 0));

  let leaf =
    Ghost.hide
      (match (Ghost.reveal cert).M.chain with
       | cert_leaf :: _ -> cert_leaf
       | [] -> B.empty);
  assert (pure (Seq.equal
    (Ghost.reveal leaf)
    (Seq.slice chain_bytes (SZ.v first_offset) (SZ.v first_offset + SZ.v first_len))));
  assert (pure (SZ.v first_offset + SZ.v first_len <= B.length chain_bytes));
  assert (pure (SZ.v first_len <= max_handshake_flight_len));

  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  with parsed. _;
  rewrite (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_leaf_der
    max_handshake_flight_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der)
    as (optional_sized_bytes_exactly
      c.handshake.buffers.certificate_leaf_der
      max_handshake_flight_len
      None);
  overwrite_optional_sized_bytes_from_certificate_chain
    lcert.IM.certificate_msg_chain_bytes
    c.handshake.buffers.certificate_leaf_der
    first_offset
    first_len
    #leaf;

  fold (IM.is_valid_certificate_msg lcert (Ghost.reveal cert));
  fold (certificate_slot_exactly
    c.handshake.messages.certificate
    (Some (Ghost.reveal cert)));

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v fragment_len <= max_transcript_len));

  copy_array_to_transcript
    fragment
    c.handshake.transcript.bytes
    fragment_len
    transcript_len;

  with copied_transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v fragment_len)));
  let new_transcript_len = SZ.add transcript_len fragment_len;
  c.handshake.transcript.len := new_transcript_len;

  assert (pure (Seq.equal
    (Ghost.reveal 'fragment_bytes)
    (W.serialize_handshake (M.Certificate (Ghost.reveal cert)))));
  assert (pure (Seq.equal
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Ghost.reveal 'fragment_bytes))
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Certificate (Ghost.reveal cert))))));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Certificate (Ghost.reveal cert)))));

  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_client_hello_bytes ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_client_hello_bytes));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der ==
    Some (Ghost.reveal leaf)));
  assert (pure ((received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_messages_exactly
    c.handshake.messages
    (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (handshake_exactly
    c.handshake
    (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_certificate_state_evolves
    st0
    (Ghost.reveal cert)
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)))
}

fn mark_validated_certificate
  (c:connection_state)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (#peer:erased X.peer_identity)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to payload 'payload_bytes **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsCertificateReceived /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None /\
                  B.length 'payload_bytes == SZ.v payload_len /\
                  SZ.v payload_len <= max_public_key_len /\
                  (Ghost.reveal peer).X.validated_hostname ==
                    st0.CS.cs_model.CS.model_config.CS.config_server_name /\
                  (Ghost.reveal peer).X.leaf_public_key ==
                    (Ghost.reveal 'payload_bytes) /\
                  (Ghost.reveal peer).X.permitted_signature_schemes == [] /\
                  CS.legal_event
                    st0.CS.cs_model
                    (CS.ConnLocalEvent
                      (CS.LocalValidateCertificate (Ghost.reveal peer))))
  ensures connection_exactly
            c
            (validated_certificate_state st0 (Ghost.reveal peer)) **
          ArrPts.pts_to payload 'payload_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsCertificateReceived));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None));
  assert (pure (B.length 'payload_bytes == SZ.v payload_len));
  assert (pure (SZ.v payload_len <= max_public_key_len));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalValidateCertificate (Ghost.reveal peer)))));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);
  with role validation_time. _;
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  with peer_present peer_hostname peer_hostname_len peer_public_key peer_public_key_len peer_schemes peer_schemes_len. _;

  c.control.handshake_stage_tag := 6uy;
  assert (pure (control_state_matches
    1uy
    6uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsCertificateValidated)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsCertificateValidated)
    st0.CS.cs_model.CS.model_failure);

  fold (sized_bytes_allocated
    c.handshake.validated_peer.validated_hostname
    max_hostname_len);
  copy_hostname_sized_bytes
    c.config.server_name
    c.handshake.validated_peer.validated_hostname;
  rewrite (sized_bytes_exactly
    c.handshake.validated_peer.validated_hostname
    max_hostname_len
    st0.CS.cs_model.CS.model_config.CS.config_server_name)
    as (sized_bytes_exactly
      c.handshake.validated_peer.validated_hostname
      max_hostname_len
      (Ghost.reveal peer).X.validated_hostname);

  fold (sized_bytes_allocated
    c.handshake.validated_peer.leaf_public_key
    max_public_key_len);
  copy_array_to_public_key_sized_bytes
    payload
    c.handshake.validated_peer.leaf_public_key
    payload_len;
  rewrite (sized_bytes_exactly
    c.handshake.validated_peer.leaf_public_key
    max_public_key_len
    (Ghost.reveal 'payload_bytes))
    as (sized_bytes_exactly
      c.handshake.validated_peer.leaf_public_key
      max_public_key_len
      (Ghost.reveal peer).X.leaf_public_key);

  c.handshake.validated_peer.permitted_signature_schemes.len := 0sz;
  c.handshake.validated_peer.present := true;

  unfold (sized_bytes_exactly
    c.handshake.validated_peer.validated_hostname
    max_hostname_len
    (Ghost.reveal peer).X.validated_hostname);
  with stored_hostname stored_hostname_len. _;
  unfold (sized_bytes_exactly
    c.handshake.validated_peer.leaf_public_key
    max_public_key_len
    (Ghost.reveal peer).X.leaf_public_key);
  with stored_public_key stored_public_key_len. _;
  assert_norm (IM.signature_schemes_match peer_schemes 0 []);
  assert (pure (IM.signature_schemes_match
    peer_schemes
    (SZ.v 0sz)
    (Ghost.reveal peer).X.permitted_signature_schemes));
  fold (peer_exactly
    c.handshake.validated_peer
    (Some (Ghost.reveal peer)));

  fold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);

  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  fold (handshake_messages_exactly
    c.handshake.messages
    (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake);
  rewrite (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
    as (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  assert (pure (cv_verified ==
    (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure (server_finished_verified ==
    (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  fold (handshake_exactly
    c.handshake
    (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake);

  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_record ==
    st0.CS.cs_model.CS.model_record));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  rewrite (record_layer_exactly c.records st0.CS.cs_model.CS.model_record)
    as (record_layer_exactly
      c.records
      (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_record);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model);

  lemma_validated_certificate_state_evolves st0 (Ghost.reveal peer);
  MR.update
    c.ghost_state
    (validated_certificate_state st0 (Ghost.reveal peer));
  fold (connection_exactly
    c
    (validated_certificate_state st0 (Ghost.reveal peer)))
}

fn mark_received_certificate_verify
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lcv:IM.certificate_verify)
  (#cv:erased M.certificate_verify)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to raw 'raw_bytes **
           ArrPts.pts_to fragment 'fragment_bytes **
           IM.is_valid_certificate_verify lcv cv **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsCertificateValidated /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None /\
                  Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
                  U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                  B.length 'fragment_bytes == SZ.v fragment_len /\
                  Seq.equal
                    (Ghost.reveal 'fragment_bytes)
                    (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))) /\
                  B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v fragment_len <= max_transcript_len /\
                  CS.event_raw_delta_legal
                    st0.CS.cs_model
                    (CS.ConnNetworkEvent {
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
                    })
                    B.empty
                    (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)) **
          ArrPts.pts_to raw 'raw_bytes **
          ArrPts.pts_to fragment 'fragment_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsCertificateValidated));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None));
  assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  c.control.handshake_stage_tag := 7uy;
  assert (pure (control_state_matches
    1uy
    7uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsCertificateVerifyReceived)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsCertificateVerifyReceived)
    st0.CS.cs_model.CS.model_failure);

  Rec.advance_seq c.records.read;
  fold (record_layer_exactly
    c.records
    { st0.CS.cs_model.CS.model_record with
        CS.record_read = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_read });

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  with stored_certificate_verify. _;
  drop_ (match stored_certificate_verify, st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_certificate_verify old_l old_m
    | _, _ -> pure False);
  c.handshake.messages.certificate_verify := Some lcv;
  fold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    (Some (Ghost.reveal cv)));

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v fragment_len <= max_transcript_len));
  assert (pure (byte_prefix_matches
    old_transcript_storage
    transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (Seq.equal
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice old_transcript_storage 0 (SZ.v transcript_len))));
  Seq.lemma_eq_intro
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice old_transcript_storage 0 (SZ.v transcript_len));

  V.to_array_pts_to c.handshake.transcript.bytes;
  let mut transcript_hash = [| 0uy; 32sz |];
  Crypto.sha256_prefix
    (V.vec_to_array c.handshake.transcript.bytes)
    transcript_len
    transcript_hash;
  V.to_vec_pts_to c.handshake.transcript.bytes;
  with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
  assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  let mut certificate_verify_input = [| 0uy; 130sz |];
  Ser.build_server_certificate_verify_input
    transcript_hash
    certificate_verify_input
    130sz;
  with certificate_verify_input_bytes.
    assert (ArrPts.pts_to certificate_verify_input certificate_verify_input_bytes);
  assert (pure (B.length certificate_verify_input_bytes == 130));
  assert (pure (B.length transcript_hash_bytes == 32));
  assert (pure (Seq.equal
    (Ghost.reveal certificate_verify_input_bytes)
    (W.serialize_server_certificate_verify_input (Ghost.reveal transcript_hash_bytes))));
  W.lemma_serialize_server_certificate_verify_input_len32
    (Ghost.reveal transcript_hash_bytes);
  assert (pure (Seq.equal
    (W.serialize_server_certificate_verify_input (Ghost.reveal transcript_hash_bytes))
    (H.certificate_verify_input (Ghost.reveal transcript_hash_bytes))));
  assert (pure (Seq.equal
    (Ghost.reveal certificate_verify_input_bytes)
    (H.certificate_verify_input (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript))));
  let cv_input = Ghost.hide
    (H.certificate_verify_input (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  with parsed. _;
  rewrite (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_verify_input
    max_certificate_verify_input_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)
    as (optional_sized_bytes_exactly
      c.handshake.buffers.certificate_verify_input
      max_certificate_verify_input_len
      None);
  assert (pure (SZ.v 130sz <= max_certificate_verify_input_len));
  overwrite_optional_certificate_verify_input
    certificate_verify_input
    c.handshake.buffers.certificate_verify_input
    130sz
    #cv_input;

  copy_array_to_transcript
    fragment
    c.handshake.transcript.bytes
    fragment_len
    transcript_len;

  with copied_transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v fragment_len)));
  let new_transcript_len = SZ.add transcript_len fragment_len;
  c.handshake.transcript.len := new_transcript_len;

  assert (pure (Seq.equal
    (Ghost.reveal 'fragment_bytes)
    (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv)))));
  assert (pure (Seq.equal
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Ghost.reveal 'fragment_bytes))
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))))));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv)))));

  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_client_hello_bytes ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_client_hello_bytes));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der));
  assert (pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input ==
    Some (H.certificate_verify_input (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript))));
  rewrite (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_verify_input
    max_certificate_verify_input_len
    (Some (Ghost.reveal cv_input)))
    as (optional_sized_bytes_exactly
      c.handshake.buffers.certificate_verify_input
      max_certificate_verify_input_len
      (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_messages_exactly
    c.handshake.messages
    (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (handshake_exactly
    c.handshake
    (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_certificate_verify_state_evolves
    st0
    (Ghost.reveal cv)
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)))
}

fn mark_verified_certificate_signature
  (c:connection_state)
  (#cv:erased M.certificate_verify)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
                    Some (Ghost.reveal cv) /\
                  Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
                  Some? st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
                  CS.legal_event
                    st0.CS.cs_model
                    (CS.ConnLocalEvent
                      (CS.LocalVerifyCertificateSignature (Ghost.reveal cv))))
  ensures connection_exactly
            c
            (verified_certificate_signature_state st0 (Ghost.reveal cv))
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsCertificateVerifyReceived));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    Some (Ghost.reveal cv)));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalVerifyCertificateSignature (Ghost.reveal cv)))));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;

  c.control.handshake_stage_tag := 8uy;
  assert (pure (control_state_matches
    1uy
    8uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsCertificateVerifyVerified)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsCertificateVerifyVerified)
    st0.CS.cs_model.CS.model_failure);

  c.handshake.certificate_verify_verified := true;

  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  fold (handshake_messages_exactly
    c.handshake.messages
    (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
    as (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  assert (pure (true ==
    (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure (server_finished_verified ==
    (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  fold (handshake_exactly
    c.handshake
    (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake);

  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_record ==
    st0.CS.cs_model.CS.model_record));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_config);
  rewrite (record_layer_exactly c.records st0.CS.cs_model.CS.model_record)
    as (record_layer_exactly
      c.records
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_record);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model);

  lemma_verified_certificate_signature_state_evolves st0 (Ghost.reveal cv);
  MR.update
    c.ghost_state
    (verified_certificate_signature_state st0 (Ghost.reveal cv));
  fold (connection_exactly
    c
    (verified_certificate_signature_state st0 (Ghost.reveal cv)))
}

fn mark_received_server_finished
  (c:connection_state)
  (raw:array U8.t)
  (lfin:IM.finished)
  (#fin:erased M.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to raw 'raw_bytes **
           IM.is_valid_finished lfin fin **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished == None /\
                  Some?
                    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                  U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                  CS.event_raw_delta_legal
                    st0.CS.cs_model
                    (CS.ConnNetworkEvent {
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
                    })
                    B.empty
                    (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)) **
          ArrPts.pts_to raw 'raw_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsCertificateVerifyVerified));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished == None));
  assert (pure (Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    B.empty
    (Ghost.reveal 'raw_bytes)));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  c.control.handshake_stage_tag := 9uy;
  assert (pure (control_state_matches
    1uy
    9uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsServerFinishedReceived)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsServerFinishedReceived)
    st0.CS.cs_model.CS.model_failure);

  Rec.advance_seq c.records.read;
  fold (record_layer_exactly
    c.records
    { st0.CS.cs_model.CS.model_record with
        CS.record_read = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_read });

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.server_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
  with stored_server_finished. _;
  drop_ (match stored_server_finished, st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_finished old_l old_m
    | _, _ -> pure False);
  c.handshake.messages.server_finished := Some lfin;
  fold (finished_slot_exactly
    c.handshake.messages.server_finished
    (Some (Ghost.reveal fin)));

  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
    as (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_messages_exactly
    c.handshake.messages
    (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  fold (handshake_exactly
    c.handshake
    (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_received_server_finished_state_evolves
    st0
    (Ghost.reveal fin)
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)))
}

fn mark_verified_server_finished
  (c:connection_state)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (#fin:erased M.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to payload 'payload_bytes **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerFinishedReceived /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
                    Some (Ghost.reveal fin) /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false /\
                  B.length 'payload_bytes == SZ.v payload_len /\
                  Seq.equal
                    (Ghost.reveal 'payload_bytes)
                    (W.serialize_handshake (M.Finished (Ghost.reveal fin))) /\
                  B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v payload_len <= max_transcript_len /\
                  CS.legal_event
                    st0.CS.cs_model
                    (CS.ConnLocalEvent
                      (CS.LocalVerifyFinished (Ghost.reveal fin))))
  ensures connection_exactly
            c
            (verified_server_finished_state st0 (Ghost.reveal fin)) **
          ArrPts.pts_to payload 'payload_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerFinishedReceived));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    Some (Ghost.reveal fin)));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false));
  assert (pure (B.length 'payload_bytes == SZ.v payload_len));
  assert (pure (Seq.equal
    (Ghost.reveal 'payload_bytes)
    (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalVerifyFinished (Ghost.reveal fin)))));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;

  c.control.handshake_stage_tag := 10uy;
  assert (pure (control_state_matches
    1uy
    10uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsServerFinishedVerified)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsServerFinishedVerified)
    st0.CS.cs_model.CS.model_failure);

  c.handshake.server_finished_verified := true;

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v payload_len <= max_transcript_len));

  copy_array_to_transcript
    payload
    c.handshake.transcript.bytes
    payload_len
    transcript_len;

  with copied_transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v payload_len)));
  let new_transcript_len = SZ.add transcript_len payload_len;
  c.handshake.transcript.len := new_transcript_len;

  assert (pure (Seq.equal
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Ghost.reveal 'payload_bytes))
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin))))));
  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));

  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  fold (handshake_messages_exactly
    c.handshake.messages
    (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  assert (pure (true ==
    (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure (cv_verified ==
    (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  fold (handshake_exactly
    c.handshake
    (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake);

  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_record ==
    st0.CS.cs_model.CS.model_record));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_config);
  rewrite (record_layer_exactly c.records st0.CS.cs_model.CS.model_record)
    as (record_layer_exactly
      c.records
      (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_record);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model);

  lemma_verified_server_finished_state_evolves st0 (Ghost.reveal fin);
  MR.update
    c.ghost_state
    (verified_server_finished_state st0 (Ghost.reveal fin));
  fold (connection_exactly
    c
    (verified_server_finished_state st0 (Ghost.reveal fin)))
}

fn mark_sent_client_finished
  (c:connection_state)
  (handshake_bytes:array U8.t)
  (handshake_len:SZ.t)
  (lfin:IM.finished)
  (network_out:array U8.t)
  (written:SZ.t)
  (#fin:erased M.finished)
  (#raw_sent:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to handshake_bytes 'handshake_storage **
           IM.is_valid_finished lfin fin **
           ArrPts.pts_to network_out 'network_out_bytes **
           pure (can_send_client_finished st0 (Ghost.reveal fin) (Ghost.reveal raw_sent) /\
                 B.length 'handshake_storage == SZ.v handshake_len /\
                 SZ.v handshake_len == 36 /\
                 Seq.equal
                   (Ghost.reveal 'handshake_storage)
                   (W.serialize_handshake (M.Finished (Ghost.reveal fin))) /\
                 SZ.v written == 58 /\
                 SZ.v written <= B.length 'network_out_bytes /\
                 Seq.equal
                   (Ghost.reveal raw_sent)
                   (Seq.slice (Ghost.reveal 'network_out_bytes) 0 (SZ.v written)))
  ensures connection_exactly
            c
            (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)) **
          ArrPts.pts_to handshake_bytes 'handshake_storage **
          ArrPts.pts_to network_out 'network_out_bytes
{
  assert (pure (can_send_client_finished st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)));
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerFinishedVerified));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None));
  assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
  assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <= max_transcript_len));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;

  c.control.control_tag := 2uy;
  assert (pure (control_state_matches
    2uy
    10uy
    false
    0uy
    0uy
    CS.ControlApplicationData));
  fold (control_exactly
    c.control
    CS.ControlApplicationData
    st0.CS.cs_model.CS.model_failure);

  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  with ca_present ca_secret ca_key ca_iv. _;
  lemma_traffic_key_material_match_present_of_some
    ca_present
    ca_secret
    ca_key
    ca_iv
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic;
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic ==
    Some {
      CS.traffic_secret = ca_secret;
      CS.traffic_key = ca_key;
      CS.traffic_iv = ca_iv;
    }));

  Rec.advance_seq c.records.write;
  V.to_array_pts_to c.handshake.keys.client_application_traffic.traffic_key;
  V.to_array_pts_to c.handshake.keys.client_application_traffic.traffic_iv;
  Rec.install_application_keys_runtime
    c.records.write
    (V.vec_to_array c.handshake.keys.client_application_traffic.traffic_key)
    (V.vec_to_array c.handshake.keys.client_application_traffic.traffic_iv);
  V.to_vec_pts_to c.handshake.keys.client_application_traffic.traffic_key;
  V.to_vec_pts_to c.handshake.keys.client_application_traffic.traffic_iv;
  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);

  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_read ==
    st0.CS.cs_model.CS.model_record.CS.record_read));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_write ==
    R.install_keys
      (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write)
      R.Application
      ca_key
      ca_iv));
  rewrite (Rec.is_record_state
    c.records.read
    st0.CS.cs_model.CS.model_record.CS.record_read)
    as (Rec.is_record_state
      c.records.read
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_read);
  rewrite (Rec.is_record_state
    c.records.write
    (R.install_keys
      (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write)
      R.Application
      ca_key
      ca_iv))
    as (Rec.is_record_state
      c.records.write
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_write);
  fold (record_layer_exactly
    c.records
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record);

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v handshake_len <= max_transcript_len));
  copy_array_to_transcript
    handshake_bytes
    c.handshake.transcript.bytes
    handshake_len
    transcript_len;
  with copied_transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v handshake_len)));
  let new_transcript_len = SZ.add transcript_len handshake_len;
  c.handshake.transcript.len := new_transcript_len;
  assert (pure (Seq.equal
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Ghost.reveal 'handshake_storage))
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin))))));
  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));

  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  with old_client_finished. _;
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None));
  assert (pure (old_client_finished == None));
  drop_ (match old_client_finished, st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_finished old_l old_m
    | _, _ -> pure False);
  c.handshake.messages.client_finished := Some lfin;
  fold (finished_slot_exactly
    c.handshake.messages.client_finished
    (Some (Ghost.reveal fin)));
  fold (handshake_messages_exactly
    c.handshake.messages
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);

  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  assert (pure (cv_verified ==
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure (server_finished_verified ==
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  fold (handshake_exactly
    c.handshake
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);

  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model);

  lemma_sent_client_finished_state_evolves st0 (Ghost.reveal fin) (Ghost.reveal raw_sent);
  MR.update
    c.ghost_state
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent));
  fold (connection_exactly
    c
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)))
}

fn try_send_client_finished
  (c:connection_state)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'old_network_out == SZ.v network_out_len)
  returns ok: bool
  ensures (if ok then
            exists* fin raw_sent network_out_bytes.
              connection_exactly c (sent_client_finished_state st0 fin raw_sent) **
              ArrPts.pts_to network_out network_out_bytes **
              pure (B.length network_out_bytes == SZ.v network_out_len /\
                    58 <= B.length network_out_bytes /\
                    can_send_client_finished st0 fin raw_sent /\
                    Seq.equal raw_sent (Seq.slice network_out_bytes 0 58))
          else
            connection_exactly c st0 **
            ArrPts.pts_to network_out 'old_network_out)
{
  let ready = can_send_client_finished_runtime c network_out_len;
  if ready {
    assert (pure (st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerFinishedVerified));
    assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic));
    assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
    assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
    assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <= max_transcript_len));
    assert (pure (58 <= SZ.v network_out_len));

    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    with cv_verified server_finished_verified. _;
    unfold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    with transcript_storage transcript_len. _;
    let transcript_len_runtime = !c.handshake.transcript.len;
    assert (pure (transcript_len_runtime == transcript_len));
    assert (pure (byte_prefix_matches
      transcript_storage
      transcript_len_runtime
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    assert (pure (Seq.equal
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
    Seq.lemma_eq_intro
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

    unfold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    unfold (traffic_key_material_exactly
      c.handshake.keys.client_handshake_traffic
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
    with ch_present ch_secret ch_key ch_iv. _;
    lemma_traffic_key_material_match_present_of_some
      ch_present
      ch_secret
      ch_key
      ch_iv
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic;
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
      Some {
        CS.traffic_secret = ch_secret;
        CS.traffic_key = ch_key;
        CS.traffic_iv = ch_iv;
      }));

    V.to_array_pts_to c.handshake.transcript.bytes;
    let mut transcript_hash = [| 0uy; 32sz |];
    Crypto.sha256_prefix
      (V.vec_to_array c.handshake.transcript.bytes)
      transcript_len_runtime
      transcript_hash;
    V.to_vec_pts_to c.handshake.transcript.bytes;
    with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
    assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

    V.to_array_pts_to c.handshake.keys.client_handshake_traffic.traffic_secret;
    let mut verify_data = [| 0uy; 32sz |];
    KS.finished_verify_data
      (V.vec_to_array c.handshake.keys.client_handshake_traffic.traffic_secret)
      transcript_hash
      verify_data;
    V.to_vec_pts_to c.handshake.keys.client_handshake_traffic.traffic_secret;
    with verify_data_bytes. assert (ArrPts.pts_to verify_data verify_data_bytes);
    assert (pure (verify_data_bytes ==
      K.finished_verify_data
        ch_secret
        (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

    fold (traffic_key_material_exactly
      c.handshake.keys.client_handshake_traffic
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);

    let fin = Ghost.hide ({ M.verify_data = verify_data_bytes });
    let fin_vec = V.alloc 0uy 32sz;
    copy_fixed32_array_to_vec verify_data fin_vec;
    let lfin = { IM.finished_verify_data = fin_vec };
    assert (pure (lfin.IM.finished_verify_data == fin_vec));
    with fin_vec_bytes. assert (V.pts_to fin_vec fin_vec_bytes);
    assert (pure (fin_vec_bytes == verify_data_bytes));
    rewrite (V.pts_to fin_vec fin_vec_bytes)
      as (V.pts_to lfin.IM.finished_verify_data fin_vec_bytes);
    assert (pure (B.length verify_data_bytes == 32));
    assert (pure (Seq.equal fin_vec_bytes (Ghost.reveal fin).M.verify_data));
    fold (IM.is_valid_finished lfin (Ghost.reveal fin));

    let mut serialized_finished = [| 0uy; 36sz |];
    let written_raw =
      Ser.serialize_client_finished_outputs
        lfin
        serialized_finished
        network_out
        network_out_len;
    with sent_fin serialized_finished_bytes network_out_bytes. _;
    let fin_sent = Ghost.hide sent_fin;
    assert (pure (B.length serialized_finished_bytes == 36));
    assert (pure (Seq.equal
      serialized_finished_bytes
      (W.serialize_handshake (M.Finished (Ghost.reveal fin_sent)))));
    assert (pure (B.length network_out_bytes == SZ.v network_out_len));
    assert (pure (SZ.v written_raw == 58));
    assert (pure (58 <= B.length network_out_bytes));
    let raw_sent = Ghost.hide (Seq.slice network_out_bytes 0 (SZ.v written_raw));
    assert (pure (Seq.equal
      (Ghost.reveal raw_sent)
      (Seq.slice network_out_bytes 0 58)));
    assert (pure (CS.raw_records_exactly (Ghost.reveal raw_sent) T.ApplicationData 1));

    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin_sent));
      })));
    assert (pure (CS.event_raw_delta_legal
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin_sent));
      })
      (Ghost.reveal raw_sent)
      B.empty));
    W.lemma_serialize_finished_len (Ghost.reveal fin_sent);
    assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
      B.length (W.serialize_handshake (M.Finished (Ghost.reveal fin_sent))) <= max_transcript_len));
    assert (pure (can_send_client_finished st0 (Ghost.reveal fin_sent) (Ghost.reveal raw_sent)));
    assert (pure (SZ.v written_raw <= B.length network_out_bytes));

    mark_sent_client_finished
      c
      serialized_finished
      36sz
      lfin
      network_out
      written_raw
      #fin_sent
      #raw_sent;
    true
  } else {
    false
  }
}

fn mark_sent_application_data_after_record_advanced
  (c:connection_state)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (written:SZ.t)
  (#raw_sent:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires MR.pts_to c.ghost_state #1.0R st0 **
           connection_config_exactly c.config st0.CS.cs_model.CS.model_config **
           control_exactly
             c.control
             st0.CS.cs_model.CS.model_control
             st0.CS.cs_model.CS.model_failure **
           record_layer_exactly
             c.records
             ({ st0.CS.cs_model.CS.model_record with
                 CS.record_write =
                   R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write }) **
           handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake **
           application_exactly c.application st0.CS.cs_model.CS.model_application **
           ArrPts.pts_to payload 'payload_bytes **
           ArrPts.pts_to network_out 'network_out_bytes **
           pure (CS.connection_state_consistent st0 /\
                 B.length 'payload_bytes == SZ.v payload_len /\
                 can_send_application_data
                   st0
                   (Ghost.reveal 'payload_bytes)
                   (Ghost.reveal raw_sent) /\
                 SZ.v written == SZ.v payload_len + 21 /\
                 SZ.v written <= B.length 'network_out_bytes /\
                 Seq.equal
                   (Ghost.reveal raw_sent)
                   (Seq.slice (Ghost.reveal 'network_out_bytes) 0 (SZ.v written)))
  ensures connection_exactly
            c
            (sent_application_data_state
              st0
              (Ghost.reveal 'payload_bytes)
              (Ghost.reveal raw_sent)) **
          ArrPts.pts_to payload 'payload_bytes **
          ArrPts.pts_to network_out 'network_out_bytes
{
  assert (pure (can_send_application_data
    st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal raw_sent)));
  assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));

  unfold (application_exactly c.application st0.CS.cs_model.CS.model_application);
  assert (pure (CS.pending_application_consistent
    (sent_application_data_state
      st0
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application));
  fold (application_exactly
    c.application
    (sent_application_data_state
      st0
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application);

  assert (pure ((sent_application_data_state
    st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((sent_application_data_state
    st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_control ==
    st0.CS.cs_model.CS.model_control));
  assert (pure ((sent_application_data_state
    st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_failure ==
    st0.CS.cs_model.CS.model_failure));
  assert (pure ((sent_application_data_state
    st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake ==
    st0.CS.cs_model.CS.model_handshake));
  assert (pure ((sent_application_data_state
    st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record ==
    { st0.CS.cs_model.CS.model_record with
        CS.record_write = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write }));

  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (sent_application_data_state
        st0
        (Ghost.reveal 'payload_bytes)
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config);
  rewrite (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure)
    as (control_exactly
      c.control
      (sent_application_data_state
        st0
        (Ghost.reveal 'payload_bytes)
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_control
      (sent_application_data_state
        st0
        (Ghost.reveal 'payload_bytes)
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_failure);
  rewrite (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake)
    as (handshake_exactly
      c.handshake
      (sent_application_data_state
        st0
        (Ghost.reveal 'payload_bytes)
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (sent_application_data_state
      st0
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal raw_sent)).CS.cs_model);

  lemma_sent_application_data_state_evolves
    st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal raw_sent);
  MR.update
    c.ghost_state
    (sent_application_data_state
      st0
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal raw_sent));
  fold (connection_exactly
    c
    (sent_application_data_state
      st0
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal raw_sent)))
}

fn mark_sent_close_notify_after_record_advanced
  (c:connection_state)
  (network_out:array U8.t)
  (written:SZ.t)
  (#raw_sent:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires MR.pts_to c.ghost_state #1.0R st0 **
           connection_config_exactly c.config st0.CS.cs_model.CS.model_config **
           control_exactly
             c.control
             st0.CS.cs_model.CS.model_control
             st0.CS.cs_model.CS.model_failure **
           record_layer_exactly
             c.records
             ({ st0.CS.cs_model.CS.model_record with
                 CS.record_write =
                   R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write }) **
           handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake **
           application_exactly c.application st0.CS.cs_model.CS.model_application **
           ArrPts.pts_to network_out 'network_out_bytes **
           pure (CS.connection_state_consistent st0 /\
                 can_send_close_notify
                   st0
                   (Ghost.reveal raw_sent) /\
                 SZ.v written == 23 /\
                 SZ.v written <= B.length 'network_out_bytes /\
                 Seq.equal
                   (Ghost.reveal raw_sent)
                   (Seq.slice (Ghost.reveal 'network_out_bytes) 0 (SZ.v written)))
  ensures connection_exactly
            c
            (sent_close_notify_state
              st0
              (Ghost.reveal raw_sent)) **
          ArrPts.pts_to network_out 'network_out_bytes
{
  assert (pure (can_send_close_notify
    st0
    (Ghost.reveal raw_sent)));
  assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));

  unfold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  assert (pure (st0.CS.cs_model.CS.model_failure == None));
  c.control.control_tag := 3uy;
  c.control.handshake_stage_tag := 0uy;
  c.control.failure_present := false;
  c.control.failure_code := 0uy;
  c.control.failure_alert := 0uy;

  assert (pure (control_state_matches
    3uy
    0uy
    false
    0uy
    0uy
    CS.ControlClosing));
  fold (control_exactly
    c.control
    CS.ControlClosing
    st0.CS.cs_model.CS.model_failure);

  assert (pure ((sent_close_notify_state
    st0
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((sent_close_notify_state
    st0
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_control ==
    CS.ControlClosing));
  assert (pure ((sent_close_notify_state
    st0
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_failure ==
    st0.CS.cs_model.CS.model_failure));
  assert (pure ((sent_close_notify_state
    st0
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake ==
    st0.CS.cs_model.CS.model_handshake));
  assert (pure ((sent_close_notify_state
    st0
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  assert (pure ((sent_close_notify_state
    st0
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record ==
    { st0.CS.cs_model.CS.model_record with
        CS.record_write = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write }));

  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (sent_close_notify_state
        st0
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config);
  rewrite (control_exactly
    c.control
    CS.ControlClosing
    st0.CS.cs_model.CS.model_failure)
    as (control_exactly
      c.control
      (sent_close_notify_state
        st0
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_control
      (sent_close_notify_state
        st0
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_failure);
  rewrite (record_layer_exactly
    c.records
    ({ st0.CS.cs_model.CS.model_record with
        CS.record_write =
          R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write }))
    as (record_layer_exactly
      c.records
      (sent_close_notify_state
        st0
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record);
  rewrite (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake)
    as (handshake_exactly
      c.handshake
      (sent_close_notify_state
        st0
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (sent_close_notify_state
        st0
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application);

  fold (connection_model_exactly
    c
    (sent_close_notify_state
      st0
      (Ghost.reveal raw_sent)).CS.cs_model);

  lemma_sent_close_notify_state_evolves
    st0
    (Ghost.reveal raw_sent);
  MR.update
    c.ghost_state
    (sent_close_notify_state
      st0
      (Ghost.reveal raw_sent));
  fold (connection_exactly
    c
    (sent_close_notify_state
      st0
      (Ghost.reveal raw_sent)))
}

fn try_send_application_data
  (c:connection_state)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to payload 'payload_bytes **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len)
  returns ok: bool
  ensures (if ok then
            exists* raw_sent network_out_bytes.
              connection_exactly
                c
                (sent_application_data_state
                  st0
                  (Ghost.reveal 'payload_bytes)
                  raw_sent) **
              ArrPts.pts_to payload 'payload_bytes **
              ArrPts.pts_to network_out network_out_bytes **
              pure (B.length network_out_bytes == SZ.v network_out_len /\
                    SZ.v payload_len + 21 <= B.length network_out_bytes /\
                    can_send_application_data
                      st0
                      (Ghost.reveal 'payload_bytes)
                      raw_sent /\
                    Seq.equal
                      raw_sent
                      (Seq.slice network_out_bytes 0 (SZ.v payload_len + 21)))
          else
            connection_exactly c st0 **
            ArrPts.pts_to payload 'payload_bytes **
            ArrPts.pts_to network_out 'old_network_out)
{
  let ready = can_send_application_data_runtime c payload_len network_out_len;
  if ready {
    assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
    assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    assert (pure (B.length (Ghost.reveal 'payload_bytes) == SZ.v payload_len));
    assert (pure (B.length (Ghost.reveal 'payload_bytes) <= SM.max_application_data_fragment_len));
    lemma_application_data_record_count_small (Ghost.reveal 'payload_bytes);
    assert (pure (SM.application_data_record_count (Ghost.reveal 'payload_bytes) == 1));
    assert (pure (SZ.v payload_len + 21 <= SZ.v network_out_len));

    assert (pure (SZ.fits (SZ.v payload_len + 16)));
    let ciphertext_len = SZ.add payload_len 16sz;
    assert (pure (SZ.v ciphertext_len == SZ.v payload_len + 16));
    assert (pure (SZ.v ciphertext_len <= 16640));
    assert (pure (SZ.v ciphertext_len + 5 <= SZ.v network_out_len));

    let ciphertext = V.alloc 0uy ciphertext_len;
    with old_ciphertext_bytes.
      assert (V.pts_to ciphertext old_ciphertext_bytes);
    V.pts_to_len ciphertext;
    assert (pure (B.length old_ciphertext_bytes == SZ.v ciphertext_len));
    let mut aad = [| 0uy; 0sz |];
    with aad_bytes.
      assert (ArrPts.pts_to aad aad_bytes);
    assert (pure (B.length aad_bytes == 0));

    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

    V.to_array_pts_to ciphertext;
    let sealed =
      Rec.seal_application
        c.records.write
        aad
        0sz
        payload
        payload_len
        (V.vec_to_array ciphertext);
    with sealed_write ciphertext_bytes. _;
    if sealed {
      assert (pure (R.seal
        st0.CS.cs_model.CS.model_record.CS.record_write
        aad_bytes
        { R.content_type = T.ApplicationData;
          R.fragment = Ghost.reveal 'payload_bytes } ==
        Some (ciphertext_bytes, sealed_write)));
      lemma_seal_application_success_next_seq
        st0.CS.cs_model.CS.model_record.CS.record_write
        aad_bytes
        (Ghost.reveal 'payload_bytes)
        ciphertext_bytes
        sealed_write;
      assert (pure (sealed_write ==
        R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write));
      rewrite (Rec.is_record_state c.records.write sealed_write)
        as (Rec.is_record_state
          c.records.write
          (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write));
      fold (record_layer_exactly
        c.records
        { st0.CS.cs_model.CS.model_record with
            CS.record_write =
              R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write });

      assert (pure (B.length ciphertext_bytes == SZ.v ciphertext_len));
      let written =
        Ser.serialize_raw_application_data_record
          (V.vec_to_array ciphertext)
          ciphertext_len
          network_out
          network_out_len;
      with network_out_bytes.
        assert (ArrPts.pts_to network_out network_out_bytes);
      assert (pure (B.length network_out_bytes == SZ.v network_out_len));
      assert (pure (SZ.v written == SZ.v ciphertext_len + 5));
      assert (pure (SZ.v written == SZ.v payload_len + 21));
      assert (pure (SZ.v written <= B.length network_out_bytes));
      let raw_sent = Ghost.hide (Seq.slice network_out_bytes 0 (SZ.v written));
      assert (pure (Seq.equal
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 (SZ.v written))));
      assert (pure (CS.raw_records_exactly
        (Ghost.reveal raw_sent)
        T.ApplicationData
        1));
      assert (pure (CS.legal_event
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsApplicationData (Ghost.reveal 'payload_bytes);
        })));
      assert (pure (CS.protected_record_count
        CL.Sent
        (M.TlsApplicationData (Ghost.reveal 'payload_bytes)) == 1));
      assert (pure (CS.network_message_raw_delta_legal
        st0.CS.cs_model
        {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsApplicationData (Ghost.reveal 'payload_bytes);
        }
        (Ghost.reveal raw_sent)));
      Seq.lemma_eq_intro B.empty B.empty;
      assert (pure (CS.event_raw_delta_legal
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsApplicationData (Ghost.reveal 'payload_bytes);
        })
        (Ghost.reveal raw_sent)
        B.empty));
      assert (pure (can_send_application_data
        st0
        (Ghost.reveal 'payload_bytes)
        (Ghost.reveal raw_sent)));

      V.to_vec_pts_to ciphertext;
      V.free ciphertext;

      mark_sent_application_data_after_record_advanced
        c
        payload
        payload_len
        network_out
        written
        #raw_sent;

      assert (pure (SZ.v written == SZ.v payload_len + 21));
      assert (pure (Seq.equal
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 (SZ.v payload_len + 21))));
      true
    } else {
      assert (pure (sealed_write ==
        st0.CS.cs_model.CS.model_record.CS.record_write));
      rewrite (Rec.is_record_state c.records.write sealed_write)
        as (Rec.is_record_state
          c.records.write
          st0.CS.cs_model.CS.model_record.CS.record_write);
      V.to_vec_pts_to ciphertext;
      V.free ciphertext;
      fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    }
  } else {
    false
  }
}

fn try_send_close_notify
  (c:connection_state)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'old_network_out == SZ.v network_out_len)
  returns ok: bool
  ensures (if ok then
            exists* raw_sent network_out_bytes.
              connection_exactly
                c
                (sent_close_notify_state
                  st0
                  raw_sent) **
              ArrPts.pts_to network_out network_out_bytes **
              pure (B.length network_out_bytes == SZ.v network_out_len /\
                    23 <= B.length network_out_bytes /\
                    can_send_close_notify
                      st0
                      raw_sent /\
                    Seq.equal
                      raw_sent
                      (Seq.slice network_out_bytes 0 23))
          else
            connection_exactly c st0 **
            ArrPts.pts_to network_out 'old_network_out)
{
  let ready = can_send_close_notify_runtime c network_out_len;
  if ready {
    assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
    assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    assert (pure (23 <= SZ.v network_out_len));

    let mut alert_plaintext = [| 0uy; 2sz |];
    write_close_notify_alert alert_plaintext;
    with alert_plaintext_bytes.
      assert (ArrPts.pts_to alert_plaintext alert_plaintext_bytes);
    assert (pure (Seq.equal alert_plaintext_bytes close_notify_alert_fragment));
    assert (pure (B.length alert_plaintext_bytes == 2));

    let ciphertext_len = 18sz;
    assert (pure (SZ.v ciphertext_len == 18));
    assert (pure (SZ.v ciphertext_len == 2 + 16));
    assert (pure (SZ.v ciphertext_len <= 16640));
    assert (pure (SZ.v ciphertext_len + 5 <= SZ.v network_out_len));

    let ciphertext = V.alloc 0uy ciphertext_len;
    with old_ciphertext_bytes.
      assert (V.pts_to ciphertext old_ciphertext_bytes);
    V.pts_to_len ciphertext;
    assert (pure (B.length old_ciphertext_bytes == SZ.v ciphertext_len));
    assert (pure (B.length old_ciphertext_bytes == B.length alert_plaintext_bytes + 16));
    let mut aad = [| 0uy; 0sz |];
    with aad_bytes.
      assert (ArrPts.pts_to aad aad_bytes);
    assert (pure (B.length aad_bytes == 0));

    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

    V.to_array_pts_to ciphertext;
    let sealed =
      Rec.seal_application
        c.records.write
        aad
        0sz
        alert_plaintext
        2sz
        (V.vec_to_array ciphertext);
    with sealed_write ciphertext_bytes. _;
    if sealed {
      assert (pure (R.seal
        st0.CS.cs_model.CS.model_record.CS.record_write
        aad_bytes
        { R.content_type = T.ApplicationData;
          R.fragment = alert_plaintext_bytes } ==
        Some (ciphertext_bytes, sealed_write)));
      lemma_seal_application_success_next_seq
        st0.CS.cs_model.CS.model_record.CS.record_write
        aad_bytes
        alert_plaintext_bytes
        ciphertext_bytes
        sealed_write;
      assert (pure (sealed_write ==
        R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write));
      rewrite (Rec.is_record_state c.records.write sealed_write)
        as (Rec.is_record_state
          c.records.write
          (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write));
      fold (record_layer_exactly
        c.records
        { st0.CS.cs_model.CS.model_record with
            CS.record_write =
              R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write });

      assert (pure (B.length ciphertext_bytes == SZ.v ciphertext_len));
      let written =
        Ser.serialize_raw_application_data_record
          (V.vec_to_array ciphertext)
          ciphertext_len
          network_out
          network_out_len;
      with network_out_bytes.
        assert (ArrPts.pts_to network_out network_out_bytes);
      assert (pure (B.length network_out_bytes == SZ.v network_out_len));
      assert (pure (SZ.v written == SZ.v ciphertext_len + 5));
      assert (pure (SZ.v written == 23));
      assert (pure (SZ.v written <= B.length network_out_bytes));
      let raw_sent = Ghost.hide (Seq.slice network_out_bytes 0 (SZ.v written));
      assert (pure (Seq.equal
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 (SZ.v written))));
      assert (pure (CS.raw_records_exactly
        (Ghost.reveal raw_sent)
        T.ApplicationData
        1));
      assert (pure (CS.legal_event
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsAlert T.CloseNotify;
        })));
      assert (pure (CS.protected_record_count
        CL.Sent
        (M.TlsAlert T.CloseNotify) == 1));
      assert (pure (CS.network_message_raw_delta_legal
        st0.CS.cs_model
        {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsAlert T.CloseNotify;
        }
        (Ghost.reveal raw_sent)));
      Seq.lemma_eq_intro B.empty B.empty;
      assert (pure (CS.event_raw_delta_legal
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsAlert T.CloseNotify;
        })
        (Ghost.reveal raw_sent)
        B.empty));
      assert (pure (can_send_close_notify
        st0
        (Ghost.reveal raw_sent)));

      V.to_vec_pts_to ciphertext;
      V.free ciphertext;

      mark_sent_close_notify_after_record_advanced
        c
        network_out
        written
        #raw_sent;

      assert (pure (SZ.v written == 23));
      assert (pure (Seq.equal
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 23)));
      true
    } else {
      assert (pure (sealed_write ==
        st0.CS.cs_model.CS.model_record.CS.record_write));
      rewrite (Rec.is_record_state c.records.write sealed_write)
        as (Rec.is_record_state
          c.records.write
          st0.CS.cs_model.CS.model_record.CS.record_write);
      V.to_vec_pts_to ciphertext;
      V.free ciphertext;
      fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    }
  } else {
    false
  }
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

fn mark_delivered_application_data
  (c:connection_state)
  (#bytes:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                 CS.legal_event
                   st0.CS.cs_model
                   (CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes)))
  ensures connection_exactly c (delivered_application_data_state st0 bytes)
{
  assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes))));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);

  unfold (application_exactly c.application st0.CS.cs_model.CS.model_application);
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_application.CS.app_pending_plaintext ==
                st0.CS.cs_model.CS.model_application.CS.app_pending_plaintext));
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_application.CS.app_pending_source_record ==
                st0.CS.cs_model.CS.model_application.CS.app_pending_source_record));
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_application.CS.app_pending_source_offset ==
                st0.CS.cs_model.CS.model_application.CS.app_pending_source_offset));
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_application.CS.app_pending_received_raw ==
                st0.CS.cs_model.CS.model_application.CS.app_pending_received_raw));
  assert (pure (CS.pending_application_consistent
    (delivered_application_data_state st0 bytes).CS.cs_model.CS.model_application));
  fold (application_exactly
    c.application
    (delivered_application_data_state st0 bytes).CS.cs_model.CS.model_application);

  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_config ==
                st0.CS.cs_model.CS.model_config));
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_control ==
                st0.CS.cs_model.CS.model_control));
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_record ==
                st0.CS.cs_model.CS.model_record));
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_handshake ==
                st0.CS.cs_model.CS.model_handshake));
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_failure ==
                st0.CS.cs_model.CS.model_failure));
  fold (connection_model_exactly
    c
    (delivered_application_data_state st0 bytes).CS.cs_model);

  lemma_delivered_application_data_state_evolves st0 bytes;
  MR.update
    c.ghost_state
    (delivered_application_data_state st0 bytes);
  fold (connection_exactly c (delivered_application_data_state st0 bytes))
}
