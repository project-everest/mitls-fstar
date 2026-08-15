module TLS13.Impl.ConnectionState.Repr

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box { box, (!), (:=) }
open FStar.List.Tot

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CryptoSpec = TLS13.Crypto.Spec
module IM = TLS13.Impl.Messages
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Bounds = TLS13.Impl.ConnectionState.Bounds
module Model = TLS13.Impl.ConnectionState.Model
module Tags = TLS13.Impl.ConnectionState.Tags
module Arr = Pulse.Lib.Array
module ArrPts = Pulse.Lib.Array.PtsTo
module R = TLS13.Record.Spec
module Rec = TLS13.Record
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module Slice = Pulse.Lib.Slice
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module V = Pulse.Lib.Vec
module X = TLS13.X509.Spec

// Phase 5: generated wire records + their Semantics accessors.
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished

open TLS13.Impl.ConnectionState.Bounds
open TLS13.Impl.ConnectionState.Model



let connection_state_preorder : FStar.Preorder.preorder CS.connection_state =
  TLS13.Spec.StateMachine.Reachability.connection_state_evolves

let state_ref : Type0 = MR.mref connection_state_preorder

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

(* The peer key share received in a ServerHello.  The buffer is always 65 bytes
   wide -- the widest group ATLAS offers -- with the share zero-padded, and
   [group] records which group the server named in its `KeyShareEntry`.  The
   group is a tag carried alongside the bytes, never recovered from them: field
   names match [optional_fixed_bytes] so the presence/bytes accessors read the
   same. *)
noeq
type kex_share_storage = {
  present: box bool;
  bytes: V.vec U8.t;
  group: box CryptoSpec.kex_group;
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
  // The traffic key buffer is always 32 bytes wide; [alg] records which AEAD
  // algorithm the key belongs to, and hence (via [CryptoSpec.aead_key_len]) how
  // many of those bytes are the logical key.  Pulse vecs cannot report their
  // length at runtime and the buffer is not reallocated per suite, so the
  // negotiated algorithm is tracked here.
  alg: box CryptoSpec.aead_alg;
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
  (* The secp256r1 offer carried alongside the X25519 offer.  The public share
     is a 65-byte SEC1 uncompressed point. *)
  client_p256_private: optional_fixed_bytes;
  client_p256_public: V.vec U8.t;
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
  client_hello_has_server_name: box bool;
  client_hello_server_name_len: box SZ.t;
  client_hello_cipher_suites_len: box SZ.t;
  client_hello_signature_schemes_len: box SZ.t;
  (* The offered legacy_session_id's width, which RFC 8446 4.1.3 makes the
     width the ServerHello must echo.  Mutable, like the other metadata: the
     mirror's [IM.client_hello] struct is allocated once and its own length
     fields cannot be rewritten when a ClientHello arrives. *)
  client_hello_session_id_len: box SZ.t;
  (* The negotiated key-exchange group, as decided by [CM.client_hello_kex_group_for]
     from the offered ClientHello.  Mutable metadata for the same reason as the
     session-id width: the mirror's [IM.client_hello] struct is allocated once
     and its scalars cannot be rewritten.  Unlike the other metadata this one is
     not recoverable from the stored bytes at all -- an all-zero 32-byte X25519
     slot is a legal share -- so the parse path writes it. *)
  client_hello_kex_group: box CryptoSpec.kex_group;
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
  server_selection_present: box bool;
  server_key_share: kex_share_storage;
  server_key_share_private: optional_fixed_bytes;
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
  key_update_response_pending: box bool;
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

let lemma_optional_fixed_bytes_match_present_iff
  (present:bool)
  (storage:B.bytes)
  (n:nat)
  (bytes:option (b:B.bytes{B.length b == n}))
  : Lemma
      (requires optional_fixed_bytes_match present storage n bytes)
      (ensures present == Some? bytes)
=
  match present, bytes with
  | true, Some b -> ()
  | true, None -> ()
  | false, Some b -> ()
  | false, None -> ()

let lemma_server_key_share_option_some
  (server:option GSH.serverHello)
  (storage:(b:B.bytes{B.length b == 65}))
  : Lemma
      (requires (match server with
                 | Some sh -> (match CS.server_hello_kex sh with
                               | Some (| _, k |) -> Some (TLS13.Crypto.Spec.pad_share_65 k)
                               | None -> None)
                 | None -> None) == Some storage)
      (ensures Some? server /\
               server == Some (Some?.v server) /\
               Some? (CS.server_hello_kex (Some?.v server)) /\
               TLS13.Crypto.Spec.pad_share_65
                 (dsnd (Some?.v (CS.server_hello_kex (Some?.v server)))) == storage)
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

type control_snapshot = {
  snapshot_control_tag: U8.t;
  snapshot_handshake_stage_tag: U8.t;
  snapshot_failure_present: bool;
  snapshot_failure_code: U8.t;
  snapshot_failure_alert: U8.t;
}

type certificate_verify_signature_snapshot = {
  cv_signature_scheme: U16.t;
  cv_signature_len: SZ.t;
}

type certificate_chain_snapshot = {
  certificate_chain_bytes_len: SZ.t;
  certificate_chain_cert_count: SZ.t;
}

noeq
type pending_protected_handshake_snapshot = {
  pending_protected_fragment: V.vec U8.t;
  pending_protected_fragment_len: SZ.t;
  pending_protected_parsed: SZ.t;
}

type key_schedule_snapshot = {
  snapshot_shared_secret_present: bool;
  snapshot_handshake_secret_present: bool;
  snapshot_master_secret_present: bool;
  snapshot_client_handshake_traffic_present: bool;
  snapshot_server_handshake_traffic_present: bool;
  snapshot_client_application_traffic_present: bool;
  snapshot_server_application_traffic_present: bool;
}

noextract

let key_schedule_snapshot_matches
  (snapshot:key_schedule_snapshot)
  (st:CS.connection_state)
  : prop =
  snapshot.snapshot_shared_secret_present ==
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  snapshot.snapshot_handshake_secret_present ==
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  snapshot.snapshot_master_secret_present ==
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
  snapshot.snapshot_client_handshake_traffic_present ==
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
  snapshot.snapshot_server_handshake_traffic_present ==
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
  snapshot.snapshot_client_application_traffic_present ==
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
  snapshot.snapshot_server_application_traffic_present ==
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic

noextract

let control_snapshot_matches
  (snapshot:control_snapshot)
  (st:CS.connection_state)
  : prop =
  Tags.control_state_matches
    snapshot.snapshot_control_tag
    snapshot.snapshot_handshake_stage_tag
    snapshot.snapshot_failure_present
    snapshot.snapshot_failure_code
    snapshot.snapshot_failure_alert
    st.CS.cs_model.CS.model_control /\
  Tags.failure_option_matches
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
    pure (Tags.endpoint_role_tag_matches role spec.CS.config_role /\
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
    pure (Tags.control_state_matches
            control_tag
            stage_tag
            failure_present
            failure_code
            failure_alert
            model_control /\
          Tags.failure_option_matches failure_present failure_code failure_alert failure)

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
  exists* present secret alg key iv.
    Box.pts_to slot.present present **
    V.pts_to slot.traffic_secret secret **
    Box.pts_to slot.alg alg **
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
              // The stored algorithm is the one the material was derived
              // under; the runtime key buffer is always 32 bytes, so a
              // 16-byte AES-128-GCM key is zero-padded (CryptoSpec.pad_key_32).
              m.CS.traffic_alg == alg /\
              Seq.equal key (CryptoSpec.pad_key_32 m.CS.traffic_key) /\
              Seq.equal iv m.CS.traffic_iv
            | None -> False
          else
            spec == None))

let lemma_traffic_key_material_match_present_of_some
  (present:bool)
  (secret:B.bytes)
  (alg:CryptoSpec.aead_alg)
  (key:B.bytes)
  (iv:B.bytes)
  (spec:option CS.traffic_key_material)
  : Lemma
      (requires (if present then
                 match spec with
                 | Some m ->
                   Seq.equal secret m.CS.traffic_secret /\
                   m.CS.traffic_alg == alg /\
                   Seq.equal key (CryptoSpec.pad_key_32 m.CS.traffic_key) /\
                   Seq.equal iv m.CS.traffic_iv
                 | None -> False
               else
                 spec == None) /\
               Some? spec /\
               B.length key == 32)
      (ensures present /\
              spec == Some {
                CS.traffic_secret = secret;
                CS.traffic_alg = alg;
                CS.traffic_key = CryptoSpec.logical_key alg key;
                CS.traffic_iv = iv;
              })
=
  match spec with
  | Some m ->
    Seq.lemma_eq_intro secret m.CS.traffic_secret;
    Seq.lemma_eq_intro key (CryptoSpec.pad_key_32 m.CS.traffic_key);
    Seq.lemma_eq_intro iv m.CS.traffic_iv;
    assert (secret == m.CS.traffic_secret);
    assert (key == CryptoSpec.pad_key_32 m.CS.traffic_key);
    assert (iv == m.CS.traffic_iv);
    CryptoSpec.lemma_unpad_pad_key_32 m.CS.traffic_key;
    assert (CryptoSpec.logical_key alg key == m.CS.traffic_key);
    assert (m == {
      CS.traffic_secret = secret;
      CS.traffic_alg = alg;
      CS.traffic_key = CryptoSpec.logical_key alg key;
      CS.traffic_iv = iv;
    })
  | None -> ()

let lemma_traffic_key_material_match_present_iff
  (present:bool)
  (secret:B.bytes)
  (alg:CryptoSpec.aead_alg)
  (key:B.bytes)
  (iv:B.bytes)
  (spec:option CS.traffic_key_material)
  : Lemma
      (requires (if present then
                 match spec with
                 | Some m ->
                   Seq.equal secret m.CS.traffic_secret /\
                   m.CS.traffic_alg == alg /\
                   Seq.equal key (CryptoSpec.pad_key_32 m.CS.traffic_key) /\
                   Seq.equal iv m.CS.traffic_iv
                 | None -> False
               else
                 spec == None))
      (ensures present == Some? spec)
=
  match present, spec with
  | true, Some m -> ()
  | true, None -> ()
  | false, Some m -> ()
  | false, None -> ()

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

fn store_traffic_key_material
  (slot:traffic_key_material_storage)
  (traffic_secret_src:array U8.t)
  (alg:CryptoSpec.aead_alg)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  requires (exists* prev. traffic_key_material_exactly slot prev) **
           ArrPts.pts_to traffic_secret_src material.CS.traffic_secret **
           ArrPts.pts_to traffic_key_src (CryptoSpec.pad_key_32 material.CS.traffic_key) **
           ArrPts.pts_to traffic_iv_src material.CS.traffic_iv **
           pure (material.CS.traffic_alg == alg)
  ensures traffic_key_material_exactly slot (Some (Ghost.reveal material)) **
          ArrPts.pts_to traffic_secret_src material.CS.traffic_secret **
          ArrPts.pts_to traffic_key_src (CryptoSpec.pad_key_32 material.CS.traffic_key) **
          ArrPts.pts_to traffic_iv_src material.CS.traffic_iv

let handshake_start_fields_allocated
  ([@@@mkey] start:handshake_start_storage)
  : slprop =
  sized_bytes_allocated start.server_name max_hostname_len **
  fixed_bytes_allocated start.client_random 32 **
  optional_fixed_bytes_exactly start.client_key_share_private 32 None **
  fixed_bytes_allocated start.client_key_share_public 32 **
  optional_fixed_bytes_exactly start.client_p256_private 32 None **
  fixed_bytes_allocated start.client_p256_public 65 **
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
  optional_fixed_bytes_exactly start.client_p256_private 32 spec.CS.start_client_p256_private **
  fixed_bytes_exactly start.client_p256_public 65 spec.CS.start_client_p256_public **
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

let client_hello_slot_exactly
  (present_box:box bool)
  ([@@@mkey] l:IM.client_hello)
  (spec:option GCH.clientHello)
  : slprop =
  exists* present random session_id server_name key_share p256_key_share
          cipher_suites signature_schemes.
    Box.pts_to present_box present **
    V.pts_to l.IM.client_hello_random random **
    V.pts_to l.IM.client_hello_session_id session_id **
    V.pts_to l.IM.client_hello_server_name server_name **
    V.pts_to l.IM.client_hello_key_share key_share **
    (* The slot's [IM.client_hello] struct is allocated once and its scalar
       fields cannot be rewritten -- the same reason the session-id width lives
       in a metadata box -- so the struct's own
       [client_hello_has_p256_key_share] flag says nothing here.  Whether the
       peer offered a usable secp256r1 share is instead a property of the spec
       message, and the runtime reads it off the [client_hello_kex_group]
       metadata box; the bytes are constrained below. *)
    V.pts_to l.IM.client_hello_p256_key_share p256_key_share **
    V.pts_to l.IM.client_hello_cipher_suites cipher_suites **
    V.pts_to l.IM.client_hello_signature_schemes signature_schemes **
    pure (V.is_full_vec l.IM.client_hello_random /\
          V.is_full_vec l.IM.client_hello_session_id /\
          V.is_full_vec l.IM.client_hello_server_name /\
          V.is_full_vec l.IM.client_hello_key_share /\
          V.is_full_vec l.IM.client_hello_p256_key_share /\
          V.is_full_vec l.IM.client_hello_cipher_suites /\
          V.is_full_vec l.IM.client_hello_signature_schemes /\
          V.length l.IM.client_hello_random == 32 /\
          V.length l.IM.client_hello_session_id == 32 /\
          V.length l.IM.client_hello_server_name == max_hostname_len /\
          V.length l.IM.client_hello_key_share == 32 /\
          V.length l.IM.client_hello_p256_key_share == 65 /\
          V.length l.IM.client_hello_cipher_suites == max_cipher_suites /\
          V.length l.IM.client_hello_signature_schemes == max_signature_schemes /\
          B.length random == 32 /\
          B.length session_id == 32 /\
          B.length server_name == max_hostname_len /\
          B.length key_share == 32 /\
          B.length p256_key_share == 65 /\
          Seq.length cipher_suites == max_cipher_suites /\
          Seq.length signature_schemes == max_signature_schemes /\
          (if present then
            match spec with
            | Some m ->
              Seq.equal random (Sem.clientHello_random m) /\
              Seq.equal session_id
                (Sem.pad_session_id_32 (Sem.clientHello_session_id m)) /\
              IM.optional_byte_prefix_matches
                (client_hello_has_sni m)
                server_name
                (client_hello_server_name_len_for m)
                (Sem.clientHello_server_name m) /\
              (match Sem.clientHello_key_share_x25519 m with
               | Some k -> B.length k == 32 /\ Seq.equal key_share k
               | None -> False) /\
              (* The peer's secp256r1 offer, when it made a usable one.  Stated
                 as a property of the message rather than of a struct scalar, so
                 no flag has to be rewritten when a ClientHello is stored; an
                 entry at any length other than 65 is no offer at all (RFC 8446
                 4.2.8), and places no demand on the mirror. *)
              (match Sem.clientHello_key_share_secp256r1 m with
               | Some k -> B.length k == 65 ==> Seq.equal p256_key_share k
               | None -> True) /\
              IM.cipher_suites_match
                cipher_suites
                (SZ.v (client_hello_cipher_suites_len_for m))
                (Sem.clientHello_cipher_suites m) /\
              (match Sem.clientHello_sig_algs m with
               | Some sas ->
                 IM.signature_schemes_match
                   signature_schemes
                   (SZ.v (client_hello_signature_schemes_len_for m))
                   sas
               | None -> False)
            | None -> False
          else
            // The slot is allocated but empty: the session-id mirror still
            // holds its all-zero initial content, which is exactly what
            // [TLS13.Impl.ConnectionState.Model.stored_client_hello_session_id]
            // reports (at length 0) for a state with no stored ClientHello.
            // Pinning it here makes the runtime session-id reader total.
            spec == None /\ Seq.equal session_id (Seq.create 32 0uy)))

let client_hello_metadata_exactly
  (has_server_name_box:box bool)
  (server_name_len_box:box SZ.t)
  (cipher_suites_len_box:box SZ.t)
  (signature_schemes_len_box:box SZ.t)
  (session_id_len_box:box SZ.t)
  (kex_group_box:box CryptoSpec.kex_group)
  (spec:option GCH.clientHello)
  : slprop =
  exists* has_server_name server_name_len cipher_suites_len signature_schemes_len
          session_id_len kex_group.
    Box.pts_to has_server_name_box has_server_name **
    Box.pts_to server_name_len_box server_name_len **
    Box.pts_to cipher_suites_len_box cipher_suites_len **
    Box.pts_to signature_schemes_len_box signature_schemes_len **
    Box.pts_to session_id_len_box session_id_len **
    Box.pts_to kex_group_box kex_group **
    pure (match spec with
      | Some m ->
        has_server_name == client_hello_has_sni m /\
        server_name_len == client_hello_server_name_len_for m /\
        cipher_suites_len == client_hello_cipher_suites_len_for m /\
        signature_schemes_len == client_hello_signature_schemes_len_for m /\
        session_id_len == client_hello_session_id_len_for m /\
        kex_group == client_hello_kex_group_for m
      | None ->
        has_server_name == false /\
        server_name_len == 0sz /\
        cipher_suites_len == 0sz /\
        signature_schemes_len == 0sz /\
        session_id_len == 0sz /\
        kex_group == CryptoSpec.KexX25519)

let server_hello_slot_exactly
  ([@@@mkey] slot:box (option IM.server_hello))
  (spec:option GSH.serverHello)
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
  (spec:option GEE.encryptedExtensions)
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
  (spec:option GCert.certificate)
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
  (spec:option GCV.certificateVerify)
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
  (spec:option GFin.finished)
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
  client_hello_metadata_exactly
    msgs.client_hello_has_server_name
    msgs.client_hello_server_name_len
    msgs.client_hello_cipher_suites_len
    msgs.client_hello_signature_schemes_len
    msgs.client_hello_session_id_len
    msgs.client_hello_kex_group
    hs.CS.hs_client_hello **
  server_hello_slot_exactly msgs.server_hello hs.CS.hs_server_hello **
  encrypted_extensions_slot_exactly msgs.encrypted_extensions hs.CS.hs_encrypted_extensions **
  certificate_slot_exactly msgs.certificate hs.CS.hs_certificate **
  certificate_verify_slot_exactly msgs.certificate_verify hs.CS.hs_certificate_verify **
  finished_slot_exactly msgs.server_finished hs.CS.hs_server_finished **
  finished_slot_exactly msgs.client_finished hs.CS.hs_client_finished

(* The group/share pair the server selected, as stored: [None] until an
   acceptable ServerHello has been received. *)
// [noextract] for the same reason as [server_key_share_private_option] below:
// these are pure projections over the *ghost* connection model state used only
// in slprops, and extracting them drags the `noextract` generated high records
// (GSH.serverHello, ...) into the C bundle as undefined struct members.
noextract
let server_kex (hs:CS.handshake_state)
  : option (g:CryptoSpec.kex_group & CryptoSpec.kex_public g) =
  match hs.CS.hs_server_hello with
  | Some sh -> CS.server_hello_kex sh
  | None -> None

noextract
let server_kex_bytes (hs:CS.handshake_state)
  : option (B.bytes_of_len 65) =
  match server_kex hs with
  | Some (| _, k |) -> Some (CryptoSpec.pad_share_65 k)
  | None -> None

let server_key_share_exactly
  ([@@@mkey] slot:kex_share_storage)
  (hs:CS.handshake_state)
  : slprop =
  exists* g.
    Box.pts_to slot.group g **
    optional_fixed_bytes_exactly
      ({ present = slot.present; bytes = slot.bytes })
      65
      (server_kex_bytes hs) **
    pure (match server_kex hs with
          | Some (| g', _ |) -> g == g'
          | None -> True)

// [noextract]: pure spec-level projection over the *ghost* connection model
// state (`CS.handshake_state`) returning spec `B.bytes`.  It is used only in
// specifications/slprops (it currently has no caller at all) and must never be
// runtime C.  It was the sole extracted referencer of `CS.handshake_state` /
// `CS.server_handshake_selection`, which transitively embed the `noextract`
// generated high records (GCH.clientHello, ...).  Removing it from extraction
// lets KaRaMeL's dead-code elimination drop those ghost model record types
// (exactly as it already drops `connection_model`, `connection_state`, ...),
// so their non-Low* fields never surface as undefined C struct members.
noextract
let server_key_share_private_option
  (hs:CS.handshake_state)
  : option (b:B.bytes{B.length b == 32}) =
  match hs.CS.hs_server_selection with
  | Some selection -> selection.CS.server_key_share_private
  | None -> None

let server_selection_absent
  (hs:CS.handshake_state)
  : prop =
  match hs.CS.hs_server_selection with
  | Some _ -> False
  | None -> True

let server_selection_private_absent
  (selection:CS.server_handshake_selection)
  : prop =
  match selection.CS.server_key_share_private with
  | Some _ -> False
  | None -> True

(**
  The selected group is a purely ghost field of [CS.server_handshake_selection]:
  the runtime stores the 32 private bytes and a presence flag, never a group tag,
  because ATLAS's server role transmits exactly one share.  [CS.legal_event] and
  [CS.server_hello_matches_selection] are group-indexed, so without this
  representation-level pin nothing downstream -- the scheduler, the ServerHello
  writer, the ECDH -- could learn which group its own stored selection names.

  This is the single place the server role's X25519-only key exchange is
  recorded; G2 stage S6 replaces it with a stored group tag and deletes the
  matching conjuncts in [TLS13.Impl.ConnectionState.Model.valid_selection] and
  [TLS13.Impl.Server.Types.server_local_event_input_ready].
**)
let server_selection_group_pinned
  (selection:option CS.server_handshake_selection)
  : prop =
  match selection with
  | Some sel -> CS.server_selected_kex_group sel == CryptoSpec.KexX25519
  | None -> True

let server_selection_presence_exactly
  ([@@@mkey] present_box:box bool)
  (selection:option CS.server_handshake_selection)
  : slprop =
  exists* present.
    Box.pts_to present_box present **
    pure (present == Some? selection /\
          server_selection_group_pinned selection)

let server_key_share_private_exactly
  ([@@@mkey] slot:optional_fixed_bytes)
  (hs:CS.handshake_state)
  : slprop =
  match hs.CS.hs_server_selection with
  | Some selection ->
    (match selection.CS.server_key_share_private with
     | Some sk -> optional_fixed_bytes_exactly slot 32 (Some sk)
     | None -> optional_fixed_bytes_exactly slot 32 None)
  | None ->
    optional_fixed_bytes_exactly slot 32 None

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
    server_selection_presence_exactly
      handshake.server_selection_present
      hs.CS.hs_server_selection **
    server_key_share_exactly handshake.server_key_share hs **
    server_key_share_private_exactly handshake.server_key_share_private hs **
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
  exists* source_offset key_update_response_pending.
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
    Box.pts_to app.key_update_response_pending key_update_response_pending **
    pure (SZ.v source_offset == spec.CS.app_pending_source_offset /\
          key_update_response_pending == spec.CS.app_key_update_response_pending /\
          TLS13.Spec.StateMachine.Correspondence.pending_application_consistent spec)

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
  pure (TLS13.Spec.StateMachine.Reachability.connection_state_consistent st)

let is_connection_state (c:connection_state) : slprop =
  exists* st. connection_exactly c st

noextract

let connection_released
  ([@@@mkey] c:connection_state)
  (st:CS.connection_state)
  : slprop =
  MR.pts_to c.ghost_state #1.0R st

fn free_connection (c:connection_state)
  requires connection_exactly c 'st
  ensures connection_released c 'st

noextract

let default_connection_config : CS.connection_config = {
  CS.config_role = CS.ClientEndpoint;
  CS.config_server_name = B.empty;
  CS.config_trust_store = { X.anchors = B.empty };
  CS.config_validation_time = { X.seconds_since_epoch = 0 };
  CS.config_cipher_suites = [T.TLS_CHACHA20_POLY1305_SHA256; T.TLS_AES_128_GCM_SHA256];
  CS.config_signature_schemes = [T.Rsa_pss_rsae_sha256; T.Ecdsa_secp256r1_sha256];
  CS.config_server = None;
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
    CS.config_server = None;
  }

noextract

let configured_initial_state
  (server_name:B.bytes)
  (trust_anchors:B.bytes)
  (validation_time_seconds:SZ.t)
  : CS.connection_state =
  CS.initial (configured_connection_config server_name trust_anchors validation_time_seconds)

noextract

let server_connection_config
  (certificate_chain:B.bytes)
  (credential_identity:B.bytes)
  : CS.connection_config =
  {
    CS.config_role = CS.ServerEndpoint;
    CS.config_server_name = B.empty;
    CS.config_trust_store = { X.anchors = B.empty };
    CS.config_validation_time = { X.seconds_since_epoch = 0 };
    CS.config_cipher_suites = default_connection_config.CS.config_cipher_suites;
    CS.config_signature_schemes = default_connection_config.CS.config_signature_schemes;
    CS.config_server =
      Some {
        CS.server_certificate_chain = certificate_chain;
        CS.server_credential_identity = credential_identity;
        (* Parity gap G5: the schemes the server may select are exactly the one
           its credential can produce.  A TLS 1.3 credential's algorithm is
           fixed by its SubjectPublicKeyInfo, so this is a function of the
           configured identity and needs no extra configuration field. *)
        CS.server_allowed_signature_schemes =
          [CryptoSpec.credential_signature_scheme credential_identity];
        CS.server_supported_cipher_suites =
          default_connection_config.CS.config_cipher_suites;
        CS.server_supported_groups = [T.X25519];
        CS.server_sni_policy = None;
      };
  }

noextract

let server_initial_state
  (certificate_chain:B.bytes)
  (credential_identity:B.bytes)
  : CS.connection_state =
  CS.initial (server_connection_config certificate_chain credential_identity)

(** IMPLEMENTATION-level validity of a server configuration: the protocol-level
    fact that the credential is present (`CS.server_config_present`), conjoined
    with THIS implementation's certificate-chain buffer bound.

    The two halves live at different layers on purpose.  The first is a property
    of the protocol; the second is a property of our buffers -- the wire format
    permits a considerably longer chain than `max_server_certificate_chain_len`,
    so this conjunct is genuinely an implementation restriction and is not
    derivable from spec-level reachability.  It is exactly the precondition the
    Pulse constructors `TLS13.Impl.Server.new_server` (and its erased-credential
    variant) already impose on their caller, and they now discharge this
    predicate as a postcondition, which is what lets the system-level
    stream-integrity theorem be instantiated at a state the implementation can
    actually build. **)
let server_config_valid (st:CS.connection_state) : prop =
  CS.server_config_present st /\
  (match st.CS.cs_model.CS.model_config.CS.config_server with
   | Some cfg ->
     B.length cfg.CS.server_certificate_chain <= max_server_certificate_chain_len
   | None -> False)

(** The state the Pulse server constructor builds satisfies the predicate, given
    exactly that constructor's own precondition.  Definitional: the config is
    built with `config_server = Some { server_certificate_chain = chain; ... }`. **)
let lemma_server_initial_state_config_valid
  (certificate_chain:B.bytes)
  (credential_identity:B.bytes)
  : Lemma
      (requires B.length certificate_chain <= max_server_certificate_chain_len)
      (ensures
        server_config_valid
          (server_initial_state certificate_chain credential_identity))
=
  ()

let lemma_default_initial_consistent ()
  : Lemma (TLS13.Spec.StateMachine.Reachability.connection_state_consistent default_initial_state)
=
  ()

let lemma_configured_initial_consistent
  (server_name:B.bytes)
  (trust_anchors:B.bytes)
  (validation_time_seconds:SZ.t)
  : Lemma
      (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
        (configured_initial_state server_name trust_anchors validation_time_seconds))
=
  ()

let lemma_server_initial_consistent
  (certificate_chain:B.bytes)
  (credential_identity:B.bytes)
  : Lemma
      (TLS13.Spec.StateMachine.Reachability.connection_state_consistent
        (server_initial_state certificate_chain credential_identity))
=
  ()

fn alloc_empty_sized_bytes (cap:SZ.t) (#cap_spec:erased nat)
  requires pure (SZ.v cap == reveal cap_spec)
  returns slot:sized_bytes
  ensures sized_bytes_exactly slot cap_spec B.empty

fn copy_array_to_sized_bytes
  (#cap_spec:erased nat)
  (src:array U8.t)
  (dst:sized_bytes)
  (cap:SZ.t)
  (src_len:SZ.t)
  requires ArrPts.pts_to src 'src_bytes **
           sized_bytes_allocated dst cap_spec **
           pure (SZ.v cap == reveal cap_spec /\
                 B.length 'src_bytes == SZ.v src_len /\
                 SZ.v src_len <= reveal cap_spec)
  ensures ArrPts.pts_to src 'src_bytes **
          sized_bytes_exactly dst cap_spec (Ghost.reveal 'src_bytes)

fn alloc_empty_optional_sized_bytes (cap:SZ.t) (#cap_spec:erased nat)
  requires pure (SZ.v cap == reveal cap_spec)
  returns slot:optional_sized_bytes
  ensures optional_sized_bytes_exactly slot cap_spec None

fn copy_optional_sized_bytes_to_array
  (#cap:erased nat)
  (slot:optional_sized_bytes)
  (dst:array U8.t)
  (dst_len:SZ.t)
  (#bytes_opt:erased (option B.bytes))
  requires optional_sized_bytes_exactly slot (reveal cap) bytes_opt **
           ArrPts.pts_to dst 'old_dst **
           pure (B.length 'old_dst == SZ.v dst_len /\
                 reveal cap <= SZ.v dst_len /\
                 Some? (Ghost.reveal bytes_opt))
  returns copied_len:SZ.t
  ensures exists* dst_bytes.
          optional_sized_bytes_exactly slot (reveal cap) bytes_opt **
          ArrPts.pts_to dst dst_bytes **
          pure (B.length dst_bytes == SZ.v dst_len /\
                SZ.v copied_len <= B.length dst_bytes /\
                (match Ghost.reveal bytes_opt with
                | Some bytes ->
                  SZ.v copied_len == B.length bytes /\
                  Seq.equal (Seq.slice dst_bytes 0 (SZ.v copied_len)) bytes
                | None -> False))

fn alloc_empty_optional_fixed32 ()
  requires emp
  returns slot:optional_fixed_bytes
  ensures optional_fixed_bytes_exactly slot 32 None

fn alloc_empty_secret ()
  requires emp
  returns slot:optional_secret_storage
  ensures optional_secret_exactly slot None

fn alloc_empty_traffic_key_material ()
  requires emp
  returns slot:traffic_key_material_storage
  ensures traffic_key_material_exactly slot None

fn alloc_default_cipher_suites ()
  requires emp
  returns slot:u16_list_storage
  ensures cipher_suite_list_exactly
            slot
            max_cipher_suites
            default_connection_config.CS.config_cipher_suites

fn alloc_default_signature_schemes ()
  requires emp
  returns slot:u16_list_storage
  ensures signature_scheme_list_exactly
            slot
            max_signature_schemes
            default_connection_config.CS.config_signature_schemes

fn alloc_default_config_storage ()
  requires emp
  returns cfg:connection_config_storage
  ensures connection_config_exactly cfg default_connection_config

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

fn alloc_control_new ()
  requires emp
  returns control:control_storage
  ensures control_exactly control CS.ControlNew None

fn alloc_key_schedule_empty ()
  requires emp
  returns keys:key_schedule_storage
  ensures key_schedule_exactly keys CS.empty_key_schedule_state

fn alloc_handshake_start_empty ()
  requires emp
  returns start:handshake_start_storage
  ensures handshake_start_exactly start None

fn alloc_client_hello_slot_empty ()
  requires emp
  returns ch_slot:client_hello_slot_storage
  ensures client_hello_slot_exactly ch_slot.ch_present ch_slot.ch_value None

fn alloc_handshake_messages_empty ()
  requires emp
  returns msgs:handshake_message_storage
  ensures handshake_messages_exactly msgs CS.empty_handshake_state

fn alloc_peer_empty ()
  requires emp
  returns peer:peer_storage
  ensures peer_exactly peer None

fn alloc_handshake_buffers_empty ()
  requires emp
  returns buffers:handshake_buffer_storage
  ensures handshake_buffers_exactly buffers CS.empty_handshake_buffer_state

fn alloc_handshake_empty ()
  requires emp
  returns handshake:handshake_storage
  ensures handshake_exactly handshake CS.empty_handshake_state

fn alloc_application_empty ()
  requires emp
  returns app:application_storage
  ensures application_exactly app CS.empty_application_state

fn new_client_default ()
  requires emp
  returns c:connection_state
  ensures connection_exactly c default_initial_state

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

fn new_server
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (credential_identity:array U8.t)
  (credential_identity_len:SZ.t)
  requires ArrPts.pts_to certificate_chain 'certificate_chain_bytes **
           ArrPts.pts_to credential_identity 'credential_identity_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                  B.length 'credential_identity_bytes == SZ.v credential_identity_len /\
                  B.length 'certificate_chain_bytes <= max_server_certificate_chain_len)
  returns c:connection_state
  ensures ArrPts.pts_to certificate_chain 'certificate_chain_bytes **
          ArrPts.pts_to credential_identity 'credential_identity_bytes **
          connection_exactly
              c
              (server_initial_state
                (Ghost.reveal 'certificate_chain_bytes)
                (Ghost.reveal 'credential_identity_bytes))

fn new_server_erased_credential_identity
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (#credential_identity:erased CS.server_credential_identity)
  requires ArrPts.pts_to certificate_chain 'certificate_chain_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                    B.length 'certificate_chain_bytes <= max_server_certificate_chain_len)
  returns c:connection_state
  ensures ArrPts.pts_to certificate_chain 'certificate_chain_bytes **
          connection_exactly
                c
                (server_initial_state
                  (Ghost.reveal 'certificate_chain_bytes)
                  (Ghost.reveal credential_identity))

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

fn copy_array_prefix_to_transcript
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
                (Ghost.reveal 'src_bytes)
                (CL.raw_slice
                  'dst_bytes
                  (SZ.v dst_offset + SZ.v src_len)
                  max_transcript_len)))

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

fn copy_fixed65_array_to_vec
  (src:array U8.t)
  (dst:V.vec U8.t)
  requires ArrPts.pts_to src 'src_bytes **
           V.pts_to dst 'old_dst **
           pure (B.length 'src_bytes == 65 /\
                 V.is_full_vec dst /\
                 V.length dst == 65 /\
                 B.length 'old_dst == 65)
  ensures ArrPts.pts_to src 'src_bytes **
          V.pts_to dst 'src_bytes **
          pure (V.is_full_vec dst /\ V.length dst == 65)

(* Copy a 32-byte X25519 share into the front of a 65-byte, zero-initialised
   destination: the runtime image of [CryptoSpec.pad_share_65] for the narrow
   group. *)
fn copy_padded32_array_to_vec65
  (src:array U8.t)
  (dst:V.vec U8.t)
  (#src_bytes:erased (B.bytes_of_len 32))
  requires ArrPts.pts_to src src_bytes **
           V.pts_to dst 'old_dst **
           pure (V.is_full_vec dst /\
                 V.length dst == 65 /\
                 Seq.equal 'old_dst (Seq.create 65 0uy))
  ensures ArrPts.pts_to src src_bytes **
          V.pts_to dst (CryptoSpec.pad_share_65 (Ghost.reveal src_bytes)) **
          pure (V.is_full_vec dst /\ V.length dst == 65)

fn store_optional_fixed32_from_array
  (src:array U8.t)
  (slot:optional_fixed_bytes)
  (#bytes:erased (b:B.bytes{B.length b == 32}))
  requires ArrPts.pts_to src bytes **
           optional_fixed_bytes_exactly slot 32 None
  ensures ArrPts.pts_to src bytes **
          optional_fixed_bytes_exactly slot 32 (Some (Ghost.reveal bytes))

fn copy_cipher_suite_list_storage
  (src:u16_list_storage)
  (dst:u16_list_storage)
  (cap:SZ.t)
  (#cap_spec:erased nat)
  (#suites:erased (list T.cipher_suite))
  requires cipher_suite_list_exactly src cap_spec suites **
           cipher_suite_list_allocated dst cap_spec **
           pure (SZ.v cap == reveal cap_spec)
  ensures cipher_suite_list_exactly src cap_spec suites **
          cipher_suite_list_exactly dst cap_spec suites

fn copy_signature_scheme_list_storage
  (src:u16_list_storage)
  (dst:u16_list_storage)
  (cap:SZ.t)
  (#cap_spec:erased nat)
  (#schemes:erased (list T.signature_scheme))
  requires signature_scheme_list_exactly src cap_spec schemes **
           signature_scheme_list_allocated dst cap_spec **
           pure (SZ.v cap == reveal cap_spec)
  ensures signature_scheme_list_exactly src cap_spec schemes **
          signature_scheme_list_exactly dst cap_spec schemes

fn copy_hostname_sized_bytes
  (src:sized_bytes)
  (dst:sized_bytes)
  requires sized_bytes_exactly src max_hostname_len 'src_bytes **
           sized_bytes_allocated dst max_hostname_len
  ensures sized_bytes_exactly src max_hostname_len 'src_bytes **
          sized_bytes_exactly dst max_hostname_len 'src_bytes

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
