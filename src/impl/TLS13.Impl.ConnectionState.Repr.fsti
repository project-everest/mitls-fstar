module TLS13.Impl.ConnectionState.Repr

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

open TLS13.Impl.ConnectionState.Bounds
open TLS13.Impl.ConnectionState.Model



let connection_state_preorder : FStar.Preorder.preorder CS.connection_state =
  CS.connection_state_evolves

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

let lemma_traffic_key_material_match_present_iff
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

fn alloc_empty_optional_sized_bytes (#cap:nat)
  requires pure (SZ.fits cap)
  returns slot:optional_sized_bytes
  ensures optional_sized_bytes_exactly slot cap None

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
  (cap:nat)
  (#suites:erased (list T.cipher_suite))
  requires cipher_suite_list_exactly src cap suites **
           cipher_suite_list_allocated dst cap **
           pure (SZ.fits cap)
  ensures cipher_suite_list_exactly src cap suites **
          cipher_suite_list_exactly dst cap suites

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
