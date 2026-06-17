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

fn alloc_empty_sized_bytes (cap:SZ.t) (#cap_spec:erased nat)
  requires pure (SZ.v cap == reveal cap_spec)
  returns slot:sized_bytes
  ensures sized_bytes_exactly slot cap_spec B.empty
{
  let bytes = V.alloc 0uy cap;
  let len = Box.alloc 0sz;
  let slot = { bytes; len };
  rewrite (V.pts_to bytes (Seq.create (SZ.v cap) 0uy)) as
    (V.pts_to slot.bytes (Seq.create (SZ.v cap) 0uy));
  rewrite (Box.pts_to len 0sz) as (Box.pts_to slot.len 0sz);
  assert (pure (B.length (Seq.create (SZ.v cap) 0uy) == SZ.v cap));
  Seq.lemma_len_slice (Seq.create (SZ.v cap) 0uy) 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice (Seq.create (SZ.v cap) 0uy) 0 0);
  assert (pure (byte_prefix_matches (Seq.create (SZ.v cap) 0uy) 0sz B.empty));
  fold (sized_bytes_exactly slot cap_spec B.empty);
  slot
}

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
{
  unfold (sized_bytes_allocated dst cap_spec);
  with dst_storage dst_len. _;

  ArrPts.pts_to_len src;
  V.to_array_pts_to dst.bytes;

  let dst_cap = cap;
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
  fold (sized_bytes_exactly dst cap_spec (Ghost.reveal 'src_bytes))
}

fn alloc_empty_optional_sized_bytes (cap:SZ.t) (#cap_spec:erased nat)
  requires pure (SZ.v cap == reveal cap_spec)
  returns slot:optional_sized_bytes
  ensures optional_sized_bytes_exactly slot cap_spec None
{
  let present = Box.alloc false;
  let bytes = V.alloc 0uy cap;
  let len = Box.alloc 0sz;
  let value = { bytes; len };
  let slot = { present; value };
  rewrite (Box.pts_to present false) as (Box.pts_to slot.present false);
  rewrite (V.pts_to bytes (Seq.create (SZ.v cap) 0uy)) as
    (V.pts_to slot.value.bytes (Seq.create (SZ.v cap) 0uy));
  rewrite (Box.pts_to len 0sz) as (Box.pts_to slot.value.len 0sz);
  assert (pure (B.length (Seq.create (SZ.v cap) 0uy) == SZ.v cap));
  fold (optional_sized_bytes_exactly slot cap_spec None);
  slot
}

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
{
  unfold (optional_sized_bytes_exactly slot (reveal cap) (Ghost.reveal bytes_opt));
  with present storage len. _;

  let copy_len = !slot.value.len;
  assert (pure (copy_len == len));
  assert (pure (present));
  assert (pure (
    match Ghost.reveal bytes_opt with
    | Some bytes -> byte_prefix_matches storage copy_len bytes
    | None -> False));
  assert (pure (SZ.v copy_len <= reveal cap));
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

  fold (optional_sized_bytes_exactly slot (reveal cap) (Ghost.reveal bytes_opt));
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
  let items = V.alloc 0x1303us (max_cipher_suites_sz);
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
  let items = V.alloc 0x0804us (max_signature_schemes_sz);
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
  let server_name = alloc_empty_sized_bytes max_hostname_len_sz #max_hostname_len;
  let trust_anchors = alloc_empty_sized_bytes max_trust_anchors_len_sz #max_trust_anchors_len;
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
  assert_norm (Tags.endpoint_role_tag_matches 0uy CS.ClientEndpoint);
  assert (pure (Tags.endpoint_role_tag_matches 0uy default_connection_config.CS.config_role));
  assert (pure (SZ.v 0sz ==
    default_connection_config.CS.config_validation_time.X.seconds_since_epoch));
  fold (connection_config_exactly cfg default_connection_config);
  cfg
}

fn alloc_server_config_storage
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (credential_identity:array U8.t)
  (credential_identity_len:SZ.t)
  requires ArrPts.pts_to certificate_chain 'certificate_chain_bytes **
           ArrPts.pts_to credential_identity 'credential_identity_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'credential_identity_bytes == SZ.v credential_identity_len /\
                 B.length 'certificate_chain_bytes <= max_server_certificate_chain_len)
  returns cfg:connection_config_storage
  ensures ArrPts.pts_to certificate_chain 'certificate_chain_bytes **
          ArrPts.pts_to credential_identity 'credential_identity_bytes **
          connection_config_exactly
            cfg
            (server_connection_config
              (Ghost.reveal 'certificate_chain_bytes)
              (Ghost.reveal 'credential_identity_bytes))
{
  assert (pure (SZ.fits max_hostname_len));
  assert (pure (SZ.fits max_trust_anchors_len));
  let role_tag = Box.alloc 1uy;
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
  rewrite (Box.pts_to role_tag 1uy) as (Box.pts_to cfg.role_tag 1uy);
  rewrite (sized_bytes_exactly server_name max_hostname_len B.empty) as
    (sized_bytes_exactly
      cfg.server_name
      max_hostname_len
      (server_connection_config
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal 'credential_identity_bytes)).CS.config_server_name);
  rewrite (sized_bytes_exactly trust_anchors max_trust_anchors_len B.empty) as
    (sized_bytes_exactly
      cfg.trust_anchors
      max_trust_anchors_len
      (server_connection_config
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal 'credential_identity_bytes)).CS.config_trust_store.X.anchors);
  rewrite (Box.pts_to validation_time_seconds 0sz) as
    (Box.pts_to cfg.validation_time_seconds 0sz);
  rewrite (cipher_suite_list_exactly
    cipher_suites
    max_cipher_suites
    default_connection_config.CS.config_cipher_suites) as
    (cipher_suite_list_exactly
      cfg.cipher_suites
      max_cipher_suites
      (server_connection_config
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal 'credential_identity_bytes)).CS.config_cipher_suites);
  rewrite (signature_scheme_list_exactly
    signature_schemes
    max_signature_schemes
    default_connection_config.CS.config_signature_schemes) as
    (signature_scheme_list_exactly
      cfg.signature_schemes
      max_signature_schemes
      (server_connection_config
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal 'credential_identity_bytes)).CS.config_signature_schemes);
  assert_norm (Tags.endpoint_role_tag_matches 1uy CS.ServerEndpoint);
  assert (pure (Tags.endpoint_role_tag_matches
    1uy
    (server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes)).CS.config_role));
  assert (pure (SZ.v 0sz ==
    (server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes)).CS.config_validation_time.X.seconds_since_epoch));
  fold (connection_config_exactly
    cfg
    (server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes)));
  cfg
}

fn alloc_server_config_storage_erased_credential_identity
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (#credential_identity:erased CS.server_credential_identity)
  requires ArrPts.pts_to certificate_chain 'certificate_chain_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                  B.length 'certificate_chain_bytes <= max_server_certificate_chain_len)
  returns cfg:connection_config_storage
  ensures ArrPts.pts_to certificate_chain 'certificate_chain_bytes **
          connection_config_exactly
            cfg
            (server_connection_config
              (Ghost.reveal 'certificate_chain_bytes)
              (Ghost.reveal credential_identity))
{
  assert (pure (SZ.fits max_hostname_len));
  assert (pure (SZ.fits max_trust_anchors_len));
  let role_tag = Box.alloc 1uy;
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
  rewrite (Box.pts_to role_tag 1uy) as (Box.pts_to cfg.role_tag 1uy);
  rewrite (sized_bytes_exactly server_name max_hostname_len B.empty) as
    (sized_bytes_exactly
      cfg.server_name
      max_hostname_len
      (server_connection_config
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal credential_identity)).CS.config_server_name);
  rewrite (sized_bytes_exactly trust_anchors max_trust_anchors_len B.empty) as
    (sized_bytes_exactly
      cfg.trust_anchors
      max_trust_anchors_len
      (server_connection_config
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal credential_identity)).CS.config_trust_store.X.anchors);
  rewrite (Box.pts_to validation_time_seconds 0sz) as
    (Box.pts_to cfg.validation_time_seconds 0sz);
  rewrite (cipher_suite_list_exactly
    cipher_suites
    max_cipher_suites
    default_connection_config.CS.config_cipher_suites) as
    (cipher_suite_list_exactly
      cfg.cipher_suites
      max_cipher_suites
      (server_connection_config
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal credential_identity)).CS.config_cipher_suites);
  rewrite (signature_scheme_list_exactly
    signature_schemes
    max_signature_schemes
    default_connection_config.CS.config_signature_schemes) as
    (signature_scheme_list_exactly
      cfg.signature_schemes
      max_signature_schemes
      (server_connection_config
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal credential_identity)).CS.config_signature_schemes);
  assert_norm (Tags.endpoint_role_tag_matches 1uy CS.ServerEndpoint);
  assert (pure (Tags.endpoint_role_tag_matches
    1uy
    (server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal credential_identity)).CS.config_role));
  assert (pure (SZ.v 0sz ==
    (server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal credential_identity)).CS.config_validation_time.X.seconds_since_epoch));
  fold (connection_config_exactly
    cfg
    (server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal credential_identity)));
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
  let server_name_slot = alloc_empty_sized_bytes max_hostname_len_sz #max_hostname_len;
  unfold (sized_bytes_exactly server_name_slot max_hostname_len B.empty);
  with empty_server_name_storage empty_server_name_len. _;
  fold (sized_bytes_allocated server_name_slot max_hostname_len);
  copy_array_to_sized_bytes
    #max_hostname_len
    server_name
    server_name_slot
    max_hostname_len_sz
    server_name_len;
  let trust_anchors_slot = alloc_empty_sized_bytes max_trust_anchors_len_sz #max_trust_anchors_len;
  unfold (sized_bytes_exactly trust_anchors_slot max_trust_anchors_len B.empty);
  with empty_trust_anchors_storage empty_trust_anchors_len. _;
  fold (sized_bytes_allocated trust_anchors_slot max_trust_anchors_len);
  copy_array_to_sized_bytes
    #max_trust_anchors_len
    trust_anchors
    trust_anchors_slot
    max_trust_anchors_len_sz
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
  assert_norm (Tags.endpoint_role_tag_matches 0uy CS.ClientEndpoint);
  assert (pure (Tags.endpoint_role_tag_matches
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
  assert_norm (Tags.control_state_matches 0uy 0uy false 0uy 0uy CS.ControlNew);
  assert_norm (Tags.failure_option_matches false 0uy 0uy None);
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
  let server_name = alloc_empty_sized_bytes max_hostname_len_sz #max_hostname_len;
  let client_random = V.alloc 0uy 32sz;
  let client_key_share_private = alloc_empty_optional_fixed32 ();
  let client_key_share_public = V.alloc 0uy 32sz;
  let cipher_suites_items = V.alloc 0us (max_cipher_suites_sz);
  let cipher_suites_len = Box.alloc 0sz;
  let cipher_suites = { items = cipher_suites_items; len = cipher_suites_len };
  let signature_schemes_items = V.alloc 0us (max_signature_schemes_sz);
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
  let client_hello_server_name = V.alloc 0uy (max_hostname_len_sz);
  let client_hello_key_share = V.alloc 0uy 32sz;
  let client_hello_cipher_suites = V.alloc 0us (max_cipher_suites_sz);
  let client_hello_signature_schemes = V.alloc 0us (max_signature_schemes_sz);
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
  let client_hello_has_server_name : box bool = Box.alloc false;
  let client_hello_server_name_len : box SZ.t = Box.alloc 0sz;
  let client_hello_cipher_suites_len : box SZ.t = Box.alloc 0sz;
  let client_hello_signature_schemes_len : box SZ.t = Box.alloc 0sz;
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
    client_hello_has_server_name;
    client_hello_server_name_len;
    client_hello_cipher_suites_len;
    client_hello_signature_schemes_len;
    server_hello;
    encrypted_extensions;
    certificate;
    certificate_verify;
    server_finished;
    client_finished;
  };
  rewrite (client_hello_slot_exactly client_hello_present client_hello None) as
    (client_hello_slot_exactly msgs.client_hello_present msgs.client_hello CS.empty_handshake_state.CS.hs_client_hello);
  rewrite (Box.pts_to client_hello_has_server_name false) as
    (Box.pts_to msgs.client_hello_has_server_name false);
  rewrite (Box.pts_to client_hello_server_name_len 0sz) as
    (Box.pts_to msgs.client_hello_server_name_len 0sz);
  rewrite (Box.pts_to client_hello_cipher_suites_len 0sz) as
    (Box.pts_to msgs.client_hello_cipher_suites_len 0sz);
  rewrite (Box.pts_to client_hello_signature_schemes_len 0sz) as
    (Box.pts_to msgs.client_hello_signature_schemes_len 0sz);
  fold (client_hello_metadata_exactly
    msgs.client_hello_has_server_name
    msgs.client_hello_server_name_len
    msgs.client_hello_cipher_suites_len
    msgs.client_hello_signature_schemes_len
    None);
  rewrite (client_hello_metadata_exactly
    msgs.client_hello_has_server_name
    msgs.client_hello_server_name_len
    msgs.client_hello_cipher_suites_len
    msgs.client_hello_signature_schemes_len
    None) as
    (client_hello_metadata_exactly
      msgs.client_hello_has_server_name
      msgs.client_hello_server_name_len
      msgs.client_hello_cipher_suites_len
      msgs.client_hello_signature_schemes_len
      CS.empty_handshake_state.CS.hs_client_hello);
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
  let validated_hostname = alloc_empty_sized_bytes max_hostname_len_sz #max_hostname_len;
  let leaf_public_key = alloc_empty_sized_bytes max_public_key_len_sz #max_public_key_len;
  let permitted_items = V.alloc 0us (max_signature_schemes_sz);
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
  let client_hello_bytes = alloc_empty_sized_bytes max_client_hello_len_sz #max_client_hello_len;
  let server_hello_bytes = alloc_empty_sized_bytes max_server_hello_len_sz #max_server_hello_len;
  let encrypted_server_handshake_bytes = alloc_empty_sized_bytes max_handshake_flight_len_sz #max_handshake_flight_len;
  let encrypted_server_handshake_parsed = Box.alloc 0sz;
  let certificate_leaf_der = alloc_empty_optional_sized_bytes max_handshake_flight_len_sz #max_handshake_flight_len;
  let certificate_verify_input = alloc_empty_optional_sized_bytes max_certificate_verify_input_len_sz #max_certificate_verify_input_len;
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
  let server_selection_present = Box.alloc false;
  let server_key_share = alloc_empty_optional_fixed32 ();
  let server_key_share_private = alloc_empty_optional_fixed32 ();
  let validated_peer = alloc_peer_empty ();
  let certificate_verify_verified = Box.alloc false;
  let server_finished_verified = Box.alloc false;
  assert (pure (SZ.fits max_transcript_len));
  let transcript = alloc_empty_sized_bytes max_transcript_len_sz #max_transcript_len;
  let buffers = alloc_handshake_buffers_empty ();
  let keys = alloc_key_schedule_empty ();
  let handshake = {
    start;
    messages;
    server_selection_present;
    server_key_share;
    server_key_share_private;
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
  rewrite (Box.pts_to server_selection_present false) as
    (Box.pts_to handshake.server_selection_present false);
  fold (server_selection_presence_exactly
    handshake.server_selection_present
    CS.empty_handshake_state.CS.hs_server_selection);
  rewrite (optional_fixed_bytes_exactly server_key_share 32 None) as
    (server_key_share_exactly handshake.server_key_share CS.empty_handshake_state);
  assert (pure (handshake.server_key_share_private == server_key_share_private));
  rewrite (optional_fixed_bytes_exactly server_key_share_private 32 None) as
    (optional_fixed_bytes_exactly handshake.server_key_share_private 32 None);
  rewrite (optional_fixed_bytes_exactly handshake.server_key_share_private 32 None) as
    (server_key_share_private_exactly
      handshake.server_key_share_private
      CS.empty_handshake_state);
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
  let pending_plaintext = alloc_empty_sized_bytes max_pending_plaintext_len_sz #max_pending_plaintext_len;
  let pending_source_record = alloc_empty_sized_bytes max_pending_plaintext_len_sz #max_pending_plaintext_len;
  let pending_source_offset = Box.alloc 0sz;
  let pending_received_raw = alloc_empty_sized_bytes max_pending_raw_len_sz #max_pending_raw_len;
  let key_update_response_pending = Box.alloc false;
  let app = {
    pending_plaintext;
    pending_source_record;
    pending_source_offset;
    pending_received_raw;
    key_update_response_pending;
  };
  rewrite (sized_bytes_exactly pending_plaintext max_pending_plaintext_len B.empty) as
    (sized_bytes_exactly app.pending_plaintext max_pending_plaintext_len CS.empty_application_state.CS.app_pending_plaintext);
  rewrite (sized_bytes_exactly pending_source_record max_pending_plaintext_len B.empty) as
    (sized_bytes_exactly app.pending_source_record max_pending_plaintext_len CS.empty_application_state.CS.app_pending_source_record);
  rewrite (Box.pts_to pending_source_offset 0sz) as
    (Box.pts_to app.pending_source_offset 0sz);
  rewrite (sized_bytes_exactly pending_received_raw max_pending_raw_len B.empty) as
    (sized_bytes_exactly app.pending_received_raw max_pending_raw_len CS.empty_application_state.CS.app_pending_received_raw);
  rewrite (Box.pts_to key_update_response_pending false) as
    (Box.pts_to app.key_update_response_pending false);
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
{
  lemma_server_initial_consistent
    (Ghost.reveal 'certificate_chain_bytes)
    (Ghost.reveal 'credential_identity_bytes);
  let config =
    alloc_server_config_storage
      certificate_chain
      certificate_chain_len
      credential_identity
      credential_identity_len;
  let control = alloc_control_new ();
  let read = Rec.record_state_new ();
  let write = Rec.record_state_new ();
  let records = { read; write };
  let handshake = alloc_handshake_empty ();
  let application = alloc_application_empty ();
  let ghost_state = MR.alloc #_ #connection_state_preorder
    (server_initial_state
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes));
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
    (server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes))) as
    (connection_config_exactly
      c.config
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal 'credential_identity_bytes)).CS.cs_model.CS.model_config);
  rewrite (control_exactly control CS.ControlNew None) as
    (control_exactly
      c.control
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal 'credential_identity_bytes)).CS.cs_model.CS.model_control
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal 'credential_identity_bytes)).CS.cs_model.CS.model_failure);
  rewrite (Rec.is_record_state read R.initial_direction_state) as
    (Rec.is_record_state
      c.records.read
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal 'credential_identity_bytes)).CS.cs_model.CS.model_record.CS.record_read);
  rewrite (Rec.is_record_state write R.initial_direction_state) as
    (Rec.is_record_state
      c.records.write
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal 'credential_identity_bytes)).CS.cs_model.CS.model_record.CS.record_write);
  fold (record_layer_exactly
    c.records
    (server_initial_state
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes)).CS.cs_model.CS.model_record);
  rewrite (handshake_exactly handshake CS.empty_handshake_state) as
    (handshake_exactly
      c.handshake
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal 'credential_identity_bytes)).CS.cs_model.CS.model_handshake);
  rewrite (application_exactly application CS.empty_application_state) as
    (application_exactly
      c.application
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal 'credential_identity_bytes)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (server_initial_state
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes)).CS.cs_model);
  rewrite (MR.pts_to
    ghost_state
    #1.0R
    (server_initial_state
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes))) as
    (MR.pts_to
      c.ghost_state
      #1.0R
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal 'credential_identity_bytes)));
  fold (connection_exactly
    c
    (server_initial_state
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes)));
  c
}

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
{
  lemma_server_initial_consistent
    (Ghost.reveal 'certificate_chain_bytes)
    (Ghost.reveal credential_identity);
  let config =
    alloc_server_config_storage_erased_credential_identity
      certificate_chain
      certificate_chain_len
      #credential_identity;
  let control = alloc_control_new ();
  let read = Rec.record_state_new ();
  let write = Rec.record_state_new ();
  let records = { read; write };
  let handshake = alloc_handshake_empty ();
  let application = alloc_application_empty ();
  let ghost_state = MR.alloc #_ #connection_state_preorder
    (server_initial_state
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal credential_identity));
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
    (server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal credential_identity))) as
    (connection_config_exactly
      c.config
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal credential_identity)).CS.cs_model.CS.model_config);
  rewrite (control_exactly control CS.ControlNew None) as
    (control_exactly
      c.control
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal credential_identity)).CS.cs_model.CS.model_control
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal credential_identity)).CS.cs_model.CS.model_failure);
  rewrite (Rec.is_record_state read R.initial_direction_state) as
    (Rec.is_record_state
      c.records.read
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal credential_identity)).CS.cs_model.CS.model_record.CS.record_read);
  rewrite (Rec.is_record_state write R.initial_direction_state) as
    (Rec.is_record_state
      c.records.write
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal credential_identity)).CS.cs_model.CS.model_record.CS.record_write);
  fold (record_layer_exactly
    c.records
    (server_initial_state
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal credential_identity)).CS.cs_model.CS.model_record);
  rewrite (handshake_exactly handshake CS.empty_handshake_state) as
    (handshake_exactly
      c.handshake
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal credential_identity)).CS.cs_model.CS.model_handshake);
  rewrite (application_exactly application CS.empty_application_state) as
    (application_exactly
      c.application
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal credential_identity)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (server_initial_state
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal credential_identity)).CS.cs_model);
  rewrite (MR.pts_to
    ghost_state
    #1.0R
    (server_initial_state
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal credential_identity))) as
    (MR.pts_to
      c.ghost_state
      #1.0R
      (server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        (Ghost.reveal credential_identity)));
  fold (connection_exactly
    c
    (server_initial_state
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal credential_identity)));
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
  let src_cap = max_server_hello_len_sz;
  let dst_cap = max_transcript_len_sz;
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
  let src_cap = max_client_hello_len_sz;
  let dst_cap = max_transcript_len_sz;
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
  let dst_cap = max_transcript_len_sz;
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
  (cap:SZ.t)
  (#cap_spec:erased nat)
  (#suites:erased (list T.cipher_suite))
  requires cipher_suite_list_exactly src cap_spec suites **
           cipher_suite_list_allocated dst cap_spec **
           pure (SZ.v cap == reveal cap_spec)
  ensures cipher_suite_list_exactly src cap_spec suites **
          cipher_suite_list_exactly dst cap_spec suites
{
  unfold (cipher_suite_list_exactly src cap_spec (Ghost.reveal suites));
  unfold (cipher_suite_list_allocated dst cap_spec);
  with src_items. assert (V.pts_to src.items src_items);
  with src_len. assert (Box.pts_to src.len src_len);
  with dst_items. assert (V.pts_to dst.items dst_items);
  with dst_len. assert (Box.pts_to dst.len dst_len);
  let src_len_runtime = !src.len;
  assert (pure (src_len_runtime == src_len));
  V.to_array_pts_to src.items;
  V.to_array_pts_to dst.items;
  Arr.memcpy cap (V.vec_to_array src.items) (V.vec_to_array dst.items);
  V.to_vec_pts_to src.items;
  V.to_vec_pts_to dst.items;
  dst.len := src_len_runtime;
  assert (V.pts_to dst.items src_items);
  fold (cipher_suite_list_exactly src cap_spec (Ghost.reveal suites));
  fold (cipher_suite_list_exactly dst cap_spec (Ghost.reveal suites))
}

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
{
  unfold (signature_scheme_list_exactly src cap_spec (Ghost.reveal schemes));
  unfold (signature_scheme_list_allocated dst cap_spec);
  with src_items. assert (V.pts_to src.items src_items);
  with src_len. assert (Box.pts_to src.len src_len);
  with dst_items. assert (V.pts_to dst.items dst_items);
  with dst_len. assert (Box.pts_to dst.len dst_len);
  let src_len_runtime = !src.len;
  assert (pure (src_len_runtime == src_len));
  V.to_array_pts_to src.items;
  V.to_array_pts_to dst.items;
  Arr.memcpy cap (V.vec_to_array src.items) (V.vec_to_array dst.items);
  V.to_vec_pts_to src.items;
  V.to_vec_pts_to dst.items;
  dst.len := src_len_runtime;
  assert (V.pts_to dst.items src_items);
  fold (signature_scheme_list_exactly src cap_spec (Ghost.reveal schemes));
  fold (signature_scheme_list_exactly dst cap_spec (Ghost.reveal schemes))
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
  let cap = max_hostname_len_sz;
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
  let dst_cap = max_public_key_len_sz;
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
  let dst_cap = max_certificate_verify_input_len_sz;
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
  let src_cap = IM.max_certificate_chain_bytes_sz;
  let dst_cap = max_handshake_flight_len_sz;
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
