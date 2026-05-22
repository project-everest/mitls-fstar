module TLS13.KeySchedule

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module A = Pulse.Lib.Array.PtsTo
module B = TLS13.Bytes
module Crypto = TLS13.Crypto
module K = TLS13.Keys
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

inline_for_extraction
let zero_u8 : U8.t = U8.uint_to_t 0

noextract
let label_derived_seq : B.bytes = K.label_derived
noextract
let label_c_hs_traffic_seq : B.bytes = K.label_c_hs_traffic
noextract
let label_s_hs_traffic_seq : B.bytes = K.label_s_hs_traffic
noextract
let label_c_ap_traffic_seq : B.bytes = K.label_c_ap_traffic
noextract
let label_s_ap_traffic_seq : B.bytes = K.label_s_ap_traffic
noextract
let label_finished_seq : B.bytes = K.label_finished
noextract
let label_key_seq : B.bytes = K.label_key
noextract
let label_iv_seq : B.bytes = K.label_iv

inline_for_extraction
fn write_label_derived (lbl: array U8.t)
  requires pts_to lbl (Seq.create 7 zero_u8)
  ensures pts_to lbl label_derived_seq
{
  lbl.(0sz) <- U8.uint_to_t 0x64;
  lbl.(1sz) <- U8.uint_to_t 0x65;
  lbl.(2sz) <- U8.uint_to_t 0x72;
  lbl.(3sz) <- U8.uint_to_t 0x69;
  lbl.(4sz) <- U8.uint_to_t 0x76;
  lbl.(5sz) <- U8.uint_to_t 0x65;
  lbl.(6sz) <- U8.uint_to_t 0x64;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_derived_seq);
  assert (pure (s == label_derived_seq));
}

inline_for_extraction
fn write_label_c_hs_traffic (lbl: array U8.t)
  requires pts_to lbl (Seq.create 12 zero_u8)
  ensures pts_to lbl label_c_hs_traffic_seq
{
  lbl.(0sz) <- U8.uint_to_t 0x63;
  lbl.(1sz) <- U8.uint_to_t 0x20;
  lbl.(2sz) <- U8.uint_to_t 0x68;
  lbl.(3sz) <- U8.uint_to_t 0x73;
  lbl.(4sz) <- U8.uint_to_t 0x20;
  lbl.(5sz) <- U8.uint_to_t 0x74;
  lbl.(6sz) <- U8.uint_to_t 0x72;
  lbl.(7sz) <- U8.uint_to_t 0x61;
  lbl.(8sz) <- U8.uint_to_t 0x66;
  lbl.(9sz) <- U8.uint_to_t 0x66;
  lbl.(10sz) <- U8.uint_to_t 0x69;
  lbl.(11sz) <- U8.uint_to_t 0x63;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_c_hs_traffic_seq);
  assert (pure (s == label_c_hs_traffic_seq));
}

inline_for_extraction
fn write_label_s_hs_traffic (lbl: array U8.t)
  requires pts_to lbl (Seq.create 12 zero_u8)
  ensures pts_to lbl label_s_hs_traffic_seq
{
  lbl.(0sz) <- U8.uint_to_t 0x73;
  lbl.(1sz) <- U8.uint_to_t 0x20;
  lbl.(2sz) <- U8.uint_to_t 0x68;
  lbl.(3sz) <- U8.uint_to_t 0x73;
  lbl.(4sz) <- U8.uint_to_t 0x20;
  lbl.(5sz) <- U8.uint_to_t 0x74;
  lbl.(6sz) <- U8.uint_to_t 0x72;
  lbl.(7sz) <- U8.uint_to_t 0x61;
  lbl.(8sz) <- U8.uint_to_t 0x66;
  lbl.(9sz) <- U8.uint_to_t 0x66;
  lbl.(10sz) <- U8.uint_to_t 0x69;
  lbl.(11sz) <- U8.uint_to_t 0x63;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_s_hs_traffic_seq);
  assert (pure (s == label_s_hs_traffic_seq));
}

inline_for_extraction
fn write_label_c_ap_traffic (lbl: array U8.t)
  requires pts_to lbl (Seq.create 12 zero_u8)
  ensures pts_to lbl label_c_ap_traffic_seq
{
  lbl.(0sz) <- U8.uint_to_t 0x63;
  lbl.(1sz) <- U8.uint_to_t 0x20;
  lbl.(2sz) <- U8.uint_to_t 0x61;
  lbl.(3sz) <- U8.uint_to_t 0x70;
  lbl.(4sz) <- U8.uint_to_t 0x20;
  lbl.(5sz) <- U8.uint_to_t 0x74;
  lbl.(6sz) <- U8.uint_to_t 0x72;
  lbl.(7sz) <- U8.uint_to_t 0x61;
  lbl.(8sz) <- U8.uint_to_t 0x66;
  lbl.(9sz) <- U8.uint_to_t 0x66;
  lbl.(10sz) <- U8.uint_to_t 0x69;
  lbl.(11sz) <- U8.uint_to_t 0x63;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_c_ap_traffic_seq);
  assert (pure (s == label_c_ap_traffic_seq));
}

inline_for_extraction
fn write_label_s_ap_traffic (lbl: array U8.t)
  requires pts_to lbl (Seq.create 12 zero_u8)
  ensures pts_to lbl label_s_ap_traffic_seq
{
  lbl.(0sz) <- U8.uint_to_t 0x73;
  lbl.(1sz) <- U8.uint_to_t 0x20;
  lbl.(2sz) <- U8.uint_to_t 0x61;
  lbl.(3sz) <- U8.uint_to_t 0x70;
  lbl.(4sz) <- U8.uint_to_t 0x20;
  lbl.(5sz) <- U8.uint_to_t 0x74;
  lbl.(6sz) <- U8.uint_to_t 0x72;
  lbl.(7sz) <- U8.uint_to_t 0x61;
  lbl.(8sz) <- U8.uint_to_t 0x66;
  lbl.(9sz) <- U8.uint_to_t 0x66;
  lbl.(10sz) <- U8.uint_to_t 0x69;
  lbl.(11sz) <- U8.uint_to_t 0x63;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_s_ap_traffic_seq);
  assert (pure (s == label_s_ap_traffic_seq));
}

inline_for_extraction
fn write_label_finished (lbl: array U8.t)
  requires pts_to lbl (Seq.create 8 zero_u8)
  ensures pts_to lbl label_finished_seq
{
  lbl.(0sz) <- U8.uint_to_t 0x66;
  lbl.(1sz) <- U8.uint_to_t 0x69;
  lbl.(2sz) <- U8.uint_to_t 0x6e;
  lbl.(3sz) <- U8.uint_to_t 0x69;
  lbl.(4sz) <- U8.uint_to_t 0x73;
  lbl.(5sz) <- U8.uint_to_t 0x68;
  lbl.(6sz) <- U8.uint_to_t 0x65;
  lbl.(7sz) <- U8.uint_to_t 0x64;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_finished_seq);
  assert (pure (s == label_finished_seq));
}

inline_for_extraction
fn write_label_key (lbl: array U8.t)
  requires pts_to lbl (Seq.create 3 zero_u8)
  ensures pts_to lbl label_key_seq
{
  lbl.(0sz) <- U8.uint_to_t 0x6b;
  lbl.(1sz) <- U8.uint_to_t 0x65;
  lbl.(2sz) <- U8.uint_to_t 0x79;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_key_seq);
  assert (pure (s == label_key_seq));
}

inline_for_extraction
fn write_label_iv (lbl: array U8.t)
  requires pts_to lbl (Seq.create 2 zero_u8)
  ensures pts_to lbl label_iv_seq
{
  lbl.(0sz) <- U8.uint_to_t 0x69;
  lbl.(1sz) <- U8.uint_to_t 0x76;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_iv_seq);
  assert (pure (s == label_iv_seq));
}

fn derived_secret
  (secret: array U8.t)
  (out: array U8.t)
  requires pts_to secret 'secret_bytes **
           pts_to out 'old **
           pure (B.length 'secret_bytes == 32 /\ B.length 'old == 32)
  ensures pts_to secret 'secret_bytes **
          pts_to out (K.derived_secret (Ghost.reveal 'secret_bytes))
{
  let empty_hash = A.alloc zero_u8 32sz;
  Crypto.sha256_empty empty_hash;

  let lbl = A.alloc zero_u8 7sz;
  write_label_derived lbl;
  Crypto.hkdf_expand_label secret lbl 7sz empty_hash 32sz out 32sz;

  A.free lbl;
  A.free empty_hash;
}

fn handshake_secret
  (early: array U8.t)
  (shared: array U8.t)
  (shared_len: SZ.t)
  (out: array U8.t)
  requires pts_to early 'early_bytes **
           pts_to shared 'shared_bytes **
           pts_to out 'old **
           pure (B.length 'early_bytes == 32 /\
                 B.length 'shared_bytes == SZ.v shared_len /\
                 B.length 'old == 32)
  ensures pts_to early 'early_bytes **
          pts_to shared 'shared_bytes **
          pts_to out (K.handshake_secret (Ghost.reveal 'early_bytes) (Ghost.reveal 'shared_bytes))
{
  let derived = A.alloc zero_u8 32sz;
  derived_secret early derived;
  Crypto.hkdf_extract derived 32sz shared shared_len out;
  A.free derived;
}

fn master_secret
  (handshake: array U8.t)
  (out: array U8.t)
  requires pts_to handshake 'handshake_bytes **
           pts_to out 'old **
           pure (B.length 'handshake_bytes == 32 /\ B.length 'old == 32)
  ensures pts_to handshake 'handshake_bytes **
          pts_to out (K.master_secret (Ghost.reveal 'handshake_bytes))
{
  let derived = A.alloc zero_u8 32sz;
  derived_secret handshake derived;
  let zero = A.alloc zero_u8 32sz;
  Crypto.hkdf_extract derived 32sz zero 32sz out;
  A.free zero;
  A.free derived;
}

fn client_handshake_traffic_secret
  (handshake: array U8.t)
  (transcript_hash: array U8.t)
  (out: array U8.t)
  requires pts_to handshake 'handshake_bytes **
           pts_to transcript_hash 'hash_bytes **
           pts_to out 'old **
           pure (B.length 'handshake_bytes == 32 /\
                 B.length 'hash_bytes == 32 /\
                 B.length 'old == 32)
  ensures pts_to handshake 'handshake_bytes **
          pts_to transcript_hash 'hash_bytes **
          pts_to out (K.client_handshake_traffic_secret
                        (Ghost.reveal 'handshake_bytes)
                        (Ghost.reveal 'hash_bytes))
{
  let lbl = A.alloc zero_u8 12sz;
  write_label_c_hs_traffic lbl;
  Crypto.hkdf_expand_label handshake lbl 12sz transcript_hash 32sz out 32sz;
  A.free lbl;
}

fn server_handshake_traffic_secret
  (handshake: array U8.t)
  (transcript_hash: array U8.t)
  (out: array U8.t)
  requires pts_to handshake 'handshake_bytes **
           pts_to transcript_hash 'hash_bytes **
           pts_to out 'old **
           pure (B.length 'handshake_bytes == 32 /\
                 B.length 'hash_bytes == 32 /\
                 B.length 'old == 32)
  ensures pts_to handshake 'handshake_bytes **
          pts_to transcript_hash 'hash_bytes **
          pts_to out (K.server_handshake_traffic_secret
                        (Ghost.reveal 'handshake_bytes)
                        (Ghost.reveal 'hash_bytes))
{
  let lbl = A.alloc zero_u8 12sz;
  write_label_s_hs_traffic lbl;
  Crypto.hkdf_expand_label handshake lbl 12sz transcript_hash 32sz out 32sz;
  A.free lbl;
}

fn client_application_traffic_secret
  (master: array U8.t)
  (transcript_hash: array U8.t)
  (out: array U8.t)
  requires pts_to master 'master_bytes **
           pts_to transcript_hash 'hash_bytes **
           pts_to out 'old **
           pure (B.length 'master_bytes == 32 /\
                 B.length 'hash_bytes == 32 /\
                 B.length 'old == 32)
  ensures pts_to master 'master_bytes **
          pts_to transcript_hash 'hash_bytes **
          pts_to out (K.client_application_traffic_secret
                        (Ghost.reveal 'master_bytes)
                        (Ghost.reveal 'hash_bytes))
{
  let lbl = A.alloc zero_u8 12sz;
  write_label_c_ap_traffic lbl;
  Crypto.hkdf_expand_label master lbl 12sz transcript_hash 32sz out 32sz;
  A.free lbl;
}

fn server_application_traffic_secret
  (master: array U8.t)
  (transcript_hash: array U8.t)
  (out: array U8.t)
  requires pts_to master 'master_bytes **
           pts_to transcript_hash 'hash_bytes **
           pts_to out 'old **
           pure (B.length 'master_bytes == 32 /\
                 B.length 'hash_bytes == 32 /\
                 B.length 'old == 32)
  ensures pts_to master 'master_bytes **
          pts_to transcript_hash 'hash_bytes **
          pts_to out (K.server_application_traffic_secret
                        (Ghost.reveal 'master_bytes)
                        (Ghost.reveal 'hash_bytes))
{
  let lbl = A.alloc zero_u8 12sz;
  write_label_s_ap_traffic lbl;
  Crypto.hkdf_expand_label master lbl 12sz transcript_hash 32sz out 32sz;
  A.free lbl;
}

fn finished_verify_data
  (base_key: array U8.t)
  (transcript_hash: array U8.t)
  (out: array U8.t)
  requires pts_to base_key 'base_key_bytes **
          pts_to transcript_hash 'hash_bytes **
          pts_to out 'old **
          pure (B.length 'base_key_bytes == 32 /\
                B.length 'hash_bytes == 32 /\
                B.length 'old == 32)
  ensures pts_to base_key 'base_key_bytes **
          pts_to transcript_hash 'hash_bytes **
          pts_to out (K.finished_verify_data
                       (Ghost.reveal 'base_key_bytes)
                       (Ghost.reveal 'hash_bytes))
{
  let lbl = A.alloc zero_u8 8sz;
  write_label_finished lbl;
  let finished_key = A.alloc zero_u8 32sz;
  Crypto.hkdf_expand_label_empty_context base_key lbl 8sz finished_key 32sz;
  Crypto.hmac_sha256 finished_key 32sz transcript_hash 32sz out;
  A.free finished_key;
  A.free lbl;
}

fn derive_traffic_key
  (traffic_secret: array U8.t)
  (out: array U8.t)
  requires pts_to traffic_secret 'secret_bytes **
          pts_to out 'old **
           pure (B.length 'secret_bytes == 32 /\ B.length 'old == 32)
  ensures pts_to traffic_secret 'secret_bytes **
          pts_to out (K.derive_aead_key (Ghost.reveal 'secret_bytes))
{
  let lbl = A.alloc zero_u8 3sz;
  write_label_key lbl;
  Crypto.hkdf_expand_label_empty_context traffic_secret lbl 3sz out 32sz;
  A.free lbl;
}

fn derive_traffic_iv
  (traffic_secret: array U8.t)
  (out: array U8.t)
  requires pts_to traffic_secret 'secret_bytes **
           pts_to out 'old **
           pure (B.length 'secret_bytes == 32 /\ B.length 'old == 12)
  ensures pts_to traffic_secret 'secret_bytes **
          pts_to out (K.derive_aead_iv (Ghost.reveal 'secret_bytes))
{
  let lbl = A.alloc zero_u8 2sz;
  write_label_iv lbl;
  Crypto.hkdf_expand_label_empty_context traffic_secret lbl 2sz out 12sz;
  A.free lbl;
}
