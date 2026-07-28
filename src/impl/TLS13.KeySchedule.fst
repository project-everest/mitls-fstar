module TLS13.KeySchedule

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module Crypto = TLS13.Crypto
module K = TLS13.Keys
module Seq = FStar.Seq
module SC = TLS13.Impl.Serializer.Common
module SZ = FStar.SizeT
module U8 = FStar.UInt8

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
noextract
let label_traffic_update_seq : B.bytes = K.label_traffic_update

inline_for_extraction
fn write_label_derived (lbl: array U8.t)
  requires pts_to lbl (Seq.create 7 0uy)
  ensures pts_to lbl label_derived_seq
{
  lbl.(0sz) <- 0x64uy;
  lbl.(1sz) <- 0x65uy;
  lbl.(2sz) <- 0x72uy;
  lbl.(3sz) <- 0x69uy;
  lbl.(4sz) <- 0x76uy;
  lbl.(5sz) <- 0x65uy;
  lbl.(6sz) <- 0x64uy;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_derived_seq);
  assert (pure (s == label_derived_seq));
}

inline_for_extraction
fn write_label_c_hs_traffic (lbl: array U8.t)
  requires pts_to lbl (Seq.create 12 0uy)
  ensures pts_to lbl label_c_hs_traffic_seq
{
  lbl.(0sz) <- 0x63uy;
  lbl.(1sz) <- 0x20uy;
  lbl.(2sz) <- 0x68uy;
  lbl.(3sz) <- 0x73uy;
  lbl.(4sz) <- 0x20uy;
  lbl.(5sz) <- 0x74uy;
  lbl.(6sz) <- 0x72uy;
  lbl.(7sz) <- 0x61uy;
  lbl.(8sz) <- 0x66uy;
  lbl.(9sz) <- 0x66uy;
  lbl.(10sz) <- 0x69uy;
  lbl.(11sz) <- 0x63uy;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_c_hs_traffic_seq);
  assert (pure (s == label_c_hs_traffic_seq));
}

inline_for_extraction
fn write_label_s_hs_traffic (lbl: array U8.t)
  requires pts_to lbl (Seq.create 12 0uy)
  ensures pts_to lbl label_s_hs_traffic_seq
{
  lbl.(0sz) <- 0x73uy;
  lbl.(1sz) <- 0x20uy;
  lbl.(2sz) <- 0x68uy;
  lbl.(3sz) <- 0x73uy;
  lbl.(4sz) <- 0x20uy;
  lbl.(5sz) <- 0x74uy;
  lbl.(6sz) <- 0x72uy;
  lbl.(7sz) <- 0x61uy;
  lbl.(8sz) <- 0x66uy;
  lbl.(9sz) <- 0x66uy;
  lbl.(10sz) <- 0x69uy;
  lbl.(11sz) <- 0x63uy;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_s_hs_traffic_seq);
  assert (pure (s == label_s_hs_traffic_seq));
}

inline_for_extraction
fn write_label_c_ap_traffic (lbl: array U8.t)
  requires pts_to lbl (Seq.create 12 0uy)
  ensures pts_to lbl label_c_ap_traffic_seq
{
  lbl.(0sz) <- 0x63uy;
  lbl.(1sz) <- 0x20uy;
  lbl.(2sz) <- 0x61uy;
  lbl.(3sz) <- 0x70uy;
  lbl.(4sz) <- 0x20uy;
  lbl.(5sz) <- 0x74uy;
  lbl.(6sz) <- 0x72uy;
  lbl.(7sz) <- 0x61uy;
  lbl.(8sz) <- 0x66uy;
  lbl.(9sz) <- 0x66uy;
  lbl.(10sz) <- 0x69uy;
  lbl.(11sz) <- 0x63uy;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_c_ap_traffic_seq);
  assert (pure (s == label_c_ap_traffic_seq));
}

inline_for_extraction
fn write_label_s_ap_traffic (lbl: array U8.t)
  requires pts_to lbl (Seq.create 12 0uy)
  ensures pts_to lbl label_s_ap_traffic_seq
{
  lbl.(0sz) <- 0x73uy;
  lbl.(1sz) <- 0x20uy;
  lbl.(2sz) <- 0x61uy;
  lbl.(3sz) <- 0x70uy;
  lbl.(4sz) <- 0x20uy;
  lbl.(5sz) <- 0x74uy;
  lbl.(6sz) <- 0x72uy;
  lbl.(7sz) <- 0x61uy;
  lbl.(8sz) <- 0x66uy;
  lbl.(9sz) <- 0x66uy;
  lbl.(10sz) <- 0x69uy;
  lbl.(11sz) <- 0x63uy;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_s_ap_traffic_seq);
  assert (pure (s == label_s_ap_traffic_seq));
}

inline_for_extraction
fn write_label_finished (lbl: array U8.t)
  requires pts_to lbl (Seq.create 8 0uy)
  ensures pts_to lbl label_finished_seq
{
  lbl.(0sz) <- 0x66uy;
  lbl.(1sz) <- 0x69uy;
  lbl.(2sz) <- 0x6euy;
  lbl.(3sz) <- 0x69uy;
  lbl.(4sz) <- 0x73uy;
  lbl.(5sz) <- 0x68uy;
  lbl.(6sz) <- 0x65uy;
  lbl.(7sz) <- 0x64uy;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_finished_seq);
  assert (pure (s == label_finished_seq));
}

inline_for_extraction
fn write_label_key (lbl: array U8.t)
  requires pts_to lbl (Seq.create 3 0uy)
  ensures pts_to lbl label_key_seq
{
  lbl.(0sz) <- 0x6buy;
  lbl.(1sz) <- 0x65uy;
  lbl.(2sz) <- 0x79uy;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_key_seq);
  assert (pure (s == label_key_seq));
}

inline_for_extraction
fn write_label_iv (lbl: array U8.t)
  requires pts_to lbl (Seq.create 2 0uy)
  ensures pts_to lbl label_iv_seq
{
  lbl.(0sz) <- 0x69uy;
  lbl.(1sz) <- 0x76uy;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_iv_seq);
  assert (pure (s == label_iv_seq));
}

inline_for_extraction
fn write_label_traffic_update (lbl: array U8.t)
  requires pts_to lbl (Seq.create 11 0uy)
  ensures pts_to lbl label_traffic_update_seq
{
  lbl.(0sz) <- 0x74uy;
  lbl.(1sz) <- 0x72uy;
  lbl.(2sz) <- 0x61uy;
  lbl.(3sz) <- 0x66uy;
  lbl.(4sz) <- 0x66uy;
  lbl.(5sz) <- 0x69uy;
  lbl.(6sz) <- 0x63uy;
  lbl.(7sz) <- 0x20uy;
  lbl.(8sz) <- 0x75uy;
  lbl.(9sz) <- 0x70uy;
  lbl.(10sz) <- 0x64uy;
  with s. assert (pts_to lbl s);
  assert_norm (s == label_traffic_update_seq);
  assert (pure (s == label_traffic_update_seq));
}

inline_for_extraction
fn write_hkdf_info_byte
  (info: array U8.t)
  (idx: SZ.t{SZ.v idx < length info})
  (value: U8.t)
  requires pts_to info 'bytes
  ensures pts_to info (C.update_byte 'bytes (SZ.v idx) value)
{
  pts_to_len info;
  info.(idx) <- value;
}

inline_for_extraction
fn copy_hkdf_info_bytes
  (src: array U8.t)
  (src_len: SZ.t)
  (info: array U8.t)
  (info_offset: SZ.t)
  requires pts_to src 'src_bytes **
           pts_to info 'info_bytes **
           pure (B.length 'src_bytes == SZ.v src_len /\
                 B.length 'info_bytes == 520 /\
                 SZ.v info_offset + SZ.v src_len <= 520)
  ensures pts_to src 'src_bytes **
          pts_to info
            (C.copy_bytes_into 'info_bytes (SZ.v info_offset) 'src_bytes)
{
  SC.copy_array_slice_to_array
    src src_len 0sz src_len info 520sz info_offset;
  with copied. assert (pts_to info copied);
  assert_norm (copied ==
    C.copy_bytes_into 'info_bytes (SZ.v info_offset) 'src_bytes);
  rewrite (pts_to info copied) as
    (pts_to info
      (C.copy_bytes_into 'info_bytes (SZ.v info_offset) 'src_bytes));
}

inline_for_extraction
fn hkdf_expand_label
  (secret: array U8.t)
  (lbl: array U8.t)
  (label_len: SZ.t)
  (context: array U8.t)
  (context_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to secret 'secret_bytes **
           pts_to lbl 'label_bytes **
           pts_to context 'context_bytes **
           pts_to out 'old **
           pure (B.length 'secret_bytes == 32 /\
                 B.length 'label_bytes == SZ.v label_len /\
                 B.length 'context_bytes == SZ.v context_len /\
                 B.length 'old == SZ.v out_len /\
                 SZ.v label_len <= 249 /\
                 SZ.v context_len <= 255 /\
                 SZ.v out_len <= 8160)
  ensures pts_to secret 'secret_bytes **
          pts_to lbl 'label_bytes **
          pts_to context 'context_bytes **
          pts_to out (C.hkdf_expand_label
                        'secret_bytes
                        'label_bytes
                        'context_bytes
                        (SZ.v out_len))
{
  let mut info = [| 0uy; 520sz |];

  let out_hi = SC.u8_of_sizet (SZ.div out_len 256sz);
  let out_lo = SC.u8_of_sizet out_len;
  let full_label_len = SZ.add 6sz label_len;
  let full_label_len_byte = SC.u8_of_sizet full_label_len;
  let context_len_byte = SC.u8_of_sizet context_len;

  write_hkdf_info_byte info 0sz out_hi;
  write_hkdf_info_byte info 1sz out_lo;
  write_hkdf_info_byte info 2sz full_label_len_byte;
  write_hkdf_info_byte info 3sz 0x74uy;
  write_hkdf_info_byte info 4sz 0x6cuy;
  write_hkdf_info_byte info 5sz 0x73uy;
  write_hkdf_info_byte info 6sz 0x31uy;
  write_hkdf_info_byte info 7sz 0x33uy;
  write_hkdf_info_byte info 8sz 0x20uy;
  copy_hkdf_info_bytes lbl label_len info 9sz;

  let context_len_offset = SZ.add 9sz label_len;
  write_hkdf_info_byte info context_len_offset context_len_byte;
  let context_offset = SZ.add 10sz label_len;
  copy_hkdf_info_bytes context context_len info context_offset;

  with info_bytes. assert (pts_to info info_bytes);
  SC.u8_of_sizet_v_byte out_len;
  SC.u8_of_sizet_v_byte (SZ.div out_len 256sz);
  SC.u8_of_sizet_v_byte full_label_len;
  SC.u8_of_sizet_v_byte context_len;
  reveal_opaque (`%C.hkdf_label_info_buffer)
    (C.hkdf_label_info_buffer 'label_bytes 'context_bytes (SZ.v out_len));
  assert_norm (info_bytes ==
    C.hkdf_label_info_buffer 'label_bytes 'context_bytes (SZ.v out_len));
  rewrite (pts_to info info_bytes) as
    (pts_to info
      (C.hkdf_label_info_buffer 'label_bytes 'context_bytes (SZ.v out_len)));

  let info_len = SZ.add 10sz (SZ.add label_len context_len);
  Crypto.hkdf_expand
    secret info info_len out out_len
    #'label_bytes #'context_bytes;
}

inline_for_extraction
fn derived_secret
  (secret: array U8.t)
  (out: array U8.t)
  requires pts_to secret 'secret_bytes **
           pts_to out 'old **
           pure (B.length 'secret_bytes == 32 /\ B.length 'old == 32)
  ensures pts_to secret 'secret_bytes **
          pts_to out (K.derived_secret (Ghost.reveal 'secret_bytes))
{
  let mut empty_hash = [| 0uy; 32sz |];
  Crypto.sha256_empty empty_hash;

  let mut lbl = [| 0uy; 7sz |];
  write_label_derived lbl;
  hkdf_expand_label secret lbl 7sz empty_hash 32sz out 32sz;
}

fn early_secret_empty
  (out: array U8.t)
  requires pts_to out 'old **
           pure (B.length 'old == 32)
  ensures pts_to out (K.early_secret B.empty)
{
  let mut empty_salt = [| 0uy; 0sz |];
  let mut zero_psk = [| 0uy; 32sz |];
  Crypto.hkdf_extract empty_salt 0sz zero_psk 32sz out;
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
  let mut derived = [| 0uy; 32sz |];
  derived_secret early derived;
  Crypto.hkdf_extract derived 32sz shared shared_len out;
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
  let mut derived = [| 0uy; 32sz |];
  derived_secret handshake derived;
  let mut zero = [| 0uy; 32sz |];
  Crypto.hkdf_extract derived 32sz zero 32sz out;
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
  let mut lbl = [| 0uy; 12sz |];
  write_label_c_hs_traffic lbl;
  hkdf_expand_label handshake lbl 12sz transcript_hash 32sz out 32sz;
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
  let mut lbl = [| 0uy; 12sz |];
  write_label_s_hs_traffic lbl;
  hkdf_expand_label handshake lbl 12sz transcript_hash 32sz out 32sz;
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
  let mut lbl = [| 0uy; 12sz |];
  write_label_c_ap_traffic lbl;
  hkdf_expand_label master lbl 12sz transcript_hash 32sz out 32sz;
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
  let mut lbl = [| 0uy; 12sz |];
  write_label_s_ap_traffic lbl;
  hkdf_expand_label master lbl 12sz transcript_hash 32sz out 32sz;
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
  let mut lbl = [| 0uy; 8sz |];
  write_label_finished lbl;
  let mut finished_key = [| 0uy; 32sz |];
  let mut empty_context = [| 0uy; 0sz |];
  hkdf_expand_label base_key lbl 8sz empty_context 0sz finished_key 32sz;
  Crypto.hmac_sha256 finished_key 32sz transcript_hash 32sz out;
}

fn application_traffic_secret_update
  (old_secret: array U8.t)
  (out: array U8.t)
  requires pts_to old_secret 'old_secret_bytes **
           pts_to out 'old **
           pure (B.length 'old_secret_bytes == 32 /\
                 B.length 'old == 32)
  ensures pts_to old_secret 'old_secret_bytes **
          pts_to out (K.application_traffic_secret_update
                        (Ghost.reveal 'old_secret_bytes))
{
  let mut lbl = [| 0uy; 11sz |];
  write_label_traffic_update lbl;
  let mut empty_context = [| 0uy; 0sz |];
  hkdf_expand_label old_secret lbl 11sz empty_context 0sz out 32sz;
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
  let mut lbl = [| 0uy; 3sz |];
  write_label_key lbl;
  let mut empty_context = [| 0uy; 0sz |];
  hkdf_expand_label traffic_secret lbl 3sz empty_context 0sz out 32sz;
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
  let mut lbl = [| 0uy; 2sz |];
  write_label_iv lbl;
  let mut empty_context = [| 0uy; 0sz |];
  hkdf_expand_label traffic_secret lbl 2sz empty_context 0sz out 12sz;
}
