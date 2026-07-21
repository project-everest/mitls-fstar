module TLS13.Crypto

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64

fn random_bytes (out: array U8.t) (out_len: SZ.t)
  requires pts_to out 'old ** pure (B.length 'old == SZ.v out_len)
  returns ok: bool
  ensures exists* bytes. pts_to out bytes ** pure (B.length bytes == SZ.v out_len)

fn sha256 (input: array U8.t) (input_len: SZ.t) (out: array U8.t)
  requires pts_to input 'msg **
           pts_to out 'old **
           pure (B.length 'msg == SZ.v input_len /\ B.length 'old == 32)
  ensures pts_to input 'msg ** pts_to out (C.sha256 'msg)

fn sha256_prefix (input: array U8.t) (input_len: SZ.t) (out: array U8.t)
  requires pts_to input 'msg **
           pts_to out 'old **
           pure (SZ.v input_len <= B.length 'msg /\
                 B.length 'old == 32)
  ensures pts_to input 'msg **
          pts_to out (C.sha256 (CL.raw_slice 'msg 0 (SZ.v input_len)))

fn sha256_empty (out: array U8.t)
  requires pts_to out 'old **
           pure (B.length 'old == 32)
  ensures pts_to out (C.sha256 B.empty)

fn hmac_sha256 (key: array U8.t) (key_len: SZ.t) (msg: array U8.t) (msg_len: SZ.t) (out: array U8.t)
  requires pts_to key 'key_bytes **
           pts_to msg 'msg_bytes **
           pts_to out 'old **
           pure (B.length 'key_bytes == SZ.v key_len /\
                 B.length 'msg_bytes == SZ.v msg_len /\
                 B.length 'old == 32)
  ensures pts_to key 'key_bytes **
          pts_to msg 'msg_bytes **
          pts_to out (C.hmac_sha256 'key_bytes 'msg_bytes)

fn equal32 (a: array U8.t) (b: array U8.t)
  requires pts_to a 'a_bytes **
           pts_to b 'b_bytes **
           pure (B.length 'a_bytes == 32 /\ B.length 'b_bytes == 32)
  returns ok: bool
  ensures pts_to a 'a_bytes **
          pts_to b 'b_bytes **
          pure (ok <==> Seq.equal 'a_bytes 'b_bytes)

fn equal12 (a: array U8.t) (b: array U8.t)
  requires pts_to a 'a_bytes **
           pts_to b 'b_bytes **
           pure (B.length 'a_bytes == 12 /\ B.length 'b_bytes == 12)
  returns ok: bool
  ensures pts_to a 'a_bytes **
          pts_to b 'b_bytes **
          pure (ok <==> Seq.equal 'a_bytes 'b_bytes)

fn hkdf_extract (salt: array U8.t) (salt_len: SZ.t) (ikm: array U8.t) (ikm_len: SZ.t) (out: array U8.t)
  requires pts_to salt 'salt_bytes **
           pts_to ikm 'ikm_bytes **
           pts_to out 'old **
           pure (B.length 'salt_bytes == SZ.v salt_len /\
                 B.length 'ikm_bytes == SZ.v ikm_len /\
                 B.length 'old == 32)
  ensures pts_to salt 'salt_bytes **
          pts_to ikm 'ikm_bytes **
          pts_to out (C.hkdf_extract 'salt_bytes 'ikm_bytes)

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
                 B.length 'old == SZ.v out_len)
  ensures pts_to secret 'secret_bytes **
          pts_to lbl 'label_bytes **
          pts_to context 'context_bytes **
          pure (B.length (C.hkdf_expand_label 'secret_bytes 'label_bytes 'context_bytes (SZ.v out_len)) == SZ.v out_len) **
          pts_to out (C.hkdf_expand_label 'secret_bytes 'label_bytes 'context_bytes (SZ.v out_len))

fn hkdf_expand_label_empty_context
  (secret: array U8.t)
  (lbl: array U8.t)
  (label_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to secret 'secret_bytes **
          pts_to lbl 'label_bytes **
          pts_to out 'old **
          pure (B.length 'secret_bytes == 32 /\
                B.length 'label_bytes == SZ.v label_len /\
                B.length 'old == SZ.v out_len)
  ensures pts_to secret 'secret_bytes **
          pts_to lbl 'label_bytes **
          pure (B.length (C.hkdf_expand_label 'secret_bytes 'label_bytes B.empty (SZ.v out_len)) == SZ.v out_len) **
          pts_to out (C.hkdf_expand_label 'secret_bytes 'label_bytes B.empty (SZ.v out_len))

fn x25519_public_from_private (sk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'old == 32)
  ensures pts_to sk 'sk_bytes ** pts_to out (C.x25519_public_from_private 'sk_bytes)

fn x25519_shared (sk: array U8.t) (pk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk 'pk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'pk_bytes == 32 /\ B.length 'old == 32)
  returns ok: bool
  ensures pts_to sk 'sk_bytes **
          pts_to pk 'pk_bytes **
          (exists* shared.
            pts_to out shared **
            pure (B.length shared == 32 /\
                  (ok ==>
                   Some? (C.x25519_shared 'sk_bytes 'pk_bytes) /\
                   Some?.v (C.x25519_shared 'sk_bytes 'pk_bytes) == shared) /\
                  (not ok ==> C.x25519_shared 'sk_bytes 'pk_bytes == None)))

noextract
val x25519_shared_call:
  sk:B.bytes ->
  pk:B.bytes ->
  shared:B.bytes ->
  ok:bool ->
  GTot prop

noextract
val lemma_x25519_shared_call_success:
  sk:B.bytes ->
  pk:B.bytes ->
  shared:B.bytes ->
  ok:bool ->
  Lemma
    (requires x25519_shared_call sk pk shared ok /\
              ok /\
              B.length shared == 32)
    (ensures Some? (C.x25519_shared sk pk) /\
             C.x25519_shared sk pk == Some (Some?.v (C.x25519_shared sk pk)) /\
             Some?.v (C.x25519_shared sk pk) == shared)

fn x25519_shared_runtime (sk: array U8.t) (pk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk 'pk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'pk_bytes == 32 /\ B.length 'old == 32)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to sk 'sk_bytes **
          pts_to pk 'pk_bytes **
          pts_to out out_bytes **
          pure (x25519_shared_call 'sk_bytes 'pk_bytes out_bytes ok)

fn tls13_record_nonce (static_iv: array U8.t) (sequence_number: U64.t) (out: array U8.t)
  requires pts_to static_iv 'iv_bytes **
           pts_to out 'old **
           pure (B.length 'iv_bytes == 12 /\ B.length 'old == 12)
  returns ok: bool
  ensures pts_to static_iv 'iv_bytes **
          pts_to out (C.tls13_record_nonce 'iv_bytes (U64.v sequence_number)) **
          pure ok

fn chacha20_poly1305_seal
  (key: array U8.t)
  (nonce: array U8.t)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (plain: array U8.t)
  (plain_len: SZ.t)
  (out: array U8.t)
  requires pts_to key 'key_bytes **
           pts_to nonce 'nonce_bytes **
           pts_to aad 'aad_bytes **
           pts_to plain 'plain_bytes **
           pts_to out 'old **
           pure (B.length 'key_bytes == 32 /\
                 B.length 'nonce_bytes == 12 /\
                 B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'plain_bytes == SZ.v plain_len /\
                 B.length 'old == SZ.v plain_len + 16)
  ensures pts_to key 'key_bytes **
          pts_to nonce 'nonce_bytes **
          pts_to aad 'aad_bytes **
          pts_to plain 'plain_bytes **
          pure (B.length (C.chacha20_poly1305_seal 'key_bytes 'nonce_bytes 'aad_bytes 'plain_bytes) == B.length 'old) **
          pts_to out (C.chacha20_poly1305_seal 'key_bytes 'nonce_bytes 'aad_bytes 'plain_bytes)

fn chacha20_poly1305_open
  (key: array U8.t)
  (nonce: array U8.t)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  (out: array U8.t)
  requires pts_to key 'key_bytes **
           pts_to nonce 'nonce_bytes **
           pts_to aad 'aad_bytes **
           pts_to cipher 'cipher_bytes **
           pts_to out 'old **
           pure (B.length 'key_bytes == 32 /\
                 B.length 'nonce_bytes == 12 /\
                 B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'cipher_bytes == SZ.v cipher_len /\
                 B.length 'old + 16 == SZ.v cipher_len)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to key 'key_bytes **
          pts_to nonce 'nonce_bytes **
          pts_to aad 'aad_bytes **
          pts_to cipher 'cipher_bytes **
          pts_to out out_bytes **
          pure (B.length 'cipher_bytes >= 16 /\
                (ok ==> Some? (C.chacha20_poly1305_open 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes) /\
                         out_bytes == Some?.v (C.chacha20_poly1305_open 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes)) /\
                (not ok ==> C.chacha20_poly1305_open 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes == None /\
                            out_bytes == 'old))

fn move_suffix_to_front
  (raw: array U8.t)
  (raw_capacity: SZ.t)
  (buffered_len: SZ.t)
  (consumed_len: SZ.t)
  requires pts_to raw 'raw_bytes **
           pure (B.length 'raw_bytes == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity)
  returns new_len: SZ.t
  ensures exists* raw_after.
          pts_to raw raw_after **
          pure (B.length raw_after == SZ.v raw_capacity /\
                B.length (Ghost.reveal 'raw_bytes) == SZ.v raw_capacity /\
                SZ.fits (SZ.v raw_capacity) /\
                SZ.fits (SZ.v buffered_len) /\
                SZ.fits (SZ.v new_len) /\
                0 <= SZ.v new_len /\
                SZ.v consumed_len <= SZ.v buffered_len /\
                SZ.v buffered_len <= SZ.v raw_capacity /\
                SZ.v new_len == SZ.v buffered_len - SZ.v consumed_len /\
                SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
                SZ.v new_len <= SZ.v buffered_len /\
                Seq.equal
                  (Seq.slice raw_after 0 (SZ.v new_len))
                  (Seq.slice
                    (Ghost.reveal 'raw_bytes)
                    (SZ.v consumed_len)
                    (SZ.v buffered_len)))
