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

(** The only external HKDF-expand boundary. The erased label and context
    witnesses pin the concrete info buffer to the verified HkdfLabel encoding
    without adding label-specific arguments to the extracted ABI. *)
fn hkdf_expand
  (secret: array U8.t)
  (info: array U8.t)
  (info_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  (#lbl: erased B.bytes)
  (#context: erased B.bytes)
  requires pts_to secret 'secret_bytes **
          pts_to info 'info_bytes **
          pts_to out 'old **
          pure (B.length 'secret_bytes == 32 /\
                B.length 'info_bytes == 520 /\
                B.length 'old == SZ.v out_len /\
                B.length (Ghost.reveal lbl) <= 249 /\
                B.length (Ghost.reveal context) <= 255 /\
                SZ.v out_len <= 8160 /\
                SZ.v info_len ==
                  C.hkdf_label_info_length
                    (Ghost.reveal lbl)
                    (Ghost.reveal context) /\
                'info_bytes ==
                  C.hkdf_label_info_buffer
                    (Ghost.reveal lbl)
                    (Ghost.reveal context)
                    (SZ.v out_len))
  ensures pts_to secret 'secret_bytes **
          pts_to info 'info_bytes **
          pure (B.length
                 (C.hkdf_expand_label
                   'secret_bytes
                   (Ghost.reveal lbl)
                   (Ghost.reveal context)
                   (SZ.v out_len)) == SZ.v out_len) **
          pts_to out (C.hkdf_expand_label
                       'secret_bytes
                       (Ghost.reveal lbl)
                       (Ghost.reveal context)
                       (SZ.v out_len))

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

(**
  secp256r1 bindings.  There is one binding per group rather than a single
  length-dispatched one: the caller knows the negotiated `C.kex_group` and picks
  the primitive from it.  The public value is 65 bytes (uncompressed SEC1) and
  the shared secret is the 32-byte X coordinate.
**)

fn p256_public_from_private (sk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'old == 65)
  ensures pts_to sk 'sk_bytes ** pts_to out (C.p256_public_from_private 'sk_bytes)

noextract
val p256_shared_call:
  sk:B.bytes ->
  pk:B.bytes ->
  shared:B.bytes ->
  ok:bool ->
  GTot prop

noextract
val lemma_p256_shared_call_success:
  sk:B.bytes ->
  pk:B.bytes ->
  shared:B.bytes ->
  ok:bool ->
  Lemma
    (requires p256_shared_call sk pk shared ok /\
              ok /\
              B.length shared == 32)
    (ensures Some? (C.p256_shared sk pk) /\
             C.p256_shared sk pk == Some (Some?.v (C.p256_shared sk pk)) /\
             Some?.v (C.p256_shared sk pk) == shared)

fn p256_shared_runtime (sk: array U8.t) (pk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk 'pk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'pk_bytes == 65 /\ B.length 'old == 32)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to sk 'sk_bytes **
          pts_to pk 'pk_bytes **
          pts_to out out_bytes **
          pure (p256_shared_call 'sk_bytes 'pk_bytes out_bytes ok)

(**
  Raw AEAD bindings, one per supported algorithm.  Each is a direct binding to a
  single primitive: the key array has exactly that algorithm's key length and the
  specification names that algorithm as a constant, so neither the C stub nor
  this interface performs any algorithm dispatch.  Agility is implemented in
  verified Pulse in `TLS13.AEAD`, which branches on the negotiated
  `C.aead_alg`.

  Both algorithms use a 12-byte nonce and a 16-byte tag, so the ciphertext
  length relation is algorithm-independent.
**)

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
          pts_to out (C.aead_seal C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'plain_bytes)

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
          pure ((ok ==> Some? (C.aead_open C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes) /\
                        out_bytes == Some?.v (C.aead_open C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes)) /\
                (not ok ==> C.aead_open C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes == None /\
                            out_bytes == 'old))

fn aes128_gcm_seal
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
           pure (B.length 'key_bytes == 16 /\
                 B.length 'nonce_bytes == 12 /\
                 B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'plain_bytes == SZ.v plain_len /\
                 B.length 'old == SZ.v plain_len + 16)
  ensures pts_to key 'key_bytes **
          pts_to nonce 'nonce_bytes **
          pts_to aad 'aad_bytes **
          pts_to plain 'plain_bytes **
          pts_to out (C.aead_seal C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'plain_bytes)

fn aes128_gcm_open
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
           pure (B.length 'key_bytes == 16 /\
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
          pure ((ok ==> Some? (C.aead_open C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes) /\
                        out_bytes == Some?.v (C.aead_open C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes)) /\
                (not ok ==> C.aead_open C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes == None /\
                            out_bytes == 'old))
