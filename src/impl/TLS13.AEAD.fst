module TLS13.AEAD

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module A = Pulse.Lib.Array
module AC = TLS13.Impl.ArrayCopy
module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module Crypto = TLS13.Crypto
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

let aead_alg_eq (a b:C.aead_alg) : r:bool{r <==> a == b} =
  match a, b with
  | C.AEAD_AES128_GCM, C.AEAD_AES128_GCM -> true
  | C.AEAD_CHACHA20_POLY1305, C.AEAD_CHACHA20_POLY1305 -> true
  | _, _ -> false

(** At the full buffer width the padding is empty, so a ChaCha20-Poly1305 key is
    stored verbatim and can be handed to the binding as-is. *)
let lemma_logical_key_chacha (key:B.bytes)
  : Lemma (requires B.length key == 32)
          (ensures C.logical_key C.AEAD_CHACHA20_POLY1305 key == key)
  = ()

(** An AES-128 key occupies the first 16 bytes of the padded buffer. *)
let lemma_logical_key_aes (key:B.bytes)
  : Lemma (requires B.length key == 32)
          (ensures Seq.equal (C.logical_key C.AEAD_AES128_GCM key) (Seq.slice key 0 16))
  = ()

fn aead_seal
  (alg: C.aead_alg)
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
          pure (B.length (C.aead_seal alg (C.logical_key alg 'key_bytes) 'nonce_bytes 'aad_bytes 'plain_bytes) == B.length 'old) **
          pts_to out (C.aead_seal alg (C.logical_key alg 'key_bytes) 'nonce_bytes 'aad_bytes 'plain_bytes)
{
  match alg {
    C.AEAD_CHACHA20_POLY1305 -> {
      lemma_logical_key_chacha 'key_bytes;
      Crypto.chacha20_poly1305_seal key nonce aad aad_len plain plain_len out;
    }
    C.AEAD_AES128_GCM -> {
      let mut aes_key = [| 0uy; 16sz |];
      AC.copy_prefix 16sz key 32sz aes_key 16sz;
      with aes_key_bytes. assert (pts_to aes_key aes_key_bytes);
      lemma_logical_key_aes 'key_bytes;
      assert (pure (Seq.equal aes_key_bytes (C.logical_key C.AEAD_AES128_GCM 'key_bytes)));
      Crypto.aes128_gcm_seal aes_key nonce aad aad_len plain plain_len out;
    }
  }
}

fn aead_open
  (alg: C.aead_alg)
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
                (ok ==> Some? (C.aead_open alg (C.logical_key alg 'key_bytes) 'nonce_bytes 'aad_bytes 'cipher_bytes) /\
                        out_bytes == Some?.v (C.aead_open alg (C.logical_key alg 'key_bytes) 'nonce_bytes 'aad_bytes 'cipher_bytes)) /\
                (not ok ==> C.aead_open alg (C.logical_key alg 'key_bytes) 'nonce_bytes 'aad_bytes 'cipher_bytes == None /\
                            out_bytes == 'old))
{
  match alg {
    C.AEAD_CHACHA20_POLY1305 -> {
      lemma_logical_key_chacha 'key_bytes;
      let ok = Crypto.chacha20_poly1305_open key nonce aad aad_len cipher cipher_len out;
      ok
    }
    C.AEAD_AES128_GCM -> {
      let mut aes_key = [| 0uy; 16sz |];
      AC.copy_prefix 16sz key 32sz aes_key 16sz;
      with aes_key_bytes. assert (pts_to aes_key aes_key_bytes);
      lemma_logical_key_aes 'key_bytes;
      assert (pure (Seq.equal aes_key_bytes (C.logical_key C.AEAD_AES128_GCM 'key_bytes)));
      let ok = Crypto.aes128_gcm_open aes_key nonce aad aad_len cipher cipher_len out;
      ok
    }
  }
}
