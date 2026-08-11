module TLS13.AEAD

#lang-pulse

(**
  Agile AEAD.

  `TLS13.Crypto` exposes one raw binding per supported algorithm, each a direct
  binding to a single primitive with that algorithm's key length baked into its
  signature.  This module is the only place where the negotiated algorithm
  selects between them, and it does so by branching on the algorithm itself --
  never on a key length.  The C stubs therefore perform no dispatch at all.

  Traffic-key buffers are a uniform 32 bytes wide so that their layout does not
  depend on the negotiated suite; a 16-byte AES-128 key is stored zero-padded
  (`C.pad_key_32`).  `C.logical_key` is the spec-level projection back out of that
  buffer, and the AES branch materialises the 16-byte key it needs rather than
  letting the binding know about the padding convention.
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

(** Runtime equality on algorithms.  Written out rather than relying on
    structural equality so that extraction produces a plain comparison. *)
inline_for_extraction
val aead_alg_eq (a b:C.aead_alg) : r:bool{r <==> a == b}

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
