module TLS13.KEX

#lang-pulse

(**
  Agile ECDH.

  `TLS13.Crypto` exposes one raw binding per supported key-exchange group, each
  a direct binding to a single primitive with that group's public-value length
  baked into its signature.  This module is the only place where the negotiated
  group selects between them, and it does so by branching on the group tag the
  server put on the wire -- never on a buffer's length.  The C stubs therefore
  perform no dispatch at all.

  Peer key-share buffers are a uniform 65 bytes wide -- the widest offered group
  -- so that their layout does not depend on the negotiated group; a 32-byte
  X25519 share is stored zero-padded (`C.pad_share_65`).  `C.unpad_share_65` is
  the spec-level projection back out of that buffer, and the X25519 branch
  materialises the 32-byte share it needs rather than letting the binding know
  about the padding convention.
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

(** Runtime equality on groups.  Written out rather than relying on structural
    equality so that extraction produces a plain comparison. *)
inline_for_extraction
val kex_group_eq (a b:C.kex_group) : r:bool{r <==> a == b}

(** The runtime public length of a group, as a machine integer. *)
inline_for_extraction
val kex_public_len_sz (g:C.kex_group) : n:SZ.t{SZ.v n == C.kex_public_len g}

(** The abstract "the binding was called and returned [ok]" predicate, agile
    over the group.  Its only consumer is [lemma_kex_shared_call_success]. *)
noextract
val kex_shared_call
  (g:C.kex_group)
  (sk:B.bytes)
  (pk:B.bytes)
  (shared:B.bytes)
  (ok:bool)
  : GTot prop

noextract
val lemma_kex_shared_call_success
  (g:C.kex_group)
  (sk:B.bytes)
  (pk:B.bytes)
  (shared:B.bytes)
  (ok:bool)
  : Lemma
      (requires kex_shared_call g sk pk shared ok /\
                ok /\
                B.length shared == 32)
      (ensures Some? (C.kex_shared g sk pk) /\
               C.kex_shared g sk pk == Some (Some?.v (C.kex_shared g sk pk)) /\
               Some?.v (C.kex_shared g sk pk) == shared)

(** ECDH against a peer share held in the uniform 65-byte buffer.  The logical
    share is the group's [kex_public_len]-byte prefix, recovered through the
    explicit group tag. *)
fn kex_shared_runtime
  (g: C.kex_group)
  (sk: array U8.t)
  (pk65: array U8.t)
  (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk65 'pk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\
                 B.length 'pk_bytes == 65 /\
                 B.length 'old == 32)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to sk 'sk_bytes **
          pts_to pk65 'pk_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32 /\
                kex_shared_call g 'sk_bytes
                  (C.unpad_share_65 'pk_bytes (C.kex_public_len g))
                  out_bytes ok)
