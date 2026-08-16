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
(** The share a peer offering *both* groups contributes to the ECDH at [g]. *)
let kex_split_share (g:C.kex_group) (x25519_bytes p256_bytes:B.bytes) : B.bytes =
  match g with
  | C.KexX25519 -> x25519_bytes
  | C.KexP256 -> p256_bytes

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

(** ECDH against a peer whose two possible shares are held **in their natural
    widths** rather than padded to a uniform 65 bytes.

    [kex_shared_runtime] above suits the client, whose mirror stores whichever
    single share the *server* named in its ServerHello, in the uniform
    [kex_share_storage] buffer.  A server's mirror is different: it stores the
    ClientHello's *offer*, which may carry an X25519 share and a secp256r1 share
    at the same time, so it keeps a 32-byte slot and a 65-byte slot side by side.
    Padding the 32-byte one only to have [unpad_share_65] undo it would cost a
    copy and a pair of extensional-equality lemmas at every call.

    Both arms therefore go straight to the raw binding, which already takes
    exactly the width its group requires. *)
fn kex_shared_split_runtime
  (g: C.kex_group)
  (sk: array U8.t)
  (pk32: array U8.t)
  (pk65: array U8.t)
  (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk32 'x25519_bytes **
           pts_to pk65 'p256_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\
                 B.length 'x25519_bytes == 32 /\
                 B.length 'p256_bytes == 65 /\
                 B.length 'old == 32)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to sk 'sk_bytes **
          pts_to pk32 'x25519_bytes **
          pts_to pk65 'p256_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32 /\
                kex_shared_call g 'sk_bytes
                  (kex_split_share g 'x25519_bytes 'p256_bytes)
                  out_bytes ok)

(** The server's own public share at the negotiated group, written into the
    uniform 65-byte buffer the send path carries, together with the share's true
    wire width.

    This is the build-direction counterpart of [kex_shared_runtime]: the same
    "one buffer, one explicit group tag, never a length test" discipline, but
    for the value the server puts on the wire rather than the one it reads off
    it.  The X25519 arm writes 32 bytes and leaves the remaining 33 as it found
    them, so the logical share is the [kex_public_len g]-byte prefix -- exactly
    [C.unpad_share_65], as on the read side. *)
fn kex_public_from_private_runtime
  (g: C.kex_group)
  (sk: array U8.t)
  (out65: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to out65 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'old == 65)
  returns n: SZ.t
  ensures exists* out_bytes.
          pts_to sk 'sk_bytes **
          pts_to out65 out_bytes **
          pure (B.length out_bytes == 65 /\
                SZ.v n == C.kex_public_len g /\
                Seq.equal
                  (C.unpad_share_65 out_bytes (C.kex_public_len g))
                  (C.kex_public_from_private g 'sk_bytes))
