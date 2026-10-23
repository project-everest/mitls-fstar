module TLS13.Crypto.Secret

(**
  Bridge between TLS's public bytes ([FStar.UInt8.t]) and hacl-pulse's secret
  bytes ([Hacl.Secret.UInt8.t]).

  hacl-pulse keeps secret bytes abstract so that its own code is checked for
  constant-time discipline; underneath, a secret byte *is* a [FStar.UInt8.t].
  The TLS code has no secrecy discipline of its own, so at the boundary every
  buffer is reinterpreted in place: [classify_seq]/[declassify_seq] are the
  identity on the representation, and [secret a] is the same pointer as [a].
  hacl-pulse only provides the byte-level [Hacl.Secret.UInt8.classify] and
  [Hacl.Secret.Declassify.u8]; the sequence- and array-level views below are
  stubbed here until they exist upstream.
**)

#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module SB = Spec.Byte

val classify_seq (s: Seq.seq U8.t) : Tot (r: Seq.seq S8.t { Seq.length r == Seq.length s })

val declassify_seq (s: Seq.seq S8.t) : Tot (r: Seq.seq U8.t { Seq.length r == Seq.length s })

val classify_index (s: Seq.seq U8.t) (i: nat { i < Seq.length s })
  : Lemma (S8.v (Seq.index (classify_seq s) i) == U8.v (Seq.index s i))
          [SMTPat (Seq.index (classify_seq s) i)]

val declassify_index (s: Seq.seq S8.t) (i: nat { i < Seq.length s })
  : Lemma (U8.v (Seq.index (declassify_seq s) i) == S8.v (Seq.index s i))
          [SMTPat (Seq.index (declassify_seq s) i)]

val declassify_classify (s: Seq.seq U8.t)
  : Lemma (declassify_seq (classify_seq s) == s)
          [SMTPat (declassify_seq (classify_seq s))]

val classify_declassify (s: Seq.seq S8.t)
  : Lemma (classify_seq (declassify_seq s) == s)
          [SMTPat (classify_seq (declassify_seq s))]

val classify_slice (s: Seq.seq U8.t) (i: nat) (j: nat { i <= j /\ j <= Seq.length s })
  : Lemma (classify_seq (Seq.slice s i j) == Seq.slice (classify_seq s) i j)

val declassify_slice (s: Seq.seq S8.t) (i: nat) (j: nat { i <= j /\ j <= Seq.length s })
  : Lemma (declassify_seq (Seq.slice s i j) == Seq.slice (declassify_seq s) i j)

val declassify_append (s1 s2: Seq.seq S8.t)
  : Lemma (declassify_seq (Seq.append s1 s2) ==
           Seq.append (declassify_seq s1) (declassify_seq s2))

(** The bytes of a sequence of byte values, as GCM's specification works on
    [Spec.Byte.elem]s rather than on (secret) machine bytes. *)
let of_elems (s: Seq.seq SB.elem) : GTot (Seq.seq U8.t) = declassify_seq (SB.secrets s)

(** The view of a public-byte array as a secret-byte array: the same pointer. *)
inline_for_extraction
val secret (a: A.array U8.t) : A.array S8.t

val secret_length (a: A.array U8.t)
  : Lemma (A.length (secret a) == A.length a)
          [SMTPat (A.length (secret a))]

ghost fn to_secret (a: A.array U8.t) (#p: perm) (#s: erased (Seq.seq U8.t))
  requires A.pts_to a #p s
  ensures A.pts_to (secret a) #p (classify_seq s)

ghost fn of_secret (a: A.array U8.t) (#p: perm) (#s: erased (Seq.seq S8.t))
  requires A.pts_to (secret a) #p s
  ensures A.pts_to a #p (declassify_seq s)
