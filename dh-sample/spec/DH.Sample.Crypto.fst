module DH.Sample.Crypto

(**
  DH.Sample.Crypto — a *pure, explicit, idealized* cryptographic-spec interface
  for the DH sample.  Everything here is an ordinary total F* function with
  concrete definitions (no admitted or assumed vals), so the equations
  the protocol relies on are theorems, not axioms.

  We model a maximally simple but faithful idealization:

    * The DH group is the additive group of exponents in [0, 2^32) encoded
      big-endian into 4 bytes; the generator's power map g^x is the identity
      encoding of the exponent x.  This makes `dh_exp` injective and lets a
      party recover a peer's exponent from a share — exactly the abstraction a
      Dolev–Yao "symbolic" model gives, but done here with concrete integers.

    * DH agreement combines the two exponents *symmetrically*, so both parties
      derive the same secret:  dh_agree x (g^y) == dh_agree y (g^x).
      This is the key correctness equation (`lemma_dh_agree`).

    * Signatures are a deterministic keyed digest.  `verify` is a *predicate*
      (a `prop`) that holds exactly when a signature equals the one `sign`
      would produce, giving both signature correctness and the "checking"
      semantics the state machine needs (`lemma_sign_verify`).

  None of this is meant to be cryptographically strong: it is an idealized
  specification whose equations are the ones the protocol proof consumes.
*)

module Seq  = FStar.Seq
module U8   = FStar.UInt8
module M    = FStar.Math.Lemmas
open DH.Sample.Types

(** 2^32, the exponent modulus for our 4-byte encoding. *)
let q : pos = 4294967296          (* = pow2 32 *)

(** ── Big-endian byte <-> natural number conversions ────────────────────── *)

(** Decode 4 big-endian bytes as a natural number in [0, 2^32). *)
let be4_to_n (b:lbytes 4) : n:nat{ n < q } =
  let b0 = U8.v (Seq.index b 0) in
  let b1 = U8.v (Seq.index b 1) in
  let b2 = U8.v (Seq.index b 2) in
  let b3 = U8.v (Seq.index b 3) in
  b0 * 16777216 + b1 * 65536 + b2 * 256 + b3

(** Encode an integer as 4 big-endian bytes (per-byte modular reduction). *)
let n_to_be4 (x:int) : lbytes 4 =
  let b0 = U8.uint_to_t ((x / 16777216) % 256) in
  let b1 = U8.uint_to_t ((x / 65536) % 256) in
  let b2 = U8.uint_to_t ((x / 256) % 256) in
  let b3 = U8.uint_to_t (x % 256) in
  let s = Seq.create 4 b0 in
  let s = Seq.upd s 1 b1 in
  let s = Seq.upd s 2 b2 in
  Seq.upd s 3 b3

(** Encode a value < 2^64 as 8 big-endian bytes (top 4 then bottom 4). *)
let n_to_be8 (x:nat) : lbytes 8 =
  Seq.append (n_to_be4 (x / q)) (n_to_be4 (x % q))

(**
  Round-trip law: decoding the 4-byte big-endian encoding of any exponent in
  range recovers it.  This is the arithmetic backbone of DH agreement — it is
  what lets a party recover the peer's exponent from the peer's share.
*)
let lemma_be4_roundtrip (v:nat{ v < q })
  : Lemma (ensures be4_to_n (n_to_be4 v) == v)
=
  let s = n_to_be4 v in
  (* The four extracted bytes, by definition of n_to_be4 and Seq.upd/index. *)
  assert (U8.v (Seq.index s 0) == (v / 16777216) % 256);
  assert (U8.v (Seq.index s 1) == (v / 65536) % 256);
  assert (U8.v (Seq.index s 2) == (v / 256) % 256);
  assert (U8.v (Seq.index s 3) == v % 256);
  (* Reassemble: (v/2^24)%256 * 2^24 + (v/2^16)%256 * 2^16
                 + (v/2^8)%256 * 2^8 + v%256 == v, for v < 2^32. *)
  M.lemma_div_mod v 16777216;
  M.lemma_div_mod (v % 16777216) 65536;
  M.lemma_div_mod (v % 65536) 256

(** ── Idealized Diffie–Hellman ──────────────────────────────────────────── *)

(**
  The exponent denoted by a scalar (private key) or by a share (public key).
  In this idealization both are just the big-endian decoding of the bytes.
*)
let scalar_exp (s:dh_scalar) : n:nat{ n < q } = be4_to_n s
let share_exp  (sh:dh_share) : n:nat{ n < q } = be4_to_n sh

(**
  The public-share map g^x.  Idealized as the identity encoding of the
  exponent, hence injective and invertible via `share_exp`.
*)
let dh_exp (s:dh_scalar) : dh_share = n_to_be4 (scalar_exp s)

(** Recovering the exponent from a freshly generated share is exact. *)
let lemma_share_of_exp (s:dh_scalar)
  : Lemma (ensures share_exp (dh_exp s) == scalar_exp s)
= lemma_be4_roundtrip (scalar_exp s)

(**
  The symmetric combination of two exponents.  Ordering the pair makes the
  combination commutative, which is exactly what forces both endpoints to agree
  on the shared secret.  Both exponents are < 2^32, so the result is < 2^64.
*)
let combine_exps (a b:nat{ a < q /\ b < q }) : n:nat{ n < q * q } =
  if a <= b then a * q + b else b * q + a

(** Commutativity of the exponent combination. *)
let lemma_combine_sym (a b:nat{ a < q /\ b < q })
  : Lemma (ensures combine_exps a b == combine_exps b a)
= ()   (* both branches yield min*q + max *)

(**
  DH agreement: an endpoint holding private scalar [s] and the peer's public
  share [sh] derives the shared secret by combining the two exponents.
*)
let dh_agree (s:dh_scalar) (sh:dh_share) : shared_secret =
  n_to_be8 (combine_exps (scalar_exp s) (share_exp sh))

(**
  The fundamental DH correctness equation:  the initiator holding [x] and the
  responder holding [y] derive the SAME shared secret, because
      dh_agree x (g^y) == dh_agree y (g^x).
  This is what guarantees the two completed endpoints share a session key.
*)
let lemma_dh_agree (x y:dh_scalar)
  : Lemma (ensures dh_agree x (dh_exp y) == dh_agree y (dh_exp x))
=
  lemma_share_of_exp y;   (* share_exp (dh_exp y) == scalar_exp y *)
  lemma_share_of_exp x;   (* share_exp (dh_exp x) == scalar_exp x *)
  lemma_combine_sym (scalar_exp x) (scalar_exp y)

(** ── Idealized signatures ──────────────────────────────────────────────── *)

(**
  A deterministic keyed digest folding a byte string into two 32-bit
  accumulators (a toy "MAC").  Only determinism is needed for the sample; no
  collision/forgery resistance is claimed or used.
*)
let rec fold_sum (b:bytes) (i:nat{ i <= Seq.length b }) (acc:nat)
  : Tot nat (decreases (Seq.length b - i))
=
  if i = Seq.length b then acc
  else fold_sum b (i + 1) (acc + U8.v (Seq.index b i))

let rec fold_mix (b:bytes) (i:nat{ i <= Seq.length b }) (acc:nat)
  : Tot nat (decreases (Seq.length b - i))
=
  if i = Seq.length b then acc
  else fold_mix b (i + 1) ((acc * 31 + U8.v (Seq.index b i) + 1))

(** The 8-byte digest of a byte string. *)
let digest8 (b:bytes) : signature =
  Seq.append (n_to_be4 (fold_sum b 0 0)) (n_to_be4 (fold_mix b 0 0))

(**
  Sign a byte string [content] under principal [signer].  The signer's identity
  is included in the digest input, so verification binds the expected signer to
  the checked content.  This toy digest intentionally makes no collision-
  resistance claim.
*)
let sign (signer:principal) (content:bytes) : signature =
  digest8 (Seq.append signer content)

(**
  Signature verification, as a PREDICATE.  It holds exactly when [sig] is the
  signature [sign] would produce for ([signer], [content]).  Returning a `prop`
  (rather than a `bool`) avoids any need for decidable sequence equality and is
  exactly the shape consumed by the state-machine step relation.
*)
let verify (signer:principal) (content:bytes) (sig:signature) : prop =
  sig == sign signer content

(**
  Signature correctness: a genuine signature always verifies.  Together with
  the definition of `verify`, this is the full "signature checking" equational
  interface the protocol needs.
*)
let lemma_sign_verify (signer:principal) (content:bytes)
  : Lemma (ensures verify signer content (sign signer content))
= ()

(** ── Signed transcripts ────────────────────────────────────────────────── *)

(**
  The signed content of the two authentication signatures.  Following the
  informal protocol

      A -> B : A, g^x
      B -> A : B, g^y, Sign_B(A, g^x, g^y)
      A -> B : Sign_A(B, g^x, g^y)

  each signer binds the *intended partner's* identity together with both DH
  shares.  We therefore expose a single transcript builder parameterized by the
  partner identity that is written into the signed content:

    * B signs `transcript A gx gy` (partner = the initiator A);
    * A signs `transcript B gx gy` (partner = the responder B).

  The transcript is a fixed 12-byte string: partner(4) ++ g^x(4) ++ g^y(4).
*)
let transcript (partner:principal) (gx gy:dh_share) : bytes =
  Seq.append partner (Seq.append gx gy)
