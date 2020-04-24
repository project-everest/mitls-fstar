module Crypto.CRF

/// Status. See also `Test.CRF.fst`.
///
/// * Later: relocate to hacl-star/secure; we still depend on mitls flags.
///
/// * Still relies on `FStar.Monotonic.DependentMap`, which used old-style
/// modifies clauses incompatible with `LowStar.Buffer`. Model.CRF uses
/// `LowStar.Buffer.modifies_loc_regions_intro` to bridge between the old
/// and new styles.
///
module Concrete = EverCrypt.Hash.Incremental
module Hash = EverCrypt.Hash
module HD = Spec.Hash.Definitions

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module U32 = FStar.UInt32
module G = FStar.Ghost

open Mem
open FStar.HyperStack.ST

inline_for_extraction noextract
let model = Flags.model
// not sure where to put the flags, or if we need a separate one

/// We first switch (on [model]) to a non-extracted,
/// specification-based implementation of the
/// EverCrypt.Hash.Incremental API that accumulates the text to hash
/// it only to compute the tag.
///
/// To justify the switch, we review that the two implementations
/// share the same full functional specs and operate on an abstract
/// type that hides the change of representation.

// DONE JP: Note that the state is not abstract, i.e. we don't re-add
// another layer of abstraction with framing lemmas. Should we?

// TODO test that verification usability matches Concrete.
// TODO refactor EverCrypt to make such switches less verbose?
// TODO hide Model, treating hashed as an abstract predicate. Confirm we don't import algorithmic specs.

#set-options "--max_fuel 0 --max_ifuel 0"

/// Re-exporting all the definitions with a switch
/// ----------------------------------------------

unfold noextract
let bytes = Model.CRF.bytes

unfold noextract
let alg = Spec.Agile.Hash.hash_alg

unfold noextract
let e_alg = G.erased alg

/// Overriding things
/// -----------------

inline_for_extraction
val state: alg -> Type0

val footprint: #a:alg -> HS.mem -> state a -> GTot B.loc

val invariant: #a:alg -> HS.mem -> state a -> Type0

val invariant_loc_in_footprint
  (#a: alg)
  (s: state a)
  (m: HS.mem)
: Lemma
  (requires (invariant m s))
  (ensures (B.loc_in (footprint m s) m))
  [SMTPat (invariant m s)]

val hashed: #a:alg -> HS.mem -> state a -> GTot bytes

val hash_fits (#a:alg) (h:HS.mem) (s:state a): Lemma
  (requires (
    invariant h s))
  (ensures (
    S.length (hashed h s) <= HD.max_input_length a))
  [ SMTPat (hashed h s) ]

val frame_invariant (#a: alg) (l: B.loc) (s: state a) (h0 h1: HS.mem): Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant h1 s /\
    footprint h0 s == footprint h1 s))
  [ SMTPat (invariant h1 s); SMTPat (B.modifies l h0 h1) ]

val frame_hashed (#a: alg) (l: B.loc) (s: state a) (h0 h1: HS.mem): Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (hashed h0 s == hashed h1 s))
  [ SMTPat (hashed h1 s); SMTPat (B.modifies l h0 h1) ]

/// Stateful API
/// ------------

(** @type: true
*)
val create_in (a: alg) (r: HS.rid): ST (state a)
  (requires (fun _ ->
    // NEW! ↓
    B.(loc_disjoint (loc_region_only true r) (loc_region_only true Mem.tls_tables_region)) /\
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant h1 s /\
    hashed h1 s == S.empty /\
    B.(modifies loc_none h0 h1) /\
    fresh_loc (footprint h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint h1 s))))

(** @type: true
*)
val init: a:e_alg -> (
  let a = G.reveal a in
  s:state a -> Stack unit
  (requires (fun h0 ->
    invariant h0 s))
  (ensures (fun h0 _ h1 ->
    invariant h1 s /\
    hashed h1 s == S.empty /\
    footprint h0 s == footprint h1 s /\
    B.(modifies (footprint h0 s) h0 h1))))

unfold
let update_pre
  (a: Hash.alg)
  (s: state a)
  (data: B.buffer UInt8.t)
  (len: UInt32.t)
  (h0: HS.mem)
=
  invariant h0 s /\
  B.live h0 data /\
  U32.v len = B.length data /\
  S.length (hashed h0 s) + U32.v len < pow2 61 /\
  B.(loc_disjoint (loc_buffer data) (footprint h0 s))

unfold
let update_post
  (a: Hash.alg)
  (s: state a)
  (data: B.buffer UInt8.t)
  (len: UInt32.t)
  (h0 h1: HS.mem)
=
  invariant h1 s /\
  B.(modifies (footprint h0 s) h0 h1) /\
  footprint h0 s == footprint h1 s /\
  hashed h1 s == hashed h0 s `S.append` B.as_seq h0 data

(** @type: true
*)
val update:
  a:e_alg -> (
  let a = G.reveal a in
  s:state a ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 -> update_pre a s data len h0)
    (ensures fun h0 s' h1 -> update_post a s data len h0 h1))

/// Note: the state is left to be reused by the caller to feed more data into
/// the hash.
inline_for_extraction
let finish_st (a: Hash.alg) =
  s:state a ->
  dst: Hacl.Hash.Definitions.hash_t a ->
  // NEW! ↓ Constrained to ST because Model.CRF.hash updates a global table.
  ST unit
    (requires fun h0 ->
      invariant h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (loc_buffer dst) (footprint h0 s)) /\
      // NEW! ↓
      B.(loc_disjoint (loc_buffer dst) (loc_region_only true Mem.tls_tables_region)))
    (ensures fun h0 s' h1 ->
      invariant h1 s /\
      hashed h0 s == hashed h1 s /\
      footprint h0 s == footprint h1 s /\
      // NEW! ↓
      B.(modifies (
        loc_buffer dst `loc_union`
        footprint h0 s `loc_union`
        loc_region_only true Mem.tls_tables_region) h0 h1) /\
      S.equal (B.as_seq h1 dst) (Spec.Agile.Hash.hash a (hashed h0 s)) /\
      // NEW! ↓
      Model.CRF.hashed a (hashed h0 s))

(** @type: true
*)
val finish: a:e_alg -> finish_st (G.reveal a)

(** @type: true
*)
val free:
  a:e_alg -> (
  let a = G.reveal a in
  s:state a ->
  ST unit
  (requires fun h0 ->
    invariant h0 s)
  (ensures fun h0 _ h1 ->
    B.modifies (footprint h0 s) h0 h1))
