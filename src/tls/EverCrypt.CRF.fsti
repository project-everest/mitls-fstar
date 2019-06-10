module EverCrypt.CRF

/// Status. See also `Test.CRF.fst`.
///
/// * Relocate to EverCrypt? But we depend on mitls flags.
///
/// * Still relies on `FStar.Monotonic.DependentMap`, not clearly
///   compatible with location-based modifies and Stack. For now I am
///   assuming a modifies clause. But we need to find a style where we
///   can modify the TLS region without too much trouble.

module Concrete = EverCrypt.Hash.Incremental
module Hash = EverCrypt.Hash

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module U32 = FStar.UInt32
module G = FStar.Ghost

open FStar.HyperStack.ST

let model = Flags.model
// not sure where to put the flags, or if we need a separate one

/// We first switch to a (non-extracted) implementation of the
/// EverCrypt.Hash.Incremental API that accumulates the text to hash
/// it using the pure spec only at extraction-time. When model=false,
/// the two implementations share the same full specs.
///
/// JP: Note that the state is not abstract, i.e. we don't re-add another layer
/// of abstraction with framing lemmas. Should we?

// TODO test that verification usability matches Concrete.
// TODO refactor EverCrypt to make such switches less verbose?
// TODO make the state abstract---requires pre/post rewriting
// TODO hide Model, treating hashed as an abstract predicate. Confirm we don't import algorithmic specs.

#set-options "--max_fuel 0 --max_ifuel 0"

/// Re-exporting all the definitions with a switch
/// ----------------------------------------------

unfold noextract
let bytes = Model.CRF.bytes

unfold noextract
let e_alg = Concrete.e_alg

unfold noextract
let fresh_loc = Concrete.fresh_loc

/// Overriding things
/// -----------------

/// This is very finely tuned to avoid inference issues.
type mstate a = a': Concrete.alg { a' == a } & p:B.pointer bytes {
  B.(loc_disjoint (loc_addr_of_buffer p) (loc_region_only true Mem.tls_tables_region))
}

let state (a: Concrete.alg) =
  if model then
    mstate a
  else
    Concrete.state a

// UGH!!!
noextract inline_for_extraction
let fst (#a: e_alg) (s: state (G.reveal a){model}):
  Tot (a': Concrete.alg { G.reveal a == a' })
=
  if model then
    let (| a, s |) = (s <: mstate (G.reveal a)) in
    a
  else
    false_elim ()

noextract inline_for_extraction
let snd (#a: e_alg) (s: state (G.reveal a){model}):
  Tot (p:B.pointer bytes {
    B.(loc_disjoint (loc_addr_of_buffer p) (loc_region_only true Mem.tls_tables_region))
  })
=
  if model then
    let (| a, s |) = (s <: mstate (G.reveal a)) in
    s
  else
    false_elim ()

let freeable #a h (s:state a) =
  if model then
    let s: B.pointer bytes = snd #(G.hide a) s in
    B.freeable s
  else
    Concrete.freeable #a h s

let preserves_freeable #a (s: state a) (h0 h1: HS.mem) =
  freeable h0 s ==> freeable h1 s

let footprint #a h (s: state a) =
  if model then
    B.loc_addr_of_buffer (snd #(G.hide a) s)
  else
    Concrete.footprint #a h s

let invariant #a h (s: state a) =
  if model then
    let s: B.pointer bytes = snd #(G.hide a) s in
    B.live h s /\ S.length (B.deref h s) < pow2 61
  else
    Concrete.invariant #a h s

let invariant_loc_in_footprint
  (#a: Concrete.alg)
  (s: state a)
  (m: HS.mem)
: Lemma
  (requires (invariant m s))
  (ensures (Concrete.loc_in (footprint m s) m))
  [SMTPat (invariant m s)]
=
  ()

let hashed #a h (s: state a) =
  if model then
    let s: B.pointer bytes = snd #(G.hide a) s in
    B.deref h s
  else
    let s: Concrete.state a = s in
    Concrete.hashed h s

#push-options "--max_ifuel 1"
let hash_fits (#a:Hash.alg) (h:HS.mem) (s:state a): Lemma
  (requires (
    invariant h s))
  (ensures (
    S.length (hashed h s) < Spec.Hash.Definitions.max_input_length a))
  [ SMTPat (hashed h s) ]
=
  assert_norm (pow2 61 < pow2 125);
  ()
#pop-options

let frame_invariant (#a: Concrete.alg) (l: B.loc) (s: state a) (h0 h1: HS.mem): Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant h1 s /\
    footprint h0 s == footprint h1 s))
  [ SMTPat (invariant h1 s); SMTPat (B.modifies l h0 h1) ]
=
  ()

let frame_hashed (#a: Concrete.alg) (l: B.loc) (s: state a) (h0 h1: HS.mem): Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (hashed h0 s == hashed h1 s))
  [ SMTPat (hashed h1 s); SMTPat (B.modifies l h0 h1) ]
=
  ()

let frame_freeable (#a: Concrete.alg) (l: B.loc) (s: state a) (h0 h1: HS.mem): Lemma
  (requires (
    invariant h0 s /\
    freeable h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (freeable h1 s))
  [ SMTPat (freeable h1 s); SMTPat (B.modifies l h0 h1) ]
=
  ()

/// Stateful API
/// ------------

(** @type: true
*)
val create_in (a: Hash.alg) (r: HS.rid): ST (state a)
  (requires (fun _ ->
    // NEW! ↓
    B.(loc_disjoint (loc_region_only true r) (loc_region_only true Mem.tls_tables_region)) /\
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant h1 s /\
    hashed h1 s == S.empty /\
    B.(modifies loc_none h0 h1) /\
    fresh_loc (footprint h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint h1 s)) /\
    freeable h1 s))

(** @type: true
*)
val init: a:e_alg -> (
  let a = G.reveal a in
  s:state a -> Stack unit
  (requires (fun h0 ->
    invariant h0 s))
  (ensures (fun h0 _ h1 ->
    preserves_freeable s h0 h1 /\
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
  preserves_freeable s h0 h1 /\
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
  // NEW! ↓ constrained to ST because Model.CRF.hash (fix MDM?)
  ST unit
    (requires fun h0 ->
      invariant h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (loc_buffer dst) (footprint h0 s)) /\
      // NEW! ↓
      B.(loc_disjoint (loc_buffer dst) (loc_region_only true Mem.tls_tables_region)))
    (ensures fun h0 s' h1 ->
      preserves_freeable s h0 h1 /\
      invariant h1 s /\
      hashed h0 s == hashed h1 s /\
      footprint h0 s == footprint h1 s /\
      // NEW! ↓
      B.(modifies (loc_buffer dst `loc_union`
        footprint h0 s `loc_union`
        loc_region_only true Mem.tls_tables_region) h0 h1) /\
      S.equal (B.as_seq h1 dst) (Spec.Hash.hash a (hashed h0 s)))

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
    freeable h0 s /\
    invariant h0 s)
  (ensures fun h0 _ h1 ->
    B.modifies (footprint h0 s) h0 h1))
