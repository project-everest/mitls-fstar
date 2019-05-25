module EverCrypt.CRF

module Concrete = EverCrypt.Hash.Incremental
module Hash = EverCrypt.Hash 

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open FStar.HyperStack.ST 

let model = Flags.model 
// not sure where to put the flags, or if we need a separate one 

/// We first switch to a (non-extracted) implementation of the
/// EverCrypt.Hash.Incremental API that accumulates the text to hash
/// it using the pure spec only at extraction-time. When model=false,
/// the two implementations share the same full specs.

// TODO test that verification usability matches Concrete. 
// TODO refactor EverCrypt to make such switches less verbose? 


let bytes = Concrete.bytes 
type hashable = s:bytes  {Seq.length s < pow2 61} 

type mstate = hashable 
// tried first a stateful variant, unnecessary since Concrete is
// actually state-passing.
// type mstate = b:B.buffer hashable {B.length b = 1}

let state (a:Hash.alg) = if model then mstate else Concrete.state a

let footprint #a (s: state a) h = 
  if model then 
    B.loc_none // B.loc_addr_of_buffer (s <: mstate)
  else 
    Concrete.footprint #a s h // (s <: Concrete.state a) h
  
let freeable #a (s:state a) h = 
  if model then True else Concrete.freeable #a s h

let preserves_freeable #a (s: state a) (h0 h1: HS.mem) = 
  if model then True else Concrete.preserves_freeable #a s h0 h1

let modifies_disjoint_preserves #a (l: B.loc) (h0 h1: HS.mem) (s: state a): Lemma 
  (requires (
    B.modifies l h0 h1 /\
    B.loc_disjoint l (footprint #a s h0) /\ ( 
    if model then True else 
      let hash_state = Concrete.State?.hash_state #a s in
      Hash.invariant #a hash_state h0)))
  (ensures (
    footprint #a s h0 == footprint #a s h1 /\ (
    if model then True else 
      let hash_state = Concrete.State?.hash_state #a s in
      Hash.invariant #a hash_state h1 /\
      Hash.repr #a hash_state h1 == Hash.repr #a hash_state h0 
      )))
=
  if model then () else Concrete.modifies_disjoint_preserves #a l h0 h1 s

// #set-options "--max_fuel 0 --max_ifuel 0"
unfold
let hashes (#a: Hash.alg) (h: HS.mem) (s: state a) (b: bytes) =
  if model then (
    Seq.length b < pow2 61 /\  Seq.equal s b 
    // B.live h (s <: mstate) /\
    // Seq.equal (B.get h (s <: mstate) 0) b
    )
  else 
    Concrete.hashes #a h s b 

val create_in (a: Hash.alg) (r: HS.rid): ST (state a)
  (requires (fun _ ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    hashes h1 s Seq.empty /\
    B.(modifies loc_none h0 h1) /\
    Hash.fresh_loc (footprint s h1) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint s h1)) /\
    freeable s h1))

unfold
let update_pre
  (a: Hash.alg)
  (s: state a)
  (prev: Ghost.erased bytes)
  (data: B.buffer UInt8.t)
  (len: UInt32.t)
  (h0: HS.mem)
=
  hashes h0 s (Ghost.reveal prev) /\
  B.live h0 data /\
  UInt32.v len = B.length data /\
  Seq.length (Ghost.reveal prev) + UInt32.v len < pow2 61 /\
  B.(loc_disjoint (loc_buffer data) (footprint s h0))

unfold
let update_post
  (a: Hash.alg)
  (s s': state a)
  (prev: Ghost.erased bytes)
  (data: B.buffer UInt8.t)
  (len: UInt32.t)
  (h0 h1: HS.mem)
=
  B.(modifies (footprint s h0) h0 h1) /\
  footprint s h0 == footprint s' h1 /\
  hashes h1 s' (Seq.append (Ghost.reveal prev) (B.as_seq h0 data)) /\
  preserves_freeable s h0 h1 /\ (
  if model then 
    True 
  else 
    Concrete.State?.hash_state #a s == Concrete.State?.hash_state #a s' /\
    Concrete.State?.buf #a s == Concrete.State?.buf #a s' )

val update:
  a:Hash.alg ->
  s:state a ->
  prev:Ghost.erased bytes ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack (state a)
    (requires fun h0 -> update_pre a s prev data len h0)
    (ensures fun h0 s' h1 -> update_post a s s' prev data len h0 h1)

inline_for_extraction
let finish_st (a: Hash.alg) =
  s:state a ->
  prev:Ghost.erased bytes ->
  dst: Hacl.Hash.Definitions.hash_t a ->
  Stack unit
    (requires fun h0 ->
      hashes h0 s (Ghost.reveal prev) /\
      B.live h0 dst /\
      B.(loc_disjoint (loc_buffer dst) (footprint s h0)))
    (ensures fun h0 s' h1 ->
      assert_norm (pow2 61 < pow2 125);
      hashes h1 s (Ghost.reveal prev) /\
      preserves_freeable s h0 h1 /\
      footprint s h0 == footprint s h1 /\
      B.(modifies (loc_union (loc_buffer dst) (footprint s h0)) h0 h1) /\
      Seq.equal (B.as_seq h1 dst) (Spec.Hash.hash a (Ghost.reveal prev)))

val finish: a:Hash.alg -> finish_st a

val free: 
  a:Hash.alg ->
  s:state a -> 
  ST unit
  (requires fun h0 ->
    freeable s h0 /\ (
    if model then 
      True
    else (
      let Concrete.State hash_state buf_ _ = (s <: Concrete.state a) in
      B.live h0 buf_ /\
      B.(loc_disjoint (loc_buffer buf_) (Hash.footprint hash_state h0)) /\
      Hash.invariant hash_state h0)))
  (ensures fun h0 _ h1 ->
    B.modifies (footprint s h0) h0 h1)
