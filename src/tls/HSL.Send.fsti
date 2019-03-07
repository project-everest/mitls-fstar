module HSL.Send

open FStar.Integers
open FStar.HyperStack.ST

module B = LowStar.Buffer
module HS = FStar.HyperStack

type buffer8 = B.buffer uint_8

type range_t (max:uint_32) =
  t:(uint_32 & uint_32){fst t <= snd t /\ snd t <= max}

val state : Type0

/// Might just be liveness of the buffer

val invariant : state -> HS.mem -> prop

val region_of : state -> GTot Mem.rgn

val footprint : state -> GTot B.loc

val buf : state -> GTot buffer8

let buf_len (st:state) : GTot uint_32 = B.len (buf st)

val indices : st:state -> HS.mem -> GTot (option (range_t (buf_len st)))

val signals : state -> HS.mem -> GTot (option (bool & bool & bool))

let region_includes r l = B.loc_regions true (Set.singleton r) `B.loc_includes` l

unfold let state_framing (st:state) (h0 h1:HS.mem)
  = indices st h0 == indices st h1 /\
    signals st h0 == signals st h1

val frame_state (st:state) (h0 h1:HS.mem) (l:B.loc)
  : Lemma
    (requires
      B.modifies l h0 h1 /\
      B.loc_disjoint (footprint st) l /\
      invariant st h0 /\
      B.live h1 (buf st))
    (ensures
      state_framing st h0 h1 /\
      invariant st h1)

val elim_invariant (st:state) (h:HS.mem)
  : Lemma
    (requires invariant st h)
    (ensures  B.live h (buf st))

val create (r:Mem.rgn) (b:buffer8)
  : ST state
       (requires (fun h0 -> True))
       (ensures  (fun h0 st h1 ->
         region_of st == r /\
	 buf st == b /\
	 indices st h1 == None /\
	 signals st h1 == None /\
	 B.fresh_loc (footprint st) h0 h1 /\
	 r `region_includes` (footprint st) /\
	 B.modifies B.loc_none h0 h1 /\
	 invariant st h1))


/// The preconditions are from HandshakeLog.fsti

val send_signals
  (st:state)
  (next_keys:option (bool & bool))
  (complete:bool)
  : ST (bool & bool & bool)
       (requires (fun h ->
         invariant st h /\
	 (Some? next_keys \/ complete)))
       (ensures  (fun h0 r h1 ->
         invariant st h1 /\
	 Some r == signals st h1 /\
	 B.modifies (footprint st) h0 h1))


/// Called by HS
/// No checking on the validity of the input range
/// The implementation will merge the argument with the current range it has

val send_fragment
  (st:state)
  (from_to:range_t (buf_len st))
  : ST (range_t (buf_len st))
       (requires (fun h -> invariant st h))
       (ensures  (fun h0 r h1 ->
         invariant st h1 /\
	 Some r == indices st h1 /\
	 B.modifies (footprint st) h0 h1))


/// Need another API to be used by record
/// That resets indices and signals to None?
