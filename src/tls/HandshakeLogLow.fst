module HandshakeLogLow

open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost
module List = FStar.List.Tot

module HS = FStar.HyperStack
module B = LowStar.Buffer

module C = TLSConstants
module Hash = Hashing
module HSM = HandshakeMessages

module LP = LowParse.Low.Base

module IncHash = EverCrypt.Hash.Incremental

open HandshakeLog.Common

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -LowParse -FStar.Tactics -FStar.Reflection'"

noeq
type hsl_state = {
  rgn:Mem.rgn;
  from_to:B.pointer (option range_t);
  parsed_bytes:(p:B.pointer (G.erased hbytes){
    B.(loc_disjoint (loc_buffer from_to) (loc_buffer p)) /\
    rgn `region_includes` B.(loc_union (loc_buffer from_to) (loc_buffer p))
  });
}

let region_of s = s.rgn

let index_from_to s h = B.deref h s.from_to

let parsed_bytes s h = G.reveal (B.deref h s.parsed_bytes)

let invariant s h =
  B.live h s.from_to /\ B.live h s.parsed_bytes

let footprint s = B.(loc_union (loc_buffer s.from_to) (loc_buffer s.parsed_bytes))

let frame_hsl_state _ _ _ _ = ()

let create r =
  let from_to = B.malloc r None 1ul in
  let parsed_bytes = B.malloc r (G.hide (Seq.empty)) 1ul in
  { rgn = r; from_to = from_to; parsed_bytes = parsed_bytes }
