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

#reset-options
   "--log_queries --query_stats \
    --using_facts_from 'Prims FStar LowStar -FStar.Reflection -FStar.Tactics -FStar.UInt128 -FStar.Math' \
    --using_facts_from 'Mem HandshakeLogLow HandshakeLog.Common Types_s Words_s Spec.Hash.Definitions.bytes' \
    --using_facts_from 'TLSError'"

type partial_flight =
  | Init
  | HRR
  | C_SKE_SHD_0: begin_ske:uint_32 -> partial_flight


noeq
type hsl_state = {
  rgn:Mem.rgn;
  from_to:B.pointer (option range_t);
  parsed_bytes:(p:B.pointer (G.erased hbytes){
   let open B in
   let locs =
     [loc_buffer from_to;
      loc_buffer p]
   in
    all_disjoint locs /\
    rgn `region_includes` B.loc_union_l locs
  });
}

let region_of s = s.rgn

let index_from_to s h = B.deref h s.from_to

let parsed_bytes s h = G.reveal (B.deref h s.parsed_bytes)

let invariant s h =
  B.live h s.from_to /\
  B.live h s.parsed_bytes

let footprint s = B.(loc_union (loc_buffer s.from_to) (loc_buffer s.parsed_bytes))

let frame_hsl_state _ _ _ _ = ()

let create r =
  let from_to = B.malloc r None 1ul in
  let parsed_bytes = B.malloc r (G.hide (Seq.empty)) 1ul in
  { rgn = r; from_to = from_to; parsed_bytes = parsed_bytes }

let receive_flight_hrr (st:hsl_state) (b:b8) (from to:uint_32) =
  admit()

let receive_flight_c_ske_shd (st:hsl_state) (b:b8) (from to:uint_32) = admit()


// /// There's only one message in this flight
// /// So, there's no incremental parsing to be performed
// let receive_flight_hrr st b from to =
//   match !* st.from_to with
//   | None ->
//   | Some (from, to) ->


//   : ST (TLSError.result (option flight_hrr))    //end input buffer index for the flight
//        (requires basic_pre_post st b  from to)
//        (ensures  receive_post st b from to valid_flight_hrr)
