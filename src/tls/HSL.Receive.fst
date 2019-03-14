module HSL.Receive

open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost
module List = FStar.List.Tot

module HS = FStar.HyperStack
module B = LowStar.Buffer

module HSM = HandshakeMessages
module LP = LowParse.Low.Base

open HSL.Common

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

noeq
type hsl_state = {
  rgn: Mem.rgn;
  from_to: B.pointer (option range_t);
  parsed_bytes: (p:B.pointer (G.erased bytes){
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

let receive_flight13_ee_c_cv_fin _ _ _ _ = admit()
let receive_flight13_ee_cr_c_cv_fin _ _ _ _ = admit ()
let receive_flight13_ee_fin _ _ _ _ = admit ()

#set-options "--log_queries --query_stats --print_z3_statistics"
let advanced_parsed_bytes (st:_) (b:b8) (from to:uint_32)
  : Stack unit
    (requires fun h ->
      basic_pre_post st b from to h)
    (ensures fun h0 _ h1 ->
      B.modifies (footprint st) h0 h1 /\  //only local footprint is modified
      (let start, finish  = update_window (index_from_to st h0) from to in
      index_from_to st h1 == Some (start, finish) /\
      finish == to /\
      parsed_bytes st h1 == B.as_seq h0 (B.gsub b start (finish - start)))) = admit()

(*
let reset_parsed_bytes

// let receive_flight13_fin st b from to =
//   if to > LP.validator_max_length then Error "Input buffer too large" else // needed because validators can work only for slices of size <= LP.validator_max_length, to provide for error codes
//   let open LP in
//   let b_slice =
//     let b = B.sub b 0ul to in
//     {
//       base = b;
//       len = to
//     }
//   in
//   let pos = HSM13.handshake13_validator b_slice from in
//   if pos = LP.validator_error_not_enough_data
//   then (advanced_parsed_bytes st b from to;
//         Correct None)
//   else if pos > LP.validator_max_length
//   then Error "Invalid finish message"
//   else let flt = ... in
//        reset_parsed_bytes;
//        Correct (Some flt)
*)

let receive_flight13_c_cv_fin _ _ _ _ = admit ()
let receive_flight13_eoed _ _ _ _ = admit ()
let receive_flight13_nst _ _ _ _ = admit ()
