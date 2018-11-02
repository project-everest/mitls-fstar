module HSL

(*
 * This module is a prototype of handshake log module in mitls
 *)

open FStar.Integers
open FStar.HyperStack.ST
open LowStar.BufferOps

open FStar.BaseTypes

module G = FStar.Ghost
module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module M = TLS.HSL.Msg
module LP = LowParse.Low.Base

type loc = LowStar.Modifies.loc
type buffer8 = B.buffer uint8

(*
 * We currently model the reading side of TLS
 * HSL maintains a buffer, that record layer writes the incoming bytes in
 * The incoming bytes are serializations of HSLMsg
 *
 * HSL maintains two pointers in the buffer, p0 and p1
 * p0 represents the point until which HSL has parsed the incoming messages
 * Between p0 and p1 is the current, incomplete message
 * So, the record layer appends to the buffer after p1
 *
 * We also keep msgs: list of all subsequences in the buffer that are serializations of valid msgs
 *                    in each subsequence, we also keep a ghost repr of its parsing
 *)
abstract noeq
type message (len:uint32)= {
  from:(x:uint32{x <= len});
  to: (x:uint32{from <= x /\ x <= len});
  msg: M.msg
}
abstract noeq type hsl_state =
  | Mk_state: len:uint32 ->
              buf:buffer8{B.len buf == len} ->
              p0:reference uint32 ->
              p1:reference uint32 ->
              msgs:reference (G.erased (list (message len))) -> //can we have an erased_reference?
              hsl_state

(* abstract getters *)
abstract 
let hsl_get_len (st:hsl_state) 
  : GTot uint32 
  = st.len

abstract 
let hsl_get_buf (st:hsl_state) 
  : GTot (b:buffer8{B.len b == hsl_get_len st})
  = st.buf

abstract 
let hsl_get_p1 (st:hsl_state) (h:HS.mem) 
  : GTot uint32
  = HS.sel h st.p1
  
abstract 
let hsl_get_msgs (st:hsl_state) (h:HS.mem)
  : GTot (list (message (hsl_get_len st))) 
  = G.reveal (HS.sel h st.msgs)

let liveness (st:hsl_state) (h:HS.mem) =
  B.live h (hsl_get_buf st)

abstract
let msgs_inv (st:hsl_state) (h:HS.mem) =
  let msgs = hsl_get_msgs st h in
  let p0 = HS.sel h st.p0 in
  let p1 = hsl_get_p1 st h in
  p0 <= p1 /\
  p1 <= st.len /\
  (forall (m:message st.len). {:pattern List.Tot.memP m msgs}
        List.Tot.memP m msgs ==>
        m.to <= p0  /\
        (let delta = m.to - m.from in
         let sub = B.gsub st.buf m.from delta in
         match LP.parse M.msg_parser (B.as_seq h sub) with
         | None -> False
         | Some (msg, consumed) ->
           msg == m.msg /\
           consumed == v delta (* unsure about the latter part *)
         ))

abstract
let st_inv (st:hsl_state) (h:HS.mem) =
  (* Disjointness *)
  B.(loc_pairwise_disjoint [
       loc_mreference st.p0;
       loc_mreference st.p1;
       loc_buffer st.buf;
       loc_mreference st.msgs;
     ]) /\
  (* Liveness *)
  B.live h st.buf /\
  h `HS.contains` st.p0 /\
  h `HS.contains` st.p1 /\
  h `HS.contains` st.msgs /\
  (* Main stateful invariant *)
  msgs_inv st h

(* Questions:
      Is the HSL state recycled? i.e., what happens when the buffer is filled?
      Is it worth keeping HSL state after a flight has been parsed?
      How much can we do with monotonicity, e.g., the msgs reference would be convenient to model monotonically
*)

// (* Finally, the abstract invariant and its elimination *)
// abstract let hsl_invariant (st:hsl_state) (h:mem) = hsl_invariant_predicate st h

// (*
//  * This is a place where we can control what clients get to derive from the invariant
//  * For now, we put everything in here
//  *)
// let lemma_hsl_invariant_elim (st:hsl_state) (h:mem)
//   :Lemma (requires (hsl_invariant st h))
//          (ensures  (hsl_invariant_predicate st h))
//          [SMTPat (hsl_invariant st h)]
//   = ()

// (*
//  * HSL footprint = p0, p1, buffer contents between 0 and p1, and msgs
//  * This is not abstract, so that the client (Record) can append the buffer after p1, and use the framing lemma
//  *)
// let hsl_footprint (st:hsl_state) (h:mem{hsl_invariant st h}) =
//   loc_union (loc_union (loc_buffer (Buffer.gsub (hsl_get_buf st) 0ul (sel h (hsl_get_p1 st))))
//                        (loc_mreference (hsl_get_p0 st)))
//             (loc_union (loc_mreference (hsl_get_p1 st))
//                        (loc_mreference (hsl_get_msgs st)))

// (*
//  * Framing the HSL invariant across its footprint
//  *)
// let lemma_frame_hsl_invariant (st:hsl_state) (l:loc) (h0 h1:mem)
//   :Lemma (requires (hsl_invariant st h0                  /\
//                     loc_disjoint l (hsl_footprint st h0) /\
//                     Mods.modifies l h0 h1))
//          (ensures  (hsl_invariant st h1 /\
//                     hsl_footprint st h1 == hsl_footprint st h0))
//   = ()

// (*
//  * Creating of HSL state
//  *)
// let hsl_create (len:uint_32{len > 0ul})
//   :ST hsl_state (requires (fun h0       -> True))
//                 (ensures  (fun h0 st h1 -> Buffer.len (hsl_get_buf st) == len               /\
//                                         hsl_invariant st h1                              /\
//                                         fresh_loc (loc_buffer (hsl_get_buf st)) h0 h1    /\
//                                         fresh_loc (loc_mreference (hsl_get_p0 st)) h0 h1 /\
//                                         fresh_loc (loc_mreference (hsl_get_p1 st)) h0 h1 /\
//                                         fresh_loc (loc_mreference (hsl_get_msgs st)) h0 h1 /\
//                                         sel h1 (hsl_get_p1 st) == 0ul                    /\
//                                         Mods.modifies loc_none h0 h1))
//   = let h0 = ST.get () in
//     let buf = Buffer.gcmalloc root 0ul len in
//     let h00 = ST.get () in
//     let p0 = ralloc root 0ul in
//     let p1 = ralloc root 0ul in
//     let msgs = ralloc root [] in
//     let h2 = ST.get () in
//     let st = Mk_state len buf p0 p1 msgs in
//     st

// (*
//  * Auxiliary function for processing the buffer
//  *
//  * Processes the buffer between p1 and p, one at a time
//  * Returns new p0, and updated list of indices
//  *)
// private let rec aux_process (b:Buffer.buffer uint_32) (p0 p1 p:uint_32) (l:list (uint_32 & uint_32))
//   :ST (uint_32 & list (uint_32 & uint_32))
//       (requires (fun h0 -> Buffer.live h0 b /\
//                         p <= Buffer.len b /\ p1 <= p /\ p0 <= p1 /\
//                         null_terminator_invariant_helper b p0 p1 h0 /\
//                         msgs_list_invariant_helper b l p0 h0))
//       (ensures  (fun h0 (r, l) h1 -> Buffer.live h1 b /\
//                                   r <= p /\
//                                   null_terminator_invariant_helper b r p h1 /\
//                                   msgs_list_invariant_helper b l r h1 /\
//                                   Mods.modifies loc_none h0 h1))
//   = if p = p1 then p0, l  //done
//     else
//       let c = Buffer.index b p1 in
//       if c = 0ul then  //found a 0
//         if p0 = p1 then aux_process b (p1 + 1ul) (p1 + 1ul) p l  //if the subsequence is empty, just go ahead
//         else aux_process b (p1 + 1ul) (p1 + 1ul) p ((p0, p1)::l)  //else add it to the list
//       else aux_process b p0 (p1 + 1ul) p l

// #reset-options "--max_fuel 0 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 16"

// (*
//  * Main process function that client (Record) calls once it has appended some data to the input buffer
//  * It updates the p0 and p1 pointers, so that p1 points to p (the input index)
//  * Also updates the msgs
//  * And maintains the invariant
//  *)
// let hsl_process (st:hsl_state) (p:uint_32)
//   :ST unit (requires (fun h0      -> hsl_invariant st h0 /\  //invariant holds
//                                   p <= hsl_get_len st /\  //the new index upto which client wrote is in bounds
//                                   sel h0 (hsl_get_p1 st) < p))  //p1 < p, i.e. some new data is there
//            (ensures  (fun h0 _ h1 -> hsl_invariant st h1 /\  //invariants holds again
//                                   sel h1 (hsl_get_p1 st) == p /\  //p1 has been updated to p
//                                   Mods.modifies (Mods.loc_union (Mods.loc_mreference (hsl_get_p0 st))
//                                                 (Mods.loc_union (Mods.loc_mreference (hsl_get_msgs st))
//                                                                 (Mods.loc_mreference (hsl_get_p1 st)))) h0 h1))
//   = let new_p0, new_msgs = aux_process st.buf !st.p0 !st.p1 p !st.msgs in
//     st.p0 := new_p0;
//     st.p1 := p;
//     st.msgs := new_msgs

// #set-options "--z3rlimit_factor 2"
// let top_level () : St unit =
//   let st = hsl_create 128ul in
//   let buf = hsl_get_buf st in
//   let rec aux (i:uint_32)
//     : ST unit
//       (requires (fun h ->
//         let p1 = sel h (hsl_get_p1 st) in
//         hsl_get_len st == 128ul /\         //not sure why I need this as a precondition
//         hsl_invariant st h /\
//         p1 <= i /\
//         i <= hsl_get_len st /\
//         (p1 <> i ==> null_terminator_invariant_helper buf (p1 + 1ul) i h)))
//       (ensures fun h0 _ h1 ->
//         hsl_invariant st h1
//       )
//     = let p1 = !st.p1 in
//       if i = hsl_get_len st then ()
//       else if i = 2ul * p1
//       then (buf.(i) <- 0ul;
//             hsl_process st (i + 1ul);
//             aux (i + 1ul))
//       else (buf.(i) <- 1ul;
//             aux (i + 1ul))
//   in
//   aux 0ul
