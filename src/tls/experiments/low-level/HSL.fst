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
module LM = LowStar.Modifies

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
abstract
noeq
type message (len:uint32)= {
  from:(x:uint32{x <= len});
  to: (x:uint32{from <= x /\ x <= len});
  msg: M.msg
}

[@unifier_hint_injective]
unfold
let reference (t:Type) = reference t

let lbuffer8 (l:uint32) = buf:buffer8{B.len buf == l}

abstract 
noeq
type hsl_state =
  | Mk_state: len:uint32 ->
              buf:lbuffer8 len ->
              p0:reference uint32 ->
              p1:reference (x:uint32{x <= len}) ->
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
  : GTot (x:uint32{x <= hsl_get_len st})
  = HS.sel h st.p1
  
abstract 
let hsl_get_msgs (st:hsl_state) (h:HS.mem)
  : GTot (list (message (hsl_get_len st))) 
  = G.reveal (HS.sel h st.msgs)

let liveness (st:hsl_state) (h:HS.mem) =
  B.live h (hsl_get_buf st)

let message_is_parsed 
       (#len:uint32)
       (m:message len) 
       (b:lbuffer8 len)
       (h:HS.mem)
   : prop 
   =  let delta = m.to - m.from in
      let sub = B.gsub b m.from delta in
      match LP.parse M.msg_parser (B.as_seq h sub) with
      | None -> False
      | Some (msg, consumed) ->
         msg == m.msg /\
         consumed == v delta (* unsure about the latter part *)

abstract
let msgs_inv (st:hsl_state) (h:HS.mem) =
  let msgs = hsl_get_msgs st h in
  let p0 = HS.sel h st.p0 in
  let p1 = hsl_get_p1 st h in
  p0 <= p1 /\
  (forall (m:message st.len). {:pattern List.Tot.memP m msgs}
        List.Tot.memP m msgs ==>
        m.to <= p0  /\
        message_is_parsed m st.buf h)

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

(*
 * From the st_inv, clients can only conclude liveness of the internal buffer
 *)
let st_inv_elim (st:hsl_state) (h:HS.mem)
  :Lemma (requires (st_inv st h))
         (ensures  (B.live h (hsl_get_buf st)))
         [SMTPat (st_inv st h)]
  = ()

(*
 * HSL footprint = p0, p1, buffer contents between 0 and p1, and msgs
 * This is not abstract, so that the client (Record) can append the buffer after p1, and use the framing lemma
 *)
abstract
let fp (st:hsl_state) =
   let open B in
   loc_union (loc_mreference st.p0)
             (loc_union (loc_mreference st.p1)
                        (loc_mreference st.msgs))

let footprint (st:hsl_state) (h:HS.mem) =
  let open B in
  loc_union (fp st) 
            (loc_buffer (B.gsub (hsl_get_buf st) 
                                 0ul
                                 (hsl_get_p1 st h)))


(*
 * Framing the HSL invariant across its footprint
 *)
let frame_st_inv (st:hsl_state) (l:loc) (h0 h1:HS.mem)
  : Lemma 
      (requires 
         st_inv st h0 /\
         B.loc_disjoint l (footprint st h0) /\
         LM.modifies l h0 h1)
      (ensures 
         st_inv st h1 /\
         footprint st h1 == footprint st h0)
  = //the pattern in msgs_inv include is w.r.t the old state
    //assert this equality to unify the two messages in the E-matching graph
    assert (hsl_get_msgs st h0 == hsl_get_msgs st h1)

(*
 * `create`: Client provides a buffer to HSL
 * 
 *)
let create (len:uint_32{len > 0ul}) (b:lbuffer8 len)
  : ST hsl_state 
       (requires fun h0 -> 
          B.live h0 b)
       (ensures fun h0 st h1 ->
          hsl_get_len st == len /\
          st_inv st h1 /\
          B.fresh_loc (fp st) h0 h1 /\
          hsl_get_p1 st h1 == 0ul /\
          hsl_get_msgs st h1 == [] /\
          LM.modifies B.loc_none h0 h1)
  = let p0 = ralloc HS.root 0ul in
    let p1 = ralloc HS.root 0ul in
    let msgs = ralloc HS.root (Ghost.hide []) in
    Mk_state len b p0 p1 msgs

(* MOVE TO LIST LIBRARY *)
let extends (l1 l2:list 'a)  = exists l3. l1 == l2 @ l3

let rec append_memP (#t:Type) (l1 l2:list t) (a:t)
  : Lemma (List.Tot.memP a (l1@l2) <==> (List.Tot.memP a l1 \/ List.Tot.memP a l2))
  = match l1 with
    | [] -> ()
    | hd::tl -> append_memP tl l2 a

let extends_mem (l1 l2:list 'a)
  : Lemma (requires l1 `extends` l2)
          (ensures  forall m. List.Tot.memP m l2 ==> List.Tot.memP m l1)
  = FStar.Classical.exists_elim 
       (forall m. List.Tot.memP m l2 ==> List.Tot.memP m l1) ()
       (fun (l3:list 'a{l1 == l2@l3}) ->
           FStar.Classical.forall_intro (append_memP l2 l3))

let extends_refl (l:list 'a) : Lemma (l `extends` l) = admit()
let extends_snoc (l:list 'a) (x:'a) : Lemma (List.Tot.snoc (l, x) `extends` l) = admit()
let invert_memP_snoc (l:list 'a) (x:'a) 
  : Lemma (FStar.List.Tot.(forall m.{:pattern (memP m (snoc (l, x)))} memP m (snoc (l, x)) <==> memP m l \/ m == x))
  = admit()

let parse_it (#len:uint32) 
             (from:uint32)
             (to:uint32{from <= to /\ to <= len})
             (b:lbuffer8 len)
  : ST (option (G.erased (message len) & uint32))
       (requires fun h ->
         B.live h b)
       (ensures fun h0 eopt h1 ->
         let eopt' = LP.parse M.msg_parser (B.as_seq h0 b) in
         LM.modifies B.loc_none h0 h1 /\ 
         (match eopt, eopt' with
         | None, None -> True
         | Some (m, n), Some (m', n') -> 
            v from + n' <= v to /\
            n == u (v from + n') /\
            m == G.hide ({from=from; to=n; msg=m'}) /\
            message_is_parsed #len (G.reveal m) b h1 // /\
            // (G.reveal m).to == n
         | _ -> False))
  = admit()         

(* TODO: Move to Ghost library *)
let bind (x:G.erased 'a) (g:'a -> G.erased 'b) : G.erased 'b =
  let x = G.reveal x in
  g x
  
let ghost_snoc (x:G.erased (list 'a)) (y:G.erased 'a)
  : G.erased (list 'a)
  = yy <-- y;
    xx <-- x;
    G.hide (List.Tot.snoc (xx, yy))
    
#set-options "--max_fuel 0 --max_ifuel 0"
let extend_st_inv_snoc (st:hsl_state) (h0 h1:HS.mem) (x:message st.len)
  : Lemma 
      (requires 
         st_inv st h0 /\
         LM.modifies (fp st) h0 h1 /\
         HS.sel h0 st.p0 <= HS.sel h1 st.p0 /\
         HS.sel h1 st.p0 <= hsl_get_p1 st h1 /\
         hsl_get_p1 st h0 <= hsl_get_p1 st h1 /\
         (let msgs1 = hsl_get_msgs st h1 in
          let msgs0 = hsl_get_msgs st h0 in
          let p0 = HS.sel h1 st.p0 in
          msgs1 == List.Tot.snoc (msgs0, x) /\
          x.to <= p0 /\
          message_is_parsed x st.buf h1))
      (ensures 
         st_inv st h1)
  = 
    let msgs1 = hsl_get_msgs st h1 in
    let msgs0 = hsl_get_msgs st h0 in
    let p0 = HS.sel h1 st.p0 in
    invert_memP_snoc msgs0 x      

#set-options "--z3rlimit_factor 3 --initial_ifuel 1 --max_ifuel 1"
(*
 * Main process function that client (Record) calls once it has appended some data to the input buffer
 * It updates the p0 and p1 pointers, so that p1 points to p (the input index)
 * Also updates the msgs
 * And maintains the invariant
 *)
let process (st:hsl_state) (p:uint32)
  : ST unit 
       (requires fun h0 ->
         st_inv st h0 /\  //invariant holds
         hsl_get_p1 st h0 <= p /\ //p1 < p, i.e. some new data is there
         p <= hsl_get_len st)  //the new index upto which client wrote is in bounds
       (ensures fun h0 _ h1 ->
         st_inv st h1 /\  //invariants holds again
         hsl_get_p1 st h1 == p /\
         LM.modifies (fp st) h0 h1 /\
         hsl_get_msgs st h1 `extends` hsl_get_msgs st h0)
  = let h0 = ST.get() in 
    let msgs = !st.msgs in
    st.p1 := p;
    let p0 = !st.p0 in
    match parse_it #st.len p0 p st.buf with
    | None -> 
      let h1 = ST.get() in
      assert (hsl_get_msgs st h1 == hsl_get_msgs st h0);
      extends_refl (G.reveal msgs)
    | Some (last, n) -> 
      extends_snoc (G.reveal msgs) (G.reveal last);
      st.msgs := ghost_snoc (!st.msgs) last;
      st.p0 := n;
      let h1 = ST.get() in
      extend_st_inv_snoc st h0 h1 (G.reveal last)


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
