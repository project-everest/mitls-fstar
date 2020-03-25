(*
  Copyright 2015--2019 INRIA and Microsoft Corporation

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.

  Authors: A. Rastogi
*)

module TLS.Handshake.Receive

(*
 * A wrapper over TLS.Handshake.ParseFlights that provides a single-slice oriented interface to
 *   TLS.Handshake.Machine,
 * As opposed to the interface of TLS.Handshake.ParseFlights that takes the input buffer as argument for every call
 *
 * This is a quite light wrapper with no abstraction
 * 
 * See the Public API section below, and a test function at the end
 *)

open FStar.Integers
open FStar.HyperStack.ST

open TLS.Result

module G  = FStar.Ghost
module Bytes = FStar.Bytes
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B  = LowStar.Buffer

module LP = LowParse.Low.Base

module PF = TLS.Handshake.ParseFlights

module R = LowParse.Repr
module C = LowStar.ConstBuffer


#set-options "--max_fuel 0 --max_ifuel 1"

type byte = FStar.Bytes.byte
type bytes = FStar.Bytes.bytes

/// The state encapsulates PF.state, and a slice with current from and to indices
///
/// The interface provided by this module is in state-passing style

let slice_t = b:LP.slice (B.trivial_preorder byte) (B.trivial_preorder byte){
  b.LP.len <= LP.validator_max_length
}

noeq type state = {
  pf_st    : PF.state; // updated by parseFlight
  rcv_b    : slice_t;  // provided by the application; should be a const slice
  rcv_from : uint_32;  // TODO: incremented after parsing a flight.
  rcv_to   : i:uint_32{rcv_from <= i /\ i <= rcv_b.LP.len} // incremented as we buffer incoming bytes. Could disappear from low-level API.
}

// proposed v1 API: keep pf_st within the machine; keep rcv_to only in HL wrapper; 

let in_progress (s:state) = PF.in_progress_flt s.pf_st


/// Invariant that relates parsed_bytes in pf_st with rcv_b and its from and to indices

let invariant (st:state) (h:HS.mem) : Type0
= LP.live_slice h st.rcv_b /\
  PF.length_parsed_bytes st.pf_st <= (v st.rcv_to - v st.rcv_from) /\
  PF.parsed_bytes st.pf_st ==
    Seq.slice (B.as_seq h st.rcv_b.LP.base) (v st.rcv_from) (v st.rcv_from + PF.length_parsed_bytes st.pf_st)


/// Framing is trivial

let loc_recv st = B.loc_buffer st.rcv_b.LP.base


let frame_invariant
  (st:state) (l:B.loc) (h0 h1:HS.mem)
: Lemma
  (requires
    invariant st h0 /\
    B.(loc_disjoint (loc_recv st) l) /\
    B.modifies l h0 h1)
  (ensures invariant st h1 /\ B.as_seq h0 st.rcv_b.LP.base == B.as_seq h1 st.rcv_b.LP.base)
= ()

unfold
let only_increments_rcv_to (st1 st0:state)
= st1.pf_st == st0.pf_st /\
  st1.rcv_b == st0.rcv_b /\
  st1.rcv_from == st0.rcv_from /\
  st0.rcv_to <= st1.rcv_to

private let lemma_seq (#a:Type) (s1 s2:Seq.seq a) (from to:nat) (to':nat)
: Lemma
  (requires
    Seq.length s1 == Seq.length s2 /\
    from <= to /\ to <= Seq.length s1 /\
    from <= to' /\ to' <= to /\
    Seq.equal (Seq.slice s1 from to) (Seq.slice s2 from to))
  (ensures Seq.equal (Seq.slice s1 from to') (Seq.slice s2 from to'))
= assert (forall (i:nat). i < to - from ==> Seq.index (Seq.slice s1 from to) i == Seq.index (Seq.slice s2 from to) i)


/// Helper function to create a const_slice from rcv_b

unfold let cslice_of (st:state) : R.const_slice = R.of_slice st.rcv_b

/// Precondition of the receive functions

unfold
let receive_pre
  (st:state) (inflight:PF.in_progress_flt_t)
: HS.mem -> Type0
= fun h ->
  invariant st h /\
  PF.(length_parsed_bytes st.pf_st == 0 \/ in_progress st == inflight)

unfold
let only_changes_pf_state (st1 st0:state) : Type0
= st1.rcv_b == st0.rcv_b /\
  st1.rcv_from == st0.rcv_from /\
  st1.rcv_to == st0.rcv_to

unfold
let changes_pf_state_and_updates_rcv_from (st1 st0:state) (pos:uint_32{pos <= st0.rcv_to}) : Type0
= st1.rcv_b == st0.rcv_b /\
  st1.rcv_from == pos /\
  st1.rcv_to == st0.rcv_to


/// Postcondition of the receive functions

unfold
let receive_post
  (#flt:Type)
  (st:state)
  (inflight:PF.in_progress_flt_t)
  (valid:uint_32 -> uint_32 -> flt -> HS.mem -> Type0)
: HS.mem -> result (option flt & state) -> HS.mem -> Type0
= fun h0 r h1 ->
  receive_pre st inflight h0 /\
  B.(modifies loc_none h0 h1) /\
  (match r with
   | Error _ -> True
   | Correct (None, rst) ->
     invariant rst h1 /\
     rst `only_changes_pf_state` st /\
     in_progress rst == inflight
   | Correct (Some flt, rst) ->
     invariant rst h1 /\
     changes_pf_state_and_updates_rcv_from rst st st.rcv_to /\
     valid st.rcv_from st.rcv_to flt h1 /\
     in_progress rst == PF.F_none /\
     PF.parsed_bytes rst.pf_st == Seq.empty)

unfold
let receive_post_with_leftover_bytes
  (#flt:Type)
  (st:state)
  (inflight:PF.in_progress_flt_t)
  (valid:uint_32 -> uint_32 -> flt -> HS.mem -> Type0)
: HS.mem -> result (option flt & state) -> HS.mem -> Type0
= fun h0 r h1 ->
  receive_pre st inflight h0 /\
  B.(modifies loc_none h0 h1) /\
  (match r with
   | Error _ -> True
   | Correct (None, rst) ->
     invariant rst h1 /\
     rst `only_changes_pf_state` st /\
     in_progress rst == inflight
   | Correct (Some flt, rst) ->
     invariant rst h1 /\
     rst.rcv_from <= st.rcv_to /\
     changes_pf_state_and_updates_rcv_from rst st rst.rcv_from /\
     valid st.rcv_from rst.rcv_from flt h1 /\
     in_progress rst == PF.F_none /\
     PF.parsed_bytes rst.pf_st == Seq.empty)

inline_for_extraction noextract
let wrap_pf_st
  (#a:Type)
  (st:state)
  (r:result (option a & PF.state))
: result (option a & state)
= match r with
  | Error e -> Error e
  | Correct (None, pf_st) -> Correct (None, { st with pf_st = pf_st })
  | Correct (Some flt, pf_st) -> Correct (Some flt, { st with pf_st = pf_st; rcv_from = st.rcv_to })

(*** Public API ***)


/// Create an input buffer (until we figure out if the application allocates it)

let alloc_slice (region: Mem.rgn):  ST slice_t 
  (requires fun h0 -> True)
  (ensures fun h0 b h1 -> 
    // TODO track freshness and region
    LP.live_slice h1 b)
=
  let receiving_buffer = LowStar.Buffer.malloc region 0uy 12000ul in
  LowParse.Slice.make_slice receiving_buffer 12000ul
  
/// Create a state instance

let create (b:slice_t)
: Stack state
  (requires fun h -> LP.live_slice h b)
  (ensures fun h0 r h1 ->
    h0 == h1 /\
    r.pf_st == PF.create () /\
    r.rcv_b == b /\
    r.rcv_from == 0ul /\
    r.rcv_to == 0ul /\
    invariant r h1)
= { pf_st = PF.create ();
    rcv_b = b;
    rcv_from = 0ul;
    rcv_to = 0ul }


/// Adds input bytes to rcv_b

let buffer_received_fragment
  (st:state) (bs:bytes)
: Stack (option state)
  (requires fun h -> invariant st h)
  (ensures fun h0 rst h1 ->
    if Bytes.length bs = 0
    then h0 == h1 /\ rst == Some st
    else if Bytes.length bs > v st.rcv_b.LP.len - v st.rcv_to
    then h0 == h1 /\ rst == None
    else
      Some? rst /\
      (let rst = Some?.v rst in
       rst `only_increments_rcv_to` st /\
       rst.rcv_to == st.rcv_to + Bytes.len bs /\
       B.(modifies (loc_buffer (gsub st.rcv_b.LP.base st.rcv_to (Bytes.len bs)))) h0 h1 /\
       Seq.slice (B.as_seq h1 rst.rcv_b.LP.base) (v st.rcv_to) (v rst.rcv_to) == Bytes.reveal bs /\
       invariant rst h1))
= if Bytes.length bs = 0 then Some st
  else if Bytes.len bs > st.rcv_b.LP.len - st.rcv_to then None
  else
    let h0 = ST.get () in
    let sub = B.sub st.rcv_b.LP.base st.rcv_to (Bytes.len bs) in
    FStar.Bytes.store_bytes bs sub;
    let h1 = ST.get () in
    let rst = { st with rcv_to = st.rcv_to + Bytes.len bs } in

    assert (Seq.equal (B.as_seq h1 (B.gsub rst.rcv_b.LP.base rst.rcv_from (st.rcv_to - rst.rcv_from)))
                      (Seq.slice (B.as_seq h1 rst.rcv_b.LP.base) (v rst.rcv_from) (v st.rcv_to)));
    lemma_seq
      (B.as_seq h0 st.rcv_b.LP.base)
      (B.as_seq h1 rst.rcv_b.LP.base)
      (v st.rcv_from)
      (v st.rcv_to)
      (v st.rcv_from + PF.length_parsed_bytes st.pf_st);
    Some rst


/// Receive flights functions

(*** ClientHello and ServerHello flights ***)


let receive_s_Idle (st:state)
: ST (result (option (PF.s_Idle (cslice_of st)) & state))
  (requires receive_pre st PF.F_s_Idle)
  (ensures receive_post st PF.F_s_Idle PF.valid_s_Idle)
= let r = PF.receive_s_Idle st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r

let receive_c_wait_ServerHello (st:state)
: ST (result (option (PF.c_wait_ServerHello (cslice_of st)) & state))
  (requires receive_pre st PF.F_c_wait_ServerHello)
  (ensures receive_post_with_leftover_bytes st PF.F_c_wait_ServerHello PF.valid_c_wait_ServerHello)
= let r = PF.receive_c_wait_ServerHello st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  match r with
  | Error e -> Error e
  | Correct (None, pf_st) -> Correct (None, { st with pf_st = pf_st })
  | Correct (Some (flt, pos), pf_st) ->
    Correct (Some flt, { st with pf_st = pf_st; rcv_from = pos })


(*** 1.3 flights ***)


let receive_c13_wait_Finished1 (st:state)
: ST (result (option (PF.c13_wait_Finished1 (cslice_of st)) & state))
  (requires receive_pre st PF.F_c13_wait_Finished1)
  (ensures receive_post st PF.F_c13_wait_Finished1 PF.valid_c13_wait_Finished1)
= let r = PF.receive_c13_wait_Finished1 st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r

let receive_s13_wait_Finished2 (st:state)
: ST (result (option (PF.s13_wait_Finished2 (cslice_of st)) & state))
  (requires receive_pre st PF.F_s13_wait_Finished2)
  (ensures  receive_post st PF.F_s13_wait_Finished2 PF.valid_s13_wait_Finished2)
= let r = PF.receive_s13_wait_Finished2 st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r

let receive_s13_wait_EOED (st:state)
: ST (result (option (PF.s13_wait_EOED (cslice_of st)) & state))
  (requires receive_pre st PF. F_s13_wait_EOED)
  (ensures  receive_post st PF.F_s13_wait_EOED PF.valid_s13_wait_EOED)
= let r = PF.receive_s13_wait_EOED st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r

let receive_c13_Complete (st:state)
: ST (result (option (PF.c13_Complete (cslice_of st)) & state))
  (requires receive_pre st PF.F_c13_Complete)
  (ensures  receive_post_with_leftover_bytes st PF.F_c13_Complete PF.valid_c13_Complete)
= let r = PF.receive_c13_Complete st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  match r with
  | Error e -> Error e
  | Correct (None, pf_st) -> Correct (None, { st with pf_st = pf_st })
  | Correct (Some (flt, pos), pf_st) ->
    Correct (Some flt, { st with pf_st = pf_st; rcv_from = pos })


(*** 1.2 flights ***)

let receive_c12_wait_ServerHelloDone (st:state)
: ST (result (option (PF.c12_wait_ServerHelloDone (cslice_of st)) & state))
  (requires receive_pre st PF.F_c12_wait_ServerHelloDone)
  (ensures  receive_post st PF.F_c12_wait_ServerHelloDone PF.valid_c12_wait_ServerHelloDone)
= let r = PF.receive_c12_wait_ServerHelloDone st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r

let receive_cs12_wait_Finished (st:state)
: ST (result (option (PF.cs12_wait_Finished (cslice_of st)) & state))
  (requires receive_pre st PF.F_cs12_wait_Finished)
  (ensures  receive_post st PF.F_cs12_wait_Finished PF.valid_cs12_wait_Finished)
= let r = PF.receive_cs12_wait_Finished st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r

let receive_c12_wait_NST (st:state)
: ST (result (option (PF.c12_wait_NST (cslice_of st)) & state))
  (requires receive_pre st PF.F_c12_wait_NST)
  (ensures  receive_post st PF.F_c12_wait_NST PF.valid_c12_wait_NST)
= let r = PF.receive_c12_wait_NST st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r

let receive_s12_wait_CCS1 (st:state)
: ST (result (option (PF.s12_wait_CCS1 (cslice_of st)) & state))
  (requires receive_pre st PF.F_s12_wait_CCS1)
  (ensures  receive_post st PF.F_s12_wait_CCS1 PF.valid_s12_wait_CCS1)
= let r = PF.receive_s12_wait_CCS1 st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r



/// unchanged from our stable Handshake API.

type incoming =
  | InAck: // the fragment is accepted, and...
      next_keys : bool -> // the reader index increases;
      complete  : bool -> // the handshake is complete!
      incoming
  | InQuery: Cert.chain -> bool -> incoming // could be part of InAck if no explicit user auth
  | InError: error -> incoming // how underspecified should it be?

let in_error ad txt = InError ({alert=ad; cause=txt})

let in_next_keys (r:incoming) = InAck? r && InAck?.next_keys r
let in_complete (r:incoming)  = InAck? r && InAck?.complete r

(*
// v1 API. 
// We'll still return signals, but we'll write the generated keys in small application-provided buffers. 
// InQuery is deprecated, as we now rely on callbacks.

// A struct including anything returned by the handshake API, except for the 
type out_ctx = {
  // how many bytes were consumed from the input buffer; 
  // can it also encode a parsing error position?
  out_consumed: UInt32.t; 

  // how many bytes were written to the output buffer
  out_written: UInt32.t;

  // signals, to be unified 
  // out_outgoing_send_first, ugly, not used anymore? 
  out_send_next_keys: option TLS.Handshake.Send.next_key_use;
  out_receive_next_keys: bool; 
  out_complete: bool;
}
type incoming0 = result out_ctx
*)


(*** Test ***)


assume val bs : bs:bytes{Bytes.length bs > 0}

noextract
let test (b:slice_t)
: ST unit
  (requires fun h -> B.live h b.LP.base)
  (ensures fun _ _ _ -> True)
= 
  //create state
  let st = create b in

  //at this point st.rcv_from and st.rcv_to are both 0, so append some bytes
  let st = buffer_received_fragment st bs in
  match st with
  | None -> ()  //buffer overflowed
  | Some st ->
    //try to receive ServerHello
    let r = receive_c_wait_ServerHello st in
    match r with
    | Error e -> ()  //abandon, some parsing error
    | Correct (None, st) ->
      //we need more data in ther buffer before the flight can be parsed
      let st = buffer_received_fragment st bs in
      (match st with
       | None -> ()  //buffer overflowed
       | Some st ->
         //if we tried to parse some other flight, it won't verify, the following call fails
         //let r = receive_c12_wait_NST st in

         //but we can try parsing ServerHello again
         let r = receive_c_wait_ServerHello st in

         //and so on ...

         ())
    | Correct (Some flt, st) ->

      let r = receive_c12_wait_ServerHelloDone st in

      //and so on ...
      ()

