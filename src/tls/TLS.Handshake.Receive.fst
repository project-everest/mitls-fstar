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
 * A wrapper over TLS.Handshake.ParseFlights that provides a single-buffer oriented interface to
 *   TLS.Handshake.Machine
 *
 * See the Public API section below
 *)

open FStar.Integers
open FStar.HyperStack.ST

module G  = FStar.Ghost
module Bytes = FStar.Bytes
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B  = LowStar.Buffer

module LP = LowParse.Low.Base

module PF = TLS.Handshake.ParseFlights

type byte = FStar.Bytes.byte
type bytes = FStar.Bytes.bytes

/// The state encapsulates PF.state, and a buffer with current from and to indices
///
/// The interface provided by this module is in state-passing style

noeq type state = {
  pf_st    : PF.state;
  rcv_b    : b:B.buffer byte;
  rcv_from : uint_32;
  rcv_to   : i:uint_32{rcv_from <= i /\ i <= B.len rcv_b}
}


/// Invariant that related parsed_bytes in pf_st with rcv_b and its from and to indices

let invariant (st:state) (h:HS.mem) : Type0
= PF.length_parsed_bytes st.pf_st <= (v st.rcv_to - v st.rcv_from) /\
  PF.parsed_bytes st.pf_st ==
    Seq.slice (B.as_seq h st.rcv_b) (v st.rcv_from) (v st.rcv_from + PF.length_parsed_bytes st.pf_st)


/// Framing is simple

let frame_invariant
  (st:state) (l:B.loc) (h0 h1:HS.mem)
: Lemma
  (requires
    invariant st h0 /\
    B.live h0 st.rcv_b /\
    B.(loc_disjoint (loc_buffer st.rcv_b) l) /\
    B.modifies l h0 h1)
  (ensures invariant st h1 /\ B.as_seq h0 st.rcv_b == B.as_seq h1 st.rcv_b)
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

module R = MITLS.Repr
module C = LowStar.ConstBuffer


/// Helper function to create a const_slice from rcv_b

let cslice_of (st:state) : R.const_slice =
  assume (st.rcv_to <= LP.validator_max_length);
  R.MkSlice (C.of_buffer st.rcv_b) st.rcv_to


/// Precondition of the receive functions

unfold
let receive_pre
  (st:state) (in_progress:PF.in_progress_flt_t)
: HS.mem -> Type0
= fun h ->
  B.live h st.rcv_b /\
  invariant st h /\
  PF.(length_parsed_bytes st.pf_st == 0 \/ in_progress_flt st.pf_st == in_progress)

unfold
let only_changes_pf_state (st1 st0:state) : Type0
= st1.rcv_b == st0.rcv_b /\
  st1.rcv_from == st0.rcv_from /\
  st1.rcv_to == st0.rcv_to


/// Postcondition of the receive functions

unfold
let receive_post
  (#flt:Type)
  (st:state)
  (in_progress:PF.in_progress_flt_t)
  (valid:uint_32 -> uint_32 -> flt -> HS.mem -> Type0)
: HS.mem -> TLSError.result (option flt & state) -> HS.mem -> Type0
= fun h0 r h1 ->
  receive_pre st in_progress h0 /\
  B.(modifies loc_none h0 h1) /\
  (let open FStar.Error in
   match r with
   | Error _ -> True
   | Correct (None, rst) ->
     invariant rst h1 /\
     rst `only_changes_pf_state` st /\
     PF.(in_progress_flt rst.pf_st == in_progress)
   | Correct (Some flt, rst) ->
     invariant rst h1 /\
     rst `only_changes_pf_state` st /\
     valid st.rcv_from st.rcv_to flt h1 /\
     PF.(in_progress_flt rst.pf_st == F_none /\
         parsed_bytes rst.pf_st == Seq.empty))

unfold
let receive_post_with_leftover_bytes
  (#flt:Type)
  (st:state)
  (in_progress:PF.in_progress_flt_t)
  (valid:uint_32 -> uint_32 -> flt -> HS.mem -> Type0)
: HS.mem -> TLSError.result (option (flt & uint_32) & state) -> HS.mem -> Type0
= fun h0 r h1 ->
  receive_pre st in_progress h0 /\
  B.(modifies loc_none h0 h1) /\
  (let open FStar.Error in
   match r with
   | Error _ -> True
   | Correct (None, rst) ->
     invariant rst h1 /\
     rst `only_changes_pf_state` st /\
     PF.(in_progress_flt rst.pf_st == in_progress)
   | Correct (Some (flt, idx_end), rst) ->
     invariant rst h1 /\
     idx_end <= st.rcv_to /\
     rst `only_changes_pf_state` st /\
     valid st.rcv_from idx_end flt h1 /\
     PF.(in_progress_flt rst.pf_st == F_none /\
         parsed_bytes rst.pf_st == Seq.empty))

module E = FStar.Error

inline_for_extraction noextract
let wrap_pf_st
  (#a:Type)
  (st:state)
  (r:TLSError.result (option a & PF.state))
: TLSError.result (option a & state)
= match r with
  | E.Error e -> E.Error e
  | E.Correct (None, pf_st) -> E.Correct (None, { st with pf_st = pf_st })
  | E.Correct (Some flt, pf_st) -> E.Correct (Some flt, { st with pf_st = pf_st })


(*** Public API ***)


/// Create a state instance
///
/// A pure function that creates a new instance of PF.state and sets from and to indices to 0
///
/// The returned instance satisfies `invariant st h` for all (h:HS.mem)

let create (b:B.buffer byte)
: state
= { pf_st = PF.create ();
    rcv_b = b;
    rcv_from = 0ul;
    rcv_to = 0ul }


/// Adds input bytes to rcv_b

let buffer_received_fragment
  (st:state) (bs:bytes)
: Stack state
  (requires fun h ->
    B.live h st.rcv_b /\
    invariant st h /\
    v st.rcv_to + Bytes.length bs <= B.length st.rcv_b)  //that adding these bytes does not overflow the buffer
  (ensures fun h0 rst h1 ->
    if Bytes.length bs = 0 then h0 == h1 /\ rst == st
    else
      rst `only_increments_rcv_to` st /\
      rst.rcv_to == st.rcv_to + Bytes.len bs /\
      B.(modifies (loc_buffer (gsub st.rcv_b st.rcv_to (Bytes.len bs)))) h0 h1 /\
      Seq.slice (B.as_seq h1 rst.rcv_b) (v st.rcv_to) (v rst.rcv_to) == Bytes.reveal bs /\
      invariant rst h1)
= if Bytes.length bs = 0 then st
  else
    let h0 = ST.get () in
    let sub = B.sub st.rcv_b st.rcv_to (Bytes.len bs) in
    FStar.Bytes.store_bytes bs sub;
    let h1 = ST.get () in
    let rst = { st with rcv_to = st.rcv_to + Bytes.len bs } in

    assert (Seq.equal (B.as_seq h1 (B.gsub rst.rcv_b rst.rcv_from (st.rcv_to - rst.rcv_from)))
                      (Seq.slice (B.as_seq h1 rst.rcv_b) (v rst.rcv_from) (v st.rcv_to)));
    lemma_seq
      (B.as_seq h0 st.rcv_b)
      (B.as_seq h1 rst.rcv_b)
      (v st.rcv_from)
      (v st.rcv_to)
      (v st.rcv_from + PF.length_parsed_bytes st.pf_st);
    rst

/// Receive flights functions

(*** ClientHello and ServerHello flights ***)


let receive_s_Idle (st:state)
: ST (TLSError.result (option (PF.s_Idle (cslice_of st)) & state))
  (requires receive_pre st PF.F_s_Idle)
  (ensures receive_post st PF.F_s_Idle PF.valid_s_Idle)
= let r = PF.receive_s_Idle st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r

let receive_c_wait_ServerHello (st:state)
: ST (TLSError.result (option (PF.c_wait_ServerHello (cslice_of st) & uint_32) & state))
  (requires receive_pre st PF.F_c_wait_ServerHello)
  (ensures receive_post_with_leftover_bytes st PF.F_c_wait_ServerHello PF.valid_c_wait_ServerHello)
= let r = PF.receive_c_wait_ServerHello st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r


(*** 1.3 flights ***)


let receive_c13_wait_Finished1 (st:state)
: ST (TLSError.result (option (PF.c13_wait_Finished1 (cslice_of st)) & state))
  (requires receive_pre st PF.F_c13_wait_Finished1)
  (ensures receive_post st PF.F_c13_wait_Finished1 PF.valid_c13_wait_Finished1)
= let r = PF.receive_c13_wait_Finished1 st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r

let receive_s13_wait_Finished2 (st:state)
: ST (TLSError.result (option (PF.s13_wait_Finished2 (cslice_of st)) & state))
  (requires receive_pre st PF.F_s13_wait_Finished2)
  (ensures  receive_post st PF.F_s13_wait_Finished2 PF.valid_s13_wait_Finished2)
= let r = PF.receive_s13_wait_Finished2 st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r

let receive_s13_wait_EOED (st:state)
: ST (TLSError.result (option (PF.s13_wait_EOED (cslice_of st)) & state))
  (requires receive_pre st PF. F_s13_wait_EOED)
  (ensures  receive_post st PF.F_s13_wait_EOED PF.valid_s13_wait_EOED)
= let r = PF.receive_s13_wait_EOED st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r

let receive_c13_Complete (st:state)
: ST (TLSError.result (option (PF.c13_Complete (cslice_of st)) & state))
  (requires receive_pre st PF.F_c13_Complete)
  (ensures  receive_post st PF.F_c13_Complete PF.valid_c13_Complete)
= let r = PF.receive_c13_Complete st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r


(*** 1.2 flights ***)

let receive_c12_wait_ServerHelloDone (st:state)
: ST (TLSError.result (option (PF.c12_wait_ServerHelloDone (cslice_of st)) & state))
  (requires receive_pre st PF.F_c12_wait_ServerHelloDone)
  (ensures  receive_post st PF.F_c12_wait_ServerHelloDone PF.valid_c12_wait_ServerHelloDone)
= let r = PF.receive_c12_wait_ServerHelloDone st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r

let receive_cs12_wait_Finished (st:state)
: ST (TLSError.result (option (PF.cs12_wait_Finished (cslice_of st)) & state))
  (requires receive_pre st PF.F_cs12_wait_Finished)
  (ensures  receive_post st PF.F_cs12_wait_Finished PF.valid_cs12_wait_Finished)
= let r = PF.receive_cs12_wait_Finished st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r

let receive_c12_wait_NST (st:state)
: ST (TLSError.result (option (PF.c12_wait_NST (cslice_of st)) & state))
  (requires receive_pre st PF.F_c12_wait_NST)
  (ensures  receive_post st PF.F_c12_wait_NST PF.valid_c12_wait_NST)
= let r = PF.receive_c12_wait_NST st.pf_st (cslice_of st) st.rcv_from st.rcv_to in
  wrap_pf_st st r

let receive_s12_wait_CCS1 (st:state)
: ST (TLSError.result (option (PF.s12_wait_CCS1 (cslice_of st)) & state))
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
  | InError: TLSError.error -> incoming // how underspecified should it be?

let in_next_keys (r:incoming) = InAck? r && InAck?.next_keys r
let in_complete (r:incoming)  = InAck? r && InAck?.complete r



(*** Test ***)


assume val bs : bs:bytes{Bytes.length bs > 0}

noextract
let test (b:B.buffer byte)
: ST unit
  (requires fun h -> B.live h b)
  (ensures fun _ _ _ -> True)
= let open FStar.Error in

  //create state
  let st = create b in

  //at this point st.rcv_from and st.rcv_to are both 0, so append some bytes
  assume (v st.rcv_to + Bytes.length bs <= B.length st.rcv_b);
  let st = buffer_received_fragment st bs in

  //try to receive ServerHello
  let r = receive_c_wait_ServerHello st in
  match r with
  | Error e -> ()  //abandon
  | Correct (None, st) ->
    //we need more data in ther buffer before the flight can be parsed
    assume (v st.rcv_to + Bytes.length bs <= B.length st.rcv_b);
    let st = buffer_received_fragment st bs in

    //if we tried to parse some other flight, it won't verify, the following call fails
    //let r = receive_c12_wait_NST st in

    //but we can try parsing ServerHello again
    let r = receive_c_wait_ServerHello st in

    ()
  | Correct (Some (flt, idx_end), st) ->
    //now we can parse ServerHelloDone
    let st = { st with rcv_from = idx_end } in

    let r = receive_c12_wait_ServerHelloDone st in
    ()
