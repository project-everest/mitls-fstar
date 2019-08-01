module TLS.Handshake.Receive.Wrapper

open FStar.Integers
open FStar.HyperStack.ST

module G  = FStar.Ghost
module Bytes = FStar.Bytes
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B  = LowStar.Buffer

module LP = LowParse.Low.Base

module Rcv = TLS.Handshake.Receive


// unchanged from our stable Handshake API.

type incoming =
  | InAck: // the fragment is accepted, and...
      next_keys : bool -> // the reader index increases;
      complete  : bool -> // the handshake is complete!
      incoming
  | InQuery: Cert.chain -> bool -> incoming // could be part of InAck if no explicit user auth
  | InError: TLSError.error -> incoming // how underspecified should it be?

let in_next_keys (r:incoming) = InAck? r && InAck?.next_keys r
let in_complete (r:incoming)  = InAck? r && InAck?.complete r




(*
 * A wrapper over HSL.receive as expected by the current TLS.Handshake.Machine
 *)

type byte = FStar.Bytes.byte
type bytes = FStar.Bytes.bytes

noeq type rcv_state = {
  current_flt : G.erased Rcv.in_progress_flt_t; // not needed? 
  hsl_rcv_st  : Rcv.hsl_state;
  rcv_b       : b:B.buffer byte{B.loc_disjoint (B.loc_buffer b) (Rcv.footprint hsl_rcv_st)};
  rcv_from    : uint_32;
  rcv_to      : i:uint_32{rcv_from <= i /\ i <= B.len rcv_b}
}

/// In case of partially parsed flights, the prefix [rcv_from, Rcv.length_parsed_bytes]
///   is what HSL.Receive maintains

let rcv_reset_inv (st:rcv_state) (h:HS.mem) : Type0 =
  B.live h st.rcv_b /\
  Rcv.invariant st.hsl_rcv_st h /\
  Rcv.parsed_bytes st.hsl_rcv_st h == Seq.empty /\
  Rcv.in_progress_flt st.hsl_rcv_st h == Rcv.F_none

let rcv_in_progress_inv (st:rcv_state) (h:HS.mem) : Type0 =
  B.live h st.rcv_b /\
  Rcv.invariant st.hsl_rcv_st h /\
  Rcv.length_parsed_bytes st.hsl_rcv_st h <= (v st.rcv_to - v st.rcv_from) /\
  Rcv.parsed_bytes st.hsl_rcv_st h ==
    Seq.slice (B.as_seq h st.rcv_b) (v st.rcv_from) (v st.rcv_from + Rcv.length_parsed_bytes st.hsl_rcv_st h) /\
  Rcv.in_progress_flt st.hsl_rcv_st h == G.reveal st.current_flt

let invariant (st:rcv_state) (h:HS.mem) =
  rcv_reset_inv st h \/ rcv_in_progress_inv st h

let frame_rcv_reset_inv
  (st:rcv_state) (l:B.loc) (h0 h1:HS.mem)
  : Lemma
    (requires
      rcv_reset_inv st h0 /\
      B.(loc_disjoint (loc_union (Rcv.footprint st.hsl_rcv_st) (loc_buffer st.rcv_b)) l /\
      B.modifies l h0 h1))
    (ensures rcv_reset_inv st h1 /\ B.as_seq h0 st.rcv_b == B.as_seq h1 st.rcv_b)
  = Rcv.frame_hsl_state st.hsl_rcv_st h0 h1 l

let frame_rcv_in_progress_inv
  (st:rcv_state) (l:B.loc) (h0 h1:HS.mem)
  : Lemma
    (requires
      rcv_in_progress_inv st h0 /\
      B.(loc_disjoint (loc_union (Rcv.footprint st.hsl_rcv_st) (loc_buffer st.rcv_b)) l /\
      B.modifies l h0 h1))
    (ensures rcv_in_progress_inv st h1 /\ B.as_seq h0 st.rcv_b == B.as_seq h1 st.rcv_b)
  = Rcv.frame_hsl_state st.hsl_rcv_st h0 h1 l

let create
  (hsl_rcv_st:Rcv.hsl_state) (b:B.buffer byte)
  : ST rcv_state
    (requires fun h ->
      B.live h b /\
      B.(loc_disjoint (loc_buffer b) (Rcv.footprint hsl_rcv_st)) /\
      Rcv.invariant hsl_rcv_st h /\
      Rcv.in_progress_flt hsl_rcv_st h == Rcv.F_none /\
      Rcv.parsed_bytes hsl_rcv_st h == Seq.empty)
    (ensures fun h0 st h1 ->
      h0 == h1 /\
      rcv_reset_inv st h1 /\
      st == {
        current_flt = G.hide Rcv.F_none;
        hsl_rcv_st = hsl_rcv_st;
        rcv_b = b;
        rcv_from = 0ul;
        rcv_to = 0ul
      })
  = {current_flt = G.hide Rcv.F_none;
     hsl_rcv_st = hsl_rcv_st;
     rcv_b = b;
     rcv_from = 0ul;
     rcv_to = 0ul}

unfold let only_increments_rcv_to (st1 st0:rcv_state) =
  st1.current_flt == st0.current_flt /\
  st1.hsl_rcv_st == st0.hsl_rcv_st /\
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

let buffer_received_fragment
  (st:rcv_state) (bs:bytes)
  : Stack rcv_state
    (requires fun h ->
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
      Rcv.frame_hsl_state st.hsl_rcv_st h0 h1 (B.loc_buffer sub);
      let rst = { st with rcv_to = st.rcv_to + Bytes.len bs } in

      assert (Seq.equal (B.as_seq h1 (B.gsub rst.rcv_b rst.rcv_from (st.rcv_to - rst.rcv_from)))
                       (Seq.slice (B.as_seq h1 rst.rcv_b) (v rst.rcv_from) (v st.rcv_to)));
      lemma_seq
        (B.as_seq h0 st.rcv_b)
        (B.as_seq h1 rst.rcv_b)
        (v st.rcv_from)
        (v st.rcv_to)
        (v st.rcv_from + Rcv.length_parsed_bytes st.hsl_rcv_st h0);
      rst


module HSM = Parsers.Handshake
module R = MITLS.Repr
module C = LowStar.ConstBuffer


let cslice_of (st:rcv_state) : R.const_slice =
  assume (st.rcv_to <= LP.validator_max_length);
  R.MkSlice (C.of_buffer st.rcv_b) st.rcv_to

let receive_c_wait_ServerHello
  (st:rcv_state)
  : ST (TLSError.result (option ((Rcv.c_wait_ServerHello (cslice_of st)) & uint_32)))
    (requires fun h ->
      G.reveal st.current_flt == Rcv.F_c_wait_ServerHello /\
      (rcv_reset_inv st h \/ rcv_in_progress_inv st h))
    (ensures fun h0 r h1 ->
      B.modifies (Rcv.footprint st.hsl_rcv_st) h0 h1 /\
      (let open FStar.Error in
       match r with
       | Error _ -> True
       | Correct None ->
         rcv_in_progress_inv st h1
       | Correct (Some (flt, idx_end)) ->
         idx_end <= st.rcv_to /\
         Rcv.valid_c_wait_ServerHello st.rcv_from idx_end flt h1 /\
         rcv_reset_inv st h1))
  = Rcv.receive_c_wait_ServerHello st.hsl_rcv_st (cslice_of st) st.rcv_from st.rcv_to

let receive_c12_wait_ServerHelloDone
  (st:rcv_state)
  : ST (TLSError.result (option (Rcv.c12_wait_ServerHelloDone (cslice_of st))))
    (requires fun h ->
      G.reveal st.current_flt == Rcv.F_c12_wait_ServerHelloDone /\
      (rcv_reset_inv st h \/ rcv_in_progress_inv st h))
    (ensures fun h0 r h1 ->
      B.modifies (Rcv.footprint st.hsl_rcv_st) h0 h1 /\
      (let open FStar.Error in
       match r with
       | Error _ -> True
       | Correct None ->
         rcv_in_progress_inv st h1
       | Correct (Some flt) ->
         Rcv.valid_c12_wait_ServerHelloDone st.rcv_from st.rcv_to flt h1 /\
         rcv_reset_inv st h1))
  = Rcv.receive_c12_wait_ServerHelloDone st.hsl_rcv_st (cslice_of st) st.rcv_from st.rcv_to

assume val bs : bytes

let test_change_of_flight (st:rcv_state) : St unit =
  let open FStar.Error in
  (*
   * assume that the state is in the reset state, i.e. no flight in progress
   * this is what you get when rcv_state is created
   *)
  let h = ST.get () in
  assume (rcv_reset_inv st h);

  (* try to receive ServerHello *)
  let st = { st with current_flt = G.hide Rcv.F_c_wait_ServerHello } in
  let r = receive_c_wait_ServerHello st in
  match r with
  | Error e -> ()  //abandon
  | Correct None ->
    //waiting for more data
    //append some bytes
    assume (v st.rcv_to + Bytes.length bs <= B.length st.rcv_b);
    let st = buffer_received_fragment st bs in
    //call receive again
    let r = receive_c_wait_ServerHello st in
    ()  //and so on
  | Correct (Some (flt, idx_end)) ->
    //flt is a valid ServerHello flight
    //now let's try to parse ServerHelloDone
    let st = { st with
      current_flt = G.hide Rcv.F_c12_wait_ServerHelloDone;
      rcv_from = idx_end } in

    let r = receive_c12_wait_ServerHelloDone st in
    ()  //and so on




