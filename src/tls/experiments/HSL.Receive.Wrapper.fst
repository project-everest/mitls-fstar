module HSL.Receive.Wrapper

open FStar.Integers
open FStar.HyperStack.ST

module G  = FStar.Ghost
module Bytes = FStar.Bytes
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B  = LowStar.Buffer

module LP = LowParse.Low.Base

module Rcv = HSL.Receive

(*
 * A wrapper over HSL.receive as expected by the current TLS.Handshake.Machine
 *)

type byte = FStar.Bytes.byte
type bytes = FStar.Bytes.bytes

noeq type rcv_state = {
  current_flt : G.erased Rcv.in_progress_flt_t;
  hsl_rcv_st  : Rcv.hsl_state;
  rcv_b       : b:B.buffer byte{B.loc_disjoint (B.loc_buffer b) (Rcv.footprint hsl_rcv_st)};
  rcv_from    : uint_32;
  rcv_to      : i:uint_32{rcv_from <= i /\ i <= B.len rcv_b}
}

/// In case of partially parsed flights, the prefix [rcv_from, Rcv.length_parsed_bytes]
///   is what HSL.Receive maintains

let rcv_inv (st:rcv_state) (h:HS.mem) : Type0 =
  B.live h st.rcv_b /\
  Rcv.invariant st.hsl_rcv_st h /\
  Rcv.length_parsed_bytes st.hsl_rcv_st h <= (v st.rcv_to - v st.rcv_from) /\
  Rcv.parsed_bytes st.hsl_rcv_st h ==
    Seq.slice (B.as_seq h st.rcv_b) (v st.rcv_from) (v st.rcv_from + Rcv.length_parsed_bytes st.hsl_rcv_st h) /\
  ((Rcv.in_progress_flt st.hsl_rcv_st h == Rcv.F_none) \/
   (Rcv.in_progress_flt st.hsl_rcv_st h == G.reveal st.current_flt))


let frame_rcv_inv
  (st:rcv_state) (l:B.loc) (h0 h1:HS.mem)
  : Lemma
    (requires
      rcv_inv st h0 /\
      B.(loc_disjoint (loc_union (Rcv.footprint st.hsl_rcv_st) (loc_buffer st.rcv_b)) l /\
      B.modifies l h0 h1))
    (ensures rcv_inv st h1 /\ B.as_seq h0 st.rcv_b == B.as_seq h1 st.rcv_b)
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
      rcv_inv st h1 /\
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
      rcv_inv st h /\
      Bytes.length bs <> 0 /\  //required by FStar.Bytes.store_bytes
      v st.rcv_to + Bytes.length bs <= B.length st.rcv_b)  //that adding these bytes does not overflow the buffer
    (ensures fun h0 rst h1 ->
      rcv_inv rst h1 /\
      rst `only_increments_rcv_to` st /\
      B.(modifies (loc_buffer (gsub st.rcv_b st.rcv_to (Bytes.len bs)))) h0 h1 /\
      Seq.slice (B.as_seq h1 rst.rcv_b) (v st.rcv_to) (v rst.rcv_to) == Bytes.reveal bs)
  = let h0 = ST.get () in

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

// module HSM = Parsers.Handshake

// type sh_flight = {
//   sh : m:HSM.handshake{HSM.M_server_hello? m}
// }

// let receive_c_wait_ServerHello
//   (st:rcv_state)
//   : ST (TLSError.result (option (sh_flight & uint_32)))
//     (requires fun h ->
//       rcv_inv st h /\
