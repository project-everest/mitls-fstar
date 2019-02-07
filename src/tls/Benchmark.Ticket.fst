module Benchmark.Ticket

open FStar.Bytes
open FStar.Error

open Mem
// open Parse
open TLSError

module TC = Parsers.TicketContents
module TC12 = Parsers.TicketContents12
module TC13 = Parsers.TicketContents13
module PB = Parsers.Boolean
module LPB = LowParse.Low.Base
module U32 = FStar.UInt32
module B = LowStar.Buffer

#reset-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 64 --z3cliopt smt.arith.nl=false --z3refresh --using_facts_from '* -FStar.Tactics -FStar.Reflection' --log_queries"


let write_ticket12 
  (tc: TC.ticketContents) 
  (sl: LPB.slice) (pos: U32.t) : Stack U32.t
  (requires (fun h -> 
    LPB.live_slice h sl /\ 
    U32.v pos <= U32.v sl.LPB.len /\ 
    TC.T_ticket12? tc ))
  (ensures (fun h pos' h' ->
    B.modifies (LPB.loc_slice_from sl pos) h h' /\ (
    if pos' = LPB.max_uint32
    then True
    else
      LPB.valid_content_pos TC.ticketContents_parser h' sl pos tc pos'
  )))
= match tc with
  | TC.T_ticket12 ({ TC12.pv=pv; TC12.cs=cs; TC12.ems=ems; TC12.master_secret=ms }) ->
    if (sl.LPB.len `U32.sub` pos) `U32.lt` 54ul
    then LPB.max_uint32
    else begin
      let pos1 = pos `U32.add` 1ul in
      let pos2 = Parsers.ProtocolVersion.protocolVersion_writer pv sl pos1 in
      let pos3 = Parsers.CipherSuite.cipherSuite_writer cs sl pos2 in
      let pos4 = Parsers.Boolean.boolean_writer ems sl pos3 in
      FStar.Bytes.store_bytes ms (B.sub sl.LPB.base pos4 48ul);
      let h = get () in
      Parsers.TicketContents12_master_secret.ticketContents12_master_secret_intro h sl pos4;
      let pos5 = pos4 `U32.add` 48ul in
      let h = get () in
      Parsers.TicketContents12.ticketContents12_valid h sl pos1;
      Parsers.TicketContents.finalize_ticketContents_ticket12 sl pos;
      pos5
    end

// #reset-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 64 --z3cliopt smt.arith.nl=false --z3cliopt trace=true --z3refresh --using_facts_from '* -FStar.Tactics -FStar.Reflection' --log_queries"

module HS = FStar.HyperStack

module LPI = LowParse.Low.Int

#reset-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 256 --z3cliopt smt.arith.nl=false --z3refresh --using_facts_from '* -FStar.Tactics -FStar.Reflection' --log_queries --query_stats"

let write_ticket13 (tc: TC.ticketContents) (sl: LPB.slice) (pos: U32.t) : Stack U32.t
  (requires (fun h -> LPB.live_slice h sl /\ U32.v pos <= U32.v sl.LPB.len /\ U32.v sl.LPB.len <= U32.v LPB.max_uint32 /\ TC.T_ticket13? tc))
  (ensures (fun h pos' h' ->
    B.modifies (LPB.loc_slice_from sl pos) h h' /\ (
    if pos' = LPB.max_uint32
    then True
    else
      LPB.valid_content_pos TC.ticketContents_parser h' sl pos tc pos'
  )))
= let h0 = get () in
  match tc with
  | TC.T_ticket13 ({ TC13.cs=cs; TC13.rms=rms; TC13.nonce=nonce; TC13.creation_time=created; TC13.age_add=age; TC13.custom_data=custom }) ->
    if (sl.LPB.len `U32.sub` pos) `U32.lt` (15ul `U32.add` len rms `U32.add` len nonce `U32.add` len custom)
    then LPB.max_uint32
    else begin
      let pos1 = pos `U32.add` 1ul in
      let pos2 = Parsers.CipherSuite.cipherSuite_writer cs sl pos1 in
      let len_rms = len rms in
      let _ = FStar.Bytes.store_bytes rms (B.sub sl.LPB.base (pos2 `U32.add` 1ul) len_rms) in
      let pos3 = Parsers.TicketContents13_rms.ticketContents13_rms_finalize sl pos2 len_rms in
      let len_nonce = len nonce in
      let _ = if len_nonce <> 0ul then FStar.Bytes.store_bytes nonce (B.sub sl.LPB.base (pos3 `U32.add` 1ul) len_nonce) in
      let pos4 = Parsers.TicketContents13_nonce.ticketContents13_nonce_finalize sl pos3 len_nonce in
      let pos5 = LPI.write_u32 created sl pos4 in
      let pos6 = LPI.write_u32 age sl pos5 in
      let len_custom = len custom in
      let _ = if len_custom <> 0ul then FStar.Bytes.store_bytes custom (B.sub sl.LPB.base (pos6 `U32.add` 2ul) len_custom) in
      let pos7 = Parsers.TicketContents13_custom_data.ticketContents13_custom_data_finalize sl pos6 len_custom in
      let h = get () in
      Parsers.TicketContents13.ticketContents13_valid h sl (pos `U32.add` 1ul);
      Parsers.TicketContents.finalize_ticketContents_ticket13 sl pos;
      pos7
    end

inline_for_extraction
let store_bytes'
  (src:bytes)
  (dst:lbuffer (len src))
: Stack unit
    (requires (fun h0 -> B.live h0 dst))
    (ensures  (fun h0 r h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      Seq.equal (FStar.Bytes.reveal src) (B.as_seq h1 dst)))
= if len src <> 0ul then store_bytes src dst

let write_ticket13' (tc: TC.ticketContents) (sl: LPB.slice) (pos: U32.t) : Stack U32.t
  (requires (fun h -> LPB.live_slice h sl /\ U32.v pos <= U32.v sl.LPB.len /\ U32.v sl.LPB.len <= U32.v LPB.max_uint32 /\ TC.T_ticket13? tc))
  (ensures (fun h pos' h' ->
    B.modifies (LPB.loc_slice_from sl pos) h h' /\ (
    if pos' = LPB.max_uint32
    then True
    else
      LPB.valid_content_pos TC.ticketContents_parser h' sl pos tc pos'
  )))
= let h0 = get () in
  match tc with
  | TC.T_ticket13 ({ TC13.cs=cs; TC13.rms=rms; TC13.nonce=nonce; TC13.creation_time=created; TC13.age_add=age; TC13.custom_data=custom }) ->
    if (sl.LPB.len `U32.sub` pos) `U32.lt` (15ul `U32.add` len rms `U32.add` len nonce `U32.add` len custom)
    then LPB.max_uint32
    else begin
      let pos1 = pos `U32.add` 1ul in
      let pos2 = Parsers.CipherSuite.cipherSuite_writer cs sl pos1 in
      let len_rms = len rms in
      let _ = FStar.Bytes.store_bytes rms (B.sub sl.LPB.base (pos2 `U32.add` 1ul) len_rms) in
      let pos3 = Parsers.TicketContents13_rms.ticketContents13_rms_finalize sl pos2 len_rms in
      let len_nonce = len nonce in
      let _ = store_bytes' nonce (B.sub sl.LPB.base (pos3 `U32.add` 1ul) len_nonce) in
      let pos4 = Parsers.TicketContents13_nonce.ticketContents13_nonce_finalize sl pos3 len_nonce in
      let pos5 = LPI.write_u32 created sl pos4 in
      let pos6 = LPI.write_u32 age sl pos5 in
      let len_custom = len custom in
      let _ = store_bytes' custom (B.sub sl.LPB.base (pos6 `U32.add` 2ul) len_custom) in
      let pos7 = Parsers.TicketContents13_custom_data.ticketContents13_custom_data_finalize sl pos6 len_custom in
      let h = get () in
      Parsers.TicketContents13.ticketContents13_valid h sl (pos `U32.add` 1ul);
      Parsers.TicketContents.finalize_ticketContents_ticket13 sl pos;
      pos7
    end

(* up to here, we are already at 28 s instead of 135 s *)

let write_ticket13_explicit_proof (tc: TC.ticketContents) (sl: LPB.slice) (pos: U32.t) : Stack U32.t
  (requires (fun h -> LPB.live_slice h sl /\ U32.v pos <= U32.v sl.LPB.len /\ TC.T_ticket13? tc))
  (ensures (fun h pos' h' ->
    B.modifies (LPB.loc_slice_from sl pos) h h' /\ 
    (
    if pos' = LPB.max_uint32
    then True
    else
      LPB.valid_content_pos TC.ticketContents_parser h' sl pos tc pos'
  )))
= let h0 = get () in
  match tc with
  | TC.T_ticket13 ({ TC13.cs=cs; TC13.rms=rms; TC13.nonce=nonce; TC13.creation_time=created; TC13.age_add=age; TC13.custom_data=custom }) ->
    if (sl.LPB.len `U32.sub` pos) `U32.lt` (15ul `U32.add` len rms `U32.add` len nonce `U32.add` len custom)
    then LPB.max_uint32
    else begin
//      assert (U32.v pos + 15 + U32.v (len rms) + U32.v (len nonce) + U32.v (len custom) <= U32.v sl.LPB.len);
      let pos1 = pos `U32.add` 1ul in
      let h1 = get () in
      let pos2 = Parsers.CipherSuite.cipherSuite_writer cs sl pos1 in
//      assert (U32.v pos2 <= U32.v pos1 + 2);
      let h2 = get () in
      let len_rms = len rms in
      let brms = B.sub sl.LPB.base (pos2 `U32.add` 1ul) len_rms in
//      let _ = FStar.Bytes.store_bytes rms brms in
      let _ = store_bytes rms brms in
      let h31 = get () in
      let _ =
        let l = (B.loc_buffer brms) in
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h2 sl pos1 l h31
      in
      let pos3 = Parsers.TicketContents13_rms.ticketContents13_rms_finalize sl pos2 len_rms in
//      assert (U32.v pos3 <= U32.v pos2 + 1 + U32.v len_rms);
      let h3 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos2 (pos2 `U32.add` 1ul) in
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h31 sl pos1 l h3
      in
      let len_nonce = len nonce in
      let bnonce = B.sub sl.LPB.base (pos3 `U32.add` 1ul) len_nonce in
      let _ = store_bytes' nonce bnonce in
//      let _ = if len_nonce <> 0ul then FStar.Bytes.store_bytes nonce bnonce in
      let h41 = get () in
      let _ =
//        let l = if len_nonce <> 0ul then B.loc_buffer bnonce else B.loc_none in
        let l = B.loc_buffer bnonce in
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h3 sl pos1 l h41;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos2 pos3) l);
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h3 sl pos2 l h41
      in
      let pos4 = Parsers.TicketContents13_nonce.ticketContents13_nonce_finalize sl pos3 len_nonce in
//      assert (U32.v pos4 <= U32.v pos3 + 1 + U32.v len_nonce);
      let h4 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos3 (pos3 `U32.add` 1ul) in
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h41 sl pos1 l h4;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos2 pos3) l);
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h41 sl pos2 l h4
      in
      let pos5 = LPI.write_u32 created sl pos4 in
//      assert (U32.v pos5 <= U32.v pos4 + 4);
      let h5 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos4 pos5 in
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h4 sl pos1 l h5;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos2 pos3) l);
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h4 sl pos2 l h5;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos3 pos4) l);
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h4 sl pos3 l h5
      in
      let pos6 = LPI.write_u32 age sl pos5 in
//      assert (U32.v pos6 <= U32.v pos5 + 4);
      let h6 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos5 pos6 in
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h5 sl pos1 l h6;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos2 pos3) l);
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h5 sl pos2 l h6;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos3 pos4) l);
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h5 sl pos3 l h6;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos4 pos5) l);
        LPB.valid_frame_strong LPI.parse_u32 h5 sl pos4 l h6
      in
      let len_custom = len custom in
      let bcustom = B.sub sl.LPB.base (pos6 `U32.add` 2ul) len_custom in
//      let _ = if len_custom <> 0ul then FStar.Bytes.store_bytes custom bcustom in
      let _ = store_bytes' custom bcustom in
      let h71 = get () in
        let _ =
//        let l = if len_custom <> 0ul then B.loc_buffer bcustom else B.loc_none in
        let l = B.loc_buffer bcustom in
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h6 sl pos1 l h71;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos2 pos3) l);
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h6 sl pos2 l h71;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos3 pos4) l);
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h6 sl pos3 l h71;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos4 pos5) l);
        LPB.valid_frame_strong LPI.parse_u32 h6 sl pos4 l h71;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos5 pos6) l);
        LPB.valid_frame_strong LPI.parse_u32 h6 sl pos5 l h71
      in
//      assert (U32.v pos6 + 2 <= U32.v sl.LPB.len);
      let pos7 = Parsers.TicketContents13_custom_data.ticketContents13_custom_data_finalize sl pos6 len_custom in
//      assert (U32.v pos7 <= U32.v pos6 + 2 + U32.v len_custom);
      let h7 = get () in
        let _ =
        let l = LPB.loc_slice_from_to sl pos6 (pos6 `U32.add` 2ul) in
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h71 sl pos1 l h7;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos2 pos3) l);
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h71 sl pos2 l h7;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos3 pos4) l);
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h71 sl pos3 l h7;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos4 pos5) l);
        LPB.valid_frame_strong LPI.parse_u32 h71 sl pos4 l h7;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos5 pos6) l);
        LPB.valid_frame_strong LPI.parse_u32 h71 sl pos5 l h7
      in
      let h = get () in
      Parsers.TicketContents13.ticketContents13_valid h sl (pos `U32.add` 1ul);
      Parsers.TicketContents.finalize_ticketContents_ticket13 sl pos;
      pos7
    end

(* here we are at 14 s, identifying the culprit for the framing lemmas (not the final modifies clause) *)

let write_ticket13_explicit_proof_2 (tc: TC.ticketContents) (sl: LPB.slice) (pos: U32.t) : Stack U32.t
  (requires (fun h -> LPB.live_slice h sl /\ U32.v pos <= U32.v sl.LPB.len /\ TC.T_ticket13? tc))
  (ensures (fun h pos' h' ->
    B.modifies (LPB.loc_slice_from sl pos) h h' /\ 
    (
    if pos' = LPB.max_uint32
    then True
    else
      LPB.valid_content_pos TC.ticketContents_parser h' sl pos tc pos'
  )))
= let h0 = get () in
  match tc with
  | TC.T_ticket13 ({ TC13.cs=cs; TC13.rms=rms; TC13.nonce=nonce; TC13.creation_time=created; TC13.age_add=age; TC13.custom_data=custom }) ->
    if (sl.LPB.len `U32.sub` pos) `U32.lt` (15ul `U32.add` len rms `U32.add` len nonce `U32.add` len custom)
    then LPB.max_uint32
    else begin
//      assert (U32.v pos + 15 + U32.v (len rms) + U32.v (len nonce) + U32.v (len custom) <= U32.v sl.LPB.len);
      let pos1 = pos `U32.add` 1ul in
      let h1 = get () in
      let pos2 = Parsers.CipherSuite.cipherSuite_writer cs sl pos1 in
//      assert (U32.v pos2 <= U32.v pos1 + 2);
      let h2 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos1 pos2 in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l)
      in
      let len_rms = len rms in
      let brms = B.sub sl.LPB.base (pos2 `U32.add` 1ul) len_rms in
//      let _ = FStar.Bytes.store_bytes rms brms in
      let _ = store_bytes rms brms in
      let h31 = get () in
      let _ =
        let l = (B.loc_buffer brms) in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h2 sl pos1 l h31
      in
      let pos3 = Parsers.TicketContents13_rms.ticketContents13_rms_finalize sl pos2 len_rms in
//      assert (U32.v pos3 <= U32.v pos2 + 1 + U32.v len_rms);
      let h3 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos2 (pos2 `U32.add` 1ul) in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h31 sl pos1 l h3
      in
      let len_nonce = len nonce in
      let bnonce = B.sub sl.LPB.base (pos3 `U32.add` 1ul) len_nonce in
      let _ = store_bytes' nonce bnonce in
//      let _ = if len_nonce <> 0ul then FStar.Bytes.store_bytes nonce bnonce in
      let h41 = get () in
      let _ =
//        let l = if len_nonce <> 0ul then B.loc_buffer bnonce else B.loc_none in
        let l = B.loc_buffer bnonce in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h3 sl pos1 l h41;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos2 pos3) l);
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h3 sl pos2 l h41
      in
      let pos4 = Parsers.TicketContents13_nonce.ticketContents13_nonce_finalize sl pos3 len_nonce in
//      assert (U32.v pos4 <= U32.v pos3 + 1 + U32.v len_nonce);
      let h4 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos3 (pos3 `U32.add` 1ul) in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h41 sl pos1 l h4;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos2 pos3) l);
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h41 sl pos2 l h4
      in
      let pos5 = LPI.write_u32 created sl pos4 in
//      assert (U32.v pos5 <= U32.v pos4 + 4);
      let h5 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos4 pos5 in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h4 sl pos1 l h5;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos2 pos3) l);
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h4 sl pos2 l h5;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos3 pos4) l);
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h4 sl pos3 l h5
      in
      let pos6 = LPI.write_u32 age sl pos5 in
//      assert (U32.v pos6 <= U32.v pos5 + 4);
      let h6 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos5 pos6 in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h5 sl pos1 l h6;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos2 pos3) l);
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h5 sl pos2 l h6;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos3 pos4) l);
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h5 sl pos3 l h6;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos4 pos5) l);
        LPB.valid_frame_strong LPI.parse_u32 h5 sl pos4 l h6
      in
      let len_custom = len custom in
      let bcustom = B.sub sl.LPB.base (pos6 `U32.add` 2ul) len_custom in
//      let _ = if len_custom <> 0ul then FStar.Bytes.store_bytes custom bcustom in
      let _ = store_bytes' custom bcustom in
      let h71 = get () in
        let _ =
//        let l = if len_custom <> 0ul then B.loc_buffer bcustom else B.loc_none in
        let l = B.loc_buffer bcustom in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h6 sl pos1 l h71;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos2 pos3) l);
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h6 sl pos2 l h71;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos3 pos4) l);
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h6 sl pos3 l h71;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos4 pos5) l);
        LPB.valid_frame_strong LPI.parse_u32 h6 sl pos4 l h71;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos5 pos6) l);
        LPB.valid_frame_strong LPI.parse_u32 h6 sl pos5 l h71
      in
//      assert (U32.v pos6 + 2 <= U32.v sl.LPB.len);
      let pos7 = Parsers.TicketContents13_custom_data.ticketContents13_custom_data_finalize sl pos6 len_custom in
//      assert (U32.v pos7 <= U32.v pos6 + 2 + U32.v len_custom);
      let h7 = get () in
        let _ =
        let l = LPB.loc_slice_from_to sl pos6 (pos6 `U32.add` 2ul) in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos1 pos2) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h71 sl pos1 l h7;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos2 pos3) l);
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h71 sl pos2 l h7;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos3 pos4) l);
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h71 sl pos3 l h7;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos4 pos5) l);
        LPB.valid_frame_strong LPI.parse_u32 h71 sl pos4 l h7;
        assume (B.loc_disjoint (LPB.loc_slice_from_to sl pos5 pos6) l);
        LPB.valid_frame_strong LPI.parse_u32 h71 sl pos5 l h7
      in
      let h = get () in
      Parsers.TicketContents13.ticketContents13_valid h sl (pos `U32.add` 1ul);
      Parsers.TicketContents.finalize_ticketContents_ticket13 sl pos;
      assume (B.loc_includes (LPB.loc_slice_from sl pos) (LPB.loc_slice_from_to sl pos (pos `U32.add` 1ul)));
      pos7
    end

let write_ticket13_explicit_proof_3 (tc: TC.ticketContents) (sl: LPB.slice) (pos: U32.t) : Stack U32.t
  (requires (fun h -> LPB.live_slice h sl /\ U32.v pos <= U32.v sl.LPB.len /\ TC.T_ticket13? tc))
  (ensures (fun h pos' h' ->
    B.modifies (LPB.loc_slice_from sl pos) h h' /\ 
    (
    if pos' = LPB.max_uint32
    then True
    else
      LPB.valid_content_pos TC.ticketContents_parser h' sl pos tc pos'
  )))
= let h0 = get () in
  match tc with
  | TC.T_ticket13 ({ TC13.cs=cs; TC13.rms=rms; TC13.nonce=nonce; TC13.creation_time=created; TC13.age_add=age; TC13.custom_data=custom }) ->
    if (sl.LPB.len `U32.sub` pos) `U32.lt` (15ul `U32.add` len rms `U32.add` len nonce `U32.add` len custom)
    then LPB.max_uint32
    else begin
//      assert (U32.v pos + 15 + U32.v (len rms) + U32.v (len nonce) + U32.v (len custom) <= U32.v sl.LPB.len);
      let pos1 = pos `U32.add` 1ul in
      let h1 = get () in
      let pos2 = Parsers.CipherSuite.cipherSuite_writer cs sl pos1 in
//      assert (U32.v pos2 <= U32.v pos1 + 2);
      let h2 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos1 pos2 in
        LPB.loc_includes_loc_slice_from_loc_slice_from_to sl pos pos1 pos2
      in
      let len_rms = len rms in
      let brms = B.sub sl.LPB.base (pos2 `U32.add` 1ul) len_rms in
//      let _ = FStar.Bytes.store_bytes rms brms in
      let _ = store_bytes rms brms in
      let h31 = get () in
      let _ =
        let l = (B.loc_buffer brms) in
        LPB.loc_slice_from_includes_gsub sl pos sl.LPB.base (pos2 `U32.add` 1ul) len_rms;
        LPB.loc_slice_from_to_gsub_disjoint sl sl.LPB.base pos pos2 (pos2 `U32.add` 1ul) len_rms;
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h2 sl pos1 l h31
      in
      let pos3 = Parsers.TicketContents13_rms.ticketContents13_rms_finalize sl pos2 len_rms in
//      assert (U32.v pos3 <= U32.v pos2 + 1 + U32.v len_rms);
      let h3 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos2 (pos2 `U32.add` 1ul) in
        LPB.loc_includes_loc_slice_from_loc_slice_from_to sl pos pos2 (pos2 `U32.add` 1ul);
        LPB.loc_slice_from_to_disjoint sl pos1 pos2 pos2 (pos2 `U32.add` 1ul);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h31 sl pos1 l h3
      in
      let len_nonce = len nonce in
      let bnonce = B.sub sl.LPB.base (pos3 `U32.add` 1ul) len_nonce in
      let _ = store_bytes' nonce bnonce in
//      let _ = if len_nonce <> 0ul then FStar.Bytes.store_bytes nonce bnonce in
      let h41 = get () in
      let _ =
//        let l = if len_nonce <> 0ul then B.loc_buffer bnonce else B.loc_none in
        let l = B.loc_buffer bnonce in
        LPB.loc_slice_from_includes_gsub sl pos sl.LPB.base (pos3 `U32.add` 1ul) len_nonce;
        LPB.loc_slice_from_to_gsub_disjoint sl sl.LPB.base pos1 pos2 (pos3 `U32.add` 1ul) len_nonce;
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h3 sl pos1 l h41;
        LPB.loc_slice_from_to_gsub_disjoint sl sl.LPB.base pos2 pos3 (pos3 `U32.add` 1ul) len_nonce;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h3 sl pos2 l h41
      in
      let pos4 = Parsers.TicketContents13_nonce.ticketContents13_nonce_finalize sl pos3 len_nonce in
//      assert (U32.v pos4 <= U32.v pos3 + 1 + U32.v len_nonce);
      let h4 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos3 (pos3 `U32.add` 1ul) in
        LPB.loc_includes_loc_slice_from_loc_slice_from_to sl pos pos3 (pos3 `U32.add` 1ul);
        LPB.loc_slice_from_to_disjoint sl pos1 pos2 pos3 (pos3 `U32.add` 1ul);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h41 sl pos1 l h4;
        LPB.loc_slice_from_to_disjoint sl pos2 pos3 pos3 (pos3 `U32.add` 1ul);
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h41 sl pos2 l h4
      in
      let pos5 = LPI.write_u32 created sl pos4 in
//      assert (U32.v pos5 <= U32.v pos4 + 4);
      let h5 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos4 pos5 in
        LPB.loc_includes_loc_slice_from_loc_slice_from_to sl pos pos4 pos5;
        LPB.loc_slice_from_to_disjoint sl pos1 pos2 pos4 pos5;
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h4 sl pos1 l h5;
        LPB.loc_slice_from_to_disjoint sl pos2 pos3 pos4 pos5;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h4 sl pos2 l h5;
        LPB.loc_slice_from_to_disjoint sl pos3 pos4 pos4 pos5;
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h4 sl pos3 l h5
      in
      let pos6 = LPI.write_u32 age sl pos5 in
//      assert (U32.v pos6 <= U32.v pos5 + 4);
      let h6 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos5 pos6 in
        LPB.loc_includes_loc_slice_from_loc_slice_from_to sl pos pos5 pos6;
        LPB.loc_slice_from_to_disjoint sl pos1 pos2 pos5 pos6;
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h5 sl pos1 l h6;
        LPB.loc_slice_from_to_disjoint sl pos2 pos3 pos5 pos6;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h5 sl pos2 l h6;
        LPB.loc_slice_from_to_disjoint sl pos3 pos4 pos5 pos6;
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h5 sl pos3 l h6;
        LPB.loc_slice_from_to_disjoint sl pos4 pos5 pos5 pos6;
        LPB.valid_frame_strong LPI.parse_u32 h5 sl pos4 l h6
      in
      let len_custom = len custom in
      let bcustom = B.sub sl.LPB.base (pos6 `U32.add` 2ul) len_custom in
//      let _ = if len_custom <> 0ul then FStar.Bytes.store_bytes custom bcustom in
      let _ = store_bytes' custom bcustom in
      let h71 = get () in
        let _ =
//        let l = if len_custom <> 0ul then B.loc_buffer bcustom else B.loc_none in
        let l = B.loc_buffer bcustom in
        LPB.loc_slice_from_includes_gsub sl pos sl.LPB.base (pos6 `U32.add` 2ul) len_custom;
        LPB.loc_slice_from_to_gsub_disjoint sl sl.LPB.base pos1 pos2 (pos6 `U32.add` 2ul) len_custom;
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h6 sl pos1 l h71;
        LPB.loc_slice_from_to_gsub_disjoint sl sl.LPB.base pos2 pos3 (pos6 `U32.add` 2ul) len_custom;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h6 sl pos2 l h71;
        LPB.loc_slice_from_to_gsub_disjoint sl sl.LPB.base pos3 pos4 (pos6 `U32.add` 2ul) len_custom;
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h6 sl pos3 l h71;
        LPB.loc_slice_from_to_gsub_disjoint sl sl.LPB.base pos4 pos5 (pos6 `U32.add` 2ul) len_custom;
        LPB.valid_frame_strong LPI.parse_u32 h6 sl pos4 l h71;
        LPB.loc_slice_from_to_gsub_disjoint sl sl.LPB.base pos5 pos6 (pos6 `U32.add` 2ul) len_custom;
        LPB.valid_frame_strong LPI.parse_u32 h6 sl pos5 l h71
      in
//      assert (U32.v pos6 + 2 <= U32.v sl.LPB.len);
      let pos7 = Parsers.TicketContents13_custom_data.ticketContents13_custom_data_finalize sl pos6 len_custom in
//      assert (U32.v pos7 <= U32.v pos6 + 2 + U32.v len_custom);
      let h7 = get () in
        let _ =
        let l = LPB.loc_slice_from_to sl pos6 (pos6 `U32.add` 2ul) in
        LPB.loc_includes_loc_slice_from_loc_slice_from_to sl pos pos6 (pos6 `U32.add` 2ul);
        LPB.loc_slice_from_to_disjoint sl pos1 pos2 pos6 (pos6 `U32.add` 2ul);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h71 sl pos1 l h7;
        LPB.loc_slice_from_to_disjoint sl pos2 pos3 pos6 (pos6 `U32.add` 2ul);
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h71 sl pos2 l h7;
        LPB.loc_slice_from_to_disjoint sl pos3 pos4 pos6 (pos6 `U32.add` 2ul);
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h71 sl pos3 l h7;
        LPB.loc_slice_from_to_disjoint sl pos4 pos5 pos6 (pos6 `U32.add` 2ul);
        LPB.valid_frame_strong LPI.parse_u32 h71 sl pos4 l h7;
        LPB.loc_slice_from_to_disjoint sl pos5 pos6 pos6 (pos6 `U32.add` 2ul);
        LPB.valid_frame_strong LPI.parse_u32 h71 sl pos5 l h7
      in
      let h = get () in
      Parsers.TicketContents13.ticketContents13_valid h sl (pos `U32.add` 1ul);
      Parsers.TicketContents.finalize_ticketContents_ticket13 sl pos;
      LPB.loc_includes_loc_slice_from_loc_slice_from_to sl pos pos (pos `U32.add` 1ul);
      pos7
    end

let write_ticket13_explicit_proof_2_somewhat_implicit (tc: TC.ticketContents) (sl: LPB.slice) (pos: U32.t) : Stack U32.t
  (requires (fun h -> LPB.live_slice h sl /\ U32.v pos <= U32.v sl.LPB.len /\ TC.T_ticket13? tc))
  (ensures (fun h pos' h' ->
    B.modifies (LPB.loc_slice_from sl pos) h h' /\ 
    (
    if pos' = LPB.max_uint32
    then True
    else
      LPB.valid_content_pos TC.ticketContents_parser h' sl pos tc pos'
  )))
= let h0 = get () in
  match tc with
  | TC.T_ticket13 ({ TC13.cs=cs; TC13.rms=rms; TC13.nonce=nonce; TC13.creation_time=created; TC13.age_add=age; TC13.custom_data=custom }) ->
    if (sl.LPB.len `U32.sub` pos) `U32.lt` (15ul `U32.add` len rms `U32.add` len nonce `U32.add` len custom)
    then LPB.max_uint32
    else begin
//      assert (U32.v pos + 15 + U32.v (len rms) + U32.v (len nonce) + U32.v (len custom) <= U32.v sl.LPB.len);
      let pos1 = pos `U32.add` 1ul in
      let h1 = get () in
      let pos2 = Parsers.CipherSuite.cipherSuite_writer cs sl pos1 in
//      assert (U32.v pos2 <= U32.v pos1 + 2);
      let h2 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos1 pos2 in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l)
      in
      let len_rms = len rms in
      let brms = B.sub sl.LPB.base (pos2 `U32.add` 1ul) len_rms in
//      let _ = FStar.Bytes.store_bytes rms brms in
      let _ = store_bytes rms brms in
      let h31 = get () in
      let _ =
        let l = (B.loc_buffer brms) in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h2 sl pos1 l h31
      in
      let pos3 = Parsers.TicketContents13_rms.ticketContents13_rms_finalize sl pos2 len_rms in
//      assert (U32.v pos3 <= U32.v pos2 + 1 + U32.v len_rms);
      let h3 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos2 (pos2 `U32.add` 1ul) in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h31 sl pos1 l h3
      in
      let len_nonce = len nonce in
      let bnonce = B.sub sl.LPB.base (pos3 `U32.add` 1ul) len_nonce in
      let _ = store_bytes' nonce bnonce in
//      let _ = if len_nonce <> 0ul then FStar.Bytes.store_bytes nonce bnonce in
      let h41 = get () in
      let _ =
//        let l = if len_nonce <> 0ul then B.loc_buffer bnonce else B.loc_none in
        let l = B.loc_buffer bnonce in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h3 sl pos1 l h41;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h3 sl pos2 l h41
      in
      let pos4 = Parsers.TicketContents13_nonce.ticketContents13_nonce_finalize sl pos3 len_nonce in
//      assert (U32.v pos4 <= U32.v pos3 + 1 + U32.v len_nonce);
      let h4 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos3 (pos3 `U32.add` 1ul) in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h41 sl pos1 l h4;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h41 sl pos2 l h4
      in
      let pos5 = LPI.write_u32 created sl pos4 in
//      assert (U32.v pos5 <= U32.v pos4 + 4);
      let h5 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos4 pos5 in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h4 sl pos1 l h5;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h4 sl pos2 l h5;
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h4 sl pos3 l h5
      in
      let pos6 = LPI.write_u32 age sl pos5 in
//      assert (U32.v pos6 <= U32.v pos5 + 4);
      let h6 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos5 pos6 in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h5 sl pos1 l h6;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h5 sl pos2 l h6;
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h5 sl pos3 l h6;
        LPB.valid_frame_strong LPI.parse_u32 h5 sl pos4 l h6
      in
      let len_custom = len custom in
      let bcustom = B.sub sl.LPB.base (pos6 `U32.add` 2ul) len_custom in
//      let _ = if len_custom <> 0ul then FStar.Bytes.store_bytes custom bcustom in
      let _ = store_bytes' custom bcustom in
      let h71 = get () in
        let _ =
//        let l = if len_custom <> 0ul then B.loc_buffer bcustom else B.loc_none in
        let l = B.loc_buffer bcustom in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h6 sl pos1 l h71;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h6 sl pos2 l h71;
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h6 sl pos3 l h71;
        LPB.valid_frame_strong LPI.parse_u32 h6 sl pos4 l h71;
        LPB.valid_frame_strong LPI.parse_u32 h6 sl pos5 l h71
      in
//      assert (U32.v pos6 + 2 <= U32.v sl.LPB.len);
      let pos7 = Parsers.TicketContents13_custom_data.ticketContents13_custom_data_finalize sl pos6 len_custom in
//      assert (U32.v pos7 <= U32.v pos6 + 2 + U32.v len_custom);
      let h7 = get () in
        let _ =
        let l = LPB.loc_slice_from_to sl pos6 (pos6 `U32.add` 2ul) in
        assume (B.loc_includes (LPB.loc_slice_from sl pos) l);
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h71 sl pos1 l h7;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h71 sl pos2 l h7;
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h71 sl pos3 l h7;
        LPB.valid_frame_strong LPI.parse_u32 h71 sl pos4 l h7;
        LPB.valid_frame_strong LPI.parse_u32 h71 sl pos5 l h7
      in
      let h = get () in
      Parsers.TicketContents13.ticketContents13_valid h sl (pos `U32.add` 1ul);
      Parsers.TicketContents.finalize_ticketContents_ticket13 sl pos;
      assume (B.loc_includes (LPB.loc_slice_from sl pos) (LPB.loc_slice_from_to sl pos (pos `U32.add` 1ul)));
      pos7
    end

let write_ticket13_explicit_proof_2_somewhat_implicit_2 (tc: TC.ticketContents) (sl: LPB.slice) (pos: U32.t) : Stack U32.t
  (requires (fun h -> LPB.live_slice h sl /\ U32.v pos <= U32.v sl.LPB.len /\ TC.T_ticket13? tc))
  (ensures (fun h pos' h' ->
    B.modifies (LPB.loc_slice_from sl pos) h h' /\ 
    (
    if pos' = LPB.max_uint32
    then True
    else
      LPB.valid_content_pos TC.ticketContents_parser h' sl pos tc pos'
  )))
= let h0 = get () in
  match tc with
  | TC.T_ticket13 ({ TC13.cs=cs; TC13.rms=rms; TC13.nonce=nonce; TC13.creation_time=created; TC13.age_add=age; TC13.custom_data=custom }) ->
    if (sl.LPB.len `U32.sub` pos) `U32.lt` (15ul `U32.add` len rms `U32.add` len nonce `U32.add` len custom)
    then LPB.max_uint32
    else begin
//      assert (U32.v pos + 15 + U32.v (len rms) + U32.v (len nonce) + U32.v (len custom) <= U32.v sl.LPB.len);
      let pos1 = pos `U32.add` 1ul in
      let h1 = get () in
      let pos2 = Parsers.CipherSuite.cipherSuite_writer cs sl pos1 in
//      assert (U32.v pos2 <= U32.v pos1 + 2);
      let h2 = get () in
      let len_rms = len rms in
      let brms = B.sub sl.LPB.base (pos2 `U32.add` 1ul) len_rms in
//      let _ = FStar.Bytes.store_bytes rms brms in
      let _ = store_bytes rms brms in
      let h31 = get () in
      let _ =
        let l = (B.loc_buffer brms) in
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h2 sl pos1 l h31
      in
      let pos3 = Parsers.TicketContents13_rms.ticketContents13_rms_finalize sl pos2 len_rms in
//      assert (U32.v pos3 <= U32.v pos2 + 1 + U32.v len_rms);
      let h3 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos2 (pos2 `U32.add` 1ul) in
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h31 sl pos1 l h3
      in
      let len_nonce = len nonce in
      let bnonce = B.sub sl.LPB.base (pos3 `U32.add` 1ul) len_nonce in
      let _ = store_bytes' nonce bnonce in
//      let _ = if len_nonce <> 0ul then FStar.Bytes.store_bytes nonce bnonce in
      let h41 = get () in
      let _ =
//        let l = if len_nonce <> 0ul then B.loc_buffer bnonce else B.loc_none in
        let l = B.loc_buffer bnonce in
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h3 sl pos1 l h41;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h3 sl pos2 l h41
      in
      let pos4 = Parsers.TicketContents13_nonce.ticketContents13_nonce_finalize sl pos3 len_nonce in
//      assert (U32.v pos4 <= U32.v pos3 + 1 + U32.v len_nonce);
      let h4 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos3 (pos3 `U32.add` 1ul) in
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h41 sl pos1 l h4;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h41 sl pos2 l h4
      in
      let pos5 = LPI.write_u32 created sl pos4 in
//      assert (U32.v pos5 <= U32.v pos4 + 4);
      let h5 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos4 pos5 in
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h4 sl pos1 l h5;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h4 sl pos2 l h5;
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h4 sl pos3 l h5
      in
      let pos6 = LPI.write_u32 age sl pos5 in
//      assert (U32.v pos6 <= U32.v pos5 + 4);
      let h6 = get () in
      let _ =
        let l = LPB.loc_slice_from_to sl pos5 pos6 in
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h5 sl pos1 l h6;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h5 sl pos2 l h6;
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h5 sl pos3 l h6;
        LPB.valid_frame_strong LPI.parse_u32 h5 sl pos4 l h6
      in
      let len_custom = len custom in
      let bcustom = B.sub sl.LPB.base (pos6 `U32.add` 2ul) len_custom in
//      let _ = if len_custom <> 0ul then FStar.Bytes.store_bytes custom bcustom in
      let _ = store_bytes' custom bcustom in
      let h71 = get () in
        let _ =
//        let l = if len_custom <> 0ul then B.loc_buffer bcustom else B.loc_none in
        let l = B.loc_buffer bcustom in
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h6 sl pos1 l h71;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h6 sl pos2 l h71;
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h6 sl pos3 l h71;
        LPB.valid_frame_strong LPI.parse_u32 h6 sl pos4 l h71;
        LPB.valid_frame_strong LPI.parse_u32 h6 sl pos5 l h71
      in
//      assert (U32.v pos6 + 2 <= U32.v sl.LPB.len);
      let pos7 = Parsers.TicketContents13_custom_data.ticketContents13_custom_data_finalize sl pos6 len_custom in
//      assert (U32.v pos7 <= U32.v pos6 + 2 + U32.v len_custom);
      let h7 = get () in
        let _ =
        let l = LPB.loc_slice_from_to sl pos6 (pos6 `U32.add` 2ul) in
        LPB.valid_frame_strong Parsers.CipherSuite.cipherSuite_parser h71 sl pos1 l h7;
        LPB.valid_frame_strong TC13.ticketContents13_rms_parser h71 sl pos2 l h7;
        LPB.valid_frame_strong TC13.ticketContents13_nonce_parser h71 sl pos3 l h7;
        LPB.valid_frame_strong LPI.parse_u32 h71 sl pos4 l h7;
        LPB.valid_frame_strong LPI.parse_u32 h71 sl pos5 l h7
      in
      let h = get () in
      Parsers.TicketContents13.ticketContents13_valid h sl (pos `U32.add` 1ul);
      Parsers.TicketContents.finalize_ticketContents_ticket13 sl pos;
      pos7
    end

#reset-options

let write_ticket (tc: TC.ticketContents) (sl: LPB.slice) (pos: U32.t) : Stack U32.t
  (requires (fun h -> LPB.live_slice h sl /\ U32.v pos <= U32.v sl.LPB.len /\ U32.v sl.LPB.len <= U32.v LPB.max_uint32 ))
  (ensures (fun h pos' h' ->
    B.modifies (LPB.loc_slice_from sl pos) h h' /\ (
    if pos' = LPB.max_uint32
    then True
    else
      LPB.valid_content_pos TC.ticketContents_parser h' sl pos tc pos'
  )))
= match tc with
  | TC.T_ticket12 _ ->
    write_ticket12 tc sl pos
  | TC.T_ticket13 _ ->
    write_ticket13 tc sl pos
