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

#reset-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 256 --z3cliopt smt.arith.nl=false --z3refresh --using_facts_from '* -FStar.Tactics -FStar.Reflection' --log_queries"

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
