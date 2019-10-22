module TLS.Handshake

open Mem
open TLSConstants

module HS = FStar.HyperStack 
module Range = Range
module Epochs = Old.Epochs
module Nego = Negotiation


// annoyingly, we will need specification-level variants too.

module Machine = TLS.Handshake.Machine
module Send = TLS.Handshake.Send
module Receive = TLS.Handshake.Receive

// 17-04-08 TODO unclear how abstract Epochs should be.
let logT (s:Machine.state) (h:HS.mem) = Epochs.epochsT (Machine.epochsT s h) h

// 19-09-11 adapted from State, to be reviewed
// returns the current counters, with a precise refinement
let iT (s:Machine.state) rw (h:HS.mem): GTot (Epochs.epoch_ctr_inv (Machine.frame s) (Machine.epochsT s h).Epochs.es) =
  match rw with
  | Reader -> Epochs.readerT (Machine.epochsT s h) h
  | Writer -> Epochs.writerT (Machine.epochsT s h) h

// this function increases (how to specify it once for all?)
let i (s:Machine.state) (rw:rw) : ST int
  (requires (fun h -> True))
  (ensures (fun h0 i h1 ->
    h0 == h1 /\
    i = iT s rw h1 /\
    Epochs.get_ctr_post (Machine.epochsT s h1) rw h0 i h1))
  =
  assume false;
  if Machine.is_init s then -1 else
  let n = Machine.nonce s in 
  let es = Machine.epochs s n in 
  match rw with
  | Reader -> Epochs.get_reader es
  | Writer -> Epochs.get_writer es

// returns the current epoch for reading or writing
let eT s rw (h:HS.mem {iT s rw h >= 0}) =
  let es = logT s h in
  let j = iT s rw h in
  assume(j < Seq.length es); //17-04-08 added verification hint; assumed for now.
  Seq.index es j
  
let logIndex (#t:Type) (log: Seq.seq t) = n:int { -1 <= n /\ n < Seq.length log }

val is_0rtt_offered: Machine.state -> bool
// let mode = get_mode s in 
// Nego.zeroRTToffer mode.Nego.n_offer

// returns the current exporter keys
val xkeys_of: s:Machine.state -> ST (Seq.seq Old.KeySchedule.exportKey)
  (requires Machine.invariant s)
  (ensures fun h0 r h1 -> modifies_none h0 h1 /\ Seq.length r <= 2)

(* ----------------------- Control Interface -------------------------*)

// Create instance for a fresh connection, with optional resumption for clients
val create: r0:rid -> cfg:config -> r:role -> ST Machine.state
  (requires (fun h -> True))
  (ensures (fun h0 s h1 ->
    modifies Set.empty h0 h1 /\
    //fresh_subregion r0 (HS?.region s) h0 h1 /\
    // hs_inv s h1 /\
    // HS?.r s = r /\
    // HS?.cfg s = cfg /\
    logT s h1 == Seq.empty 
    ))

let mods s h0 h1 = HS.modifies_one (Machine.frame s) h0 h1

let modifies_internal h0 s h1 =
    Machine.invariant s h1 /\
    mods s h0 h1
    // can't say it abstractly:
    // HS.modifies_ref (Machine.frame s)  !{as_ref s.state} ( h0) ( h1)

// Idle client starts a full handshake on the current connection
val rehandshake: s:Machine.client -> config -> ST bool
  (requires (fun h -> Machine.invariant s h))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))

// Idle client starts an abbreviated handshake resuming the current session
val rekey: s:Machine.client -> config -> ST bool
  (requires (fun h -> Machine.invariant s h))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))

// Post-handshake servers can send new tickets that include arbitrary app data
val send_ticket: s:Machine.server -> app_data:Bytes.bytes -> ST bool
  (requires (fun h -> Machine.invariant s h))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))

// (Idle) Server requests an handshake
val request: s:Machine.server -> config -> ST bool
  (requires (fun h -> Machine.invariant s h))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))

val invalidateSession: s:Machine.state -> ST unit
  (requires (Machine.invariant s))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1)) // underspecified


(* ------------------ Outgoing -----------------------*)

open TLSError //17-04-07 necessary to TC the | Correct pattern?
//val next_fragment: see .fsti
let next_fragment_ensures (#i:TLSInfo.id) (s:Machine.state) h0 (result: result (Send.outgoing i)) h1 =
    let es = logT s h0 in
    let w0 = iT s Writer h0 in
    let w1 = iT s Writer h1 in
    let r0 = iT s Reader h0 in
    let r1 = iT s Reader h1 in
    Machine.invariant s h1 /\
    mods s h0 h1 /\
    r1 == r0 /\
    Seq.length (logT s h1) >= Seq.length (logT s h0) /\
    ( let open FStar.Error in
      match result with
      | Correct (Send.Outgoing frg nextKeys complete) ->
          w1 == (if Some? nextKeys then w0 + 1 else w0) /\
          (b2t complete ==> r1 = w1 /\ Seq.indexable (logT s h1) w1 (*/\ completed (eT s Writer h1)*) )
      | _ -> True )

let next_fragment_requires (#i:TLSInfo.id) (s:Machine.state) h0 =
  let es = logT s h0 in
  let j = iT s Writer h0 in
  j < Seq.length es /\ //17-04-08 added verification hint
  Machine.invariant s h0 /\
  (if j < 0 then TLSInfo.PlaintextID? i else let e = Seq.index es j in i = Epochs.epoch_id e)


/// Returns outgoing handshake packet or signal; the length of the
/// outgoing packet can be bounded tighter than the TLS
/// max_fragment_length.

val next_fragment_bounded: s:Machine.state -> i:TLSInfo.id -> max:UInt32.t -> 

  ST (result (Send.outgoing i))
  (requires fun h0 -> next_fragment_requires #i s h0)
  (ensures fun h0 r h1 -> next_fragment_ensures #i s h0 r h1)

val next_fragment: s:Machine.state -> i:TLSInfo.id -> 
  ST (result (Send.outgoing i))
  (requires (fun h0 -> next_fragment_requires #i s h0))
  (ensures (fun h0 r h1 -> next_fragment_ensures #i s h0 r h1))

val to_be_written: s:Machine.state -> ST nat
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(* ----------------------- Incoming ----------------------- *)

let recv_ensures (s:Machine.state) (h0:HS.mem) (result:Receive.incoming) (h1:HS.mem) =
    let w0 = iT s Writer h0 in
    let w1 = iT s Writer h1 in
    let r0 = iT s Reader h0 in
    let r1 = iT s Reader h1 in
    Machine.invariant s h1 /\
    mods s h0 h1 /\
    w1 == w0 /\
    r1 == (if Receive.in_next_keys result then r0 + 1 else r0) /\
    (b2t (Receive.in_complete result) ==> r1 >= 0 /\ r1 = w1 /\ iT s Reader h1 >= 0 (*/\ completed (eT s Reader h1)*) )

val recv_fragment: 
  s:Machine.state -> 
  // high-level incoming fragment 
  #i:TLSInfo.id -> rg:Range.frange i -> f:Range.rbytes rg -> 
  // resulting signals, keys, outgoing fragments, etc
  ST Receive.incoming 
  (requires Machine.invariant s)
  (ensures recv_ensures s)

// special case: CCS before 1p3; could merge with recv_fragment
val recv_ccs: Receive.(
  s:Machine.state -> ST incoming
  (requires (Machine.invariant s))
  (ensures (fun h0 result h1 ->
    recv_ensures s h0 result h1 /\
    (InError? result \/ result = InAck true false))
    ))

val authorize: Receive.(
  s:Machine.state -> Cert.chain -> ST incoming // special case: explicit authorize (needed?)
  (requires (Machine.invariant s))
  (ensures (fun h0 result h1 ->
    (InAck? result \/ InError? result) /\ recv_ensures s h0 result h1 )))
