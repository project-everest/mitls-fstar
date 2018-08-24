module Old.Handshake

open Mem
open TLSConstants

module HS = FStar.HyperStack 
module Range = Range
module Epochs = Old.Epochs
module KeySchedule = Old.KeySchedule

#set-options "--admit_smt_queries true"

val hs: Type0

// the handshake epochs internally maintains counters for the current reader and writer
val nonce: hs -> Tot TLSInfo.random  // unique for all honest instances; locally enforced
val region_of: hs -> Tot Parse.rgn
val role_of: hs -> role
val random_of: hs -> Tot TLSInfo.random
val config_of: hs -> ST config
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> h0 == h1)
val version_of: hs -> ST TLSConstants.protocolVersion
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> h0 == h1)
val get_mode: hs -> ST Negotiation.mode
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> h0 == h1)
val is_server_hrr: hs -> ST bool
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> h0 == h1)
val is_0rtt_offered: hs -> ST bool
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> h0 == h1)

// annoyingly, we will need specification-level variants too.

// 17-04-08 TODO unclear how abstract Epochs should be.

let epochs_t_of (s:hs) = Seq.seq (Epochs.epoch (region_of s) (random_of s))
val epochs_of: s:hs -> Tot (Epochs.epochs (region_of s) (random_of s))

// val logT: s:hs ->  h:HS.mem -> GTot (epochs_t_of s)
let logT (s:hs) (h:HS.mem) = Epochs.epochsT (epochs_of s) h

let non_empty h s = Seq.length (logT s h) > 0

let logIndex (#t:Type) (log: Seq.seq t) = n:int { -1 <= n /\ n < Seq.length log }

val completed: #region:rgn -> #nonce:TLSInfo.random -> Epochs.epoch region nonce -> Type0

val hs_inv: s:hs -> HS.mem -> Type0

let es_of (s:hs) = Epochs.((epochs_of s).es)

// returns the current counters, with a precise refinement
let iT (s:hs) rw (h:HS.mem): GTot (Epochs.epoch_ctr_inv (region_of s) (es_of s)) =
  match rw with
  | Reader -> Epochs.readerT (epochs_of s) h
  | Writer -> Epochs.writerT (epochs_of s) h

// this function increases (how to specify it once for all?)
let i (s:hs) (rw:rw) : ST int
  (requires (fun h -> True))
  (ensures (fun h0 i h1 ->
    h0 == h1 /\
    i = iT s rw h1 /\
    Epochs.get_ctr_post (epochs_of s) rw h0 i h1))
=
  assume false;
  match rw with
  | Reader -> Epochs.get_reader (epochs_of s)
  | Writer -> Epochs.get_writer (epochs_of s)

// returns the current epoch for reading or writing
let eT s rw (h:HS.mem {iT s rw h >= 0}) =
  let es = logT s h in
  let j = iT s rw h in
  assume(j < Seq.length es); //17-04-08 added verification hint; assumed for now.
  Seq.index es j
let readerT s h = eT s Reader h
let writerT s h = eT s Writer h

// returns the current exporter keys
val xkeys_of: s:hs -> ST (Seq.seq KeySchedule.exportKey)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> h0 == h1 /\ Seq.length r <= 2)


type incoming =
  | InAck: // the fragment is accepted, and...
      next_keys : bool -> // the reader index increases;
      complete  : bool -> // the handshake is complete!
      incoming
  | InQuery: Cert.chain -> bool -> incoming // could be part of InAck if no explicit user auth
  | InError: TLSError.error -> incoming // how underspecified should it be?

let in_next_keys (r:incoming) = InAck? r && InAck?.next_keys r
let in_complete (r:incoming)  = InAck? r && InAck?.complete r

(* ----------------------- Control Interface -------------------------*)

// Create instance for a fresh connection, with optional resumption for clients
val create: r0:rid -> cfg:config -> r:role -> ST hs
  (requires (fun h -> True))
  (ensures (fun h0 s h1 ->
    modifies Set.empty h0 h1 /\
    //fresh_subregion r0 (HS?.region s) h0 h1 /\
    // hs_inv s h1 /\
    // HS?.r s = r /\
    // HS?.cfg s = cfg /\
    logT s h1 == Seq.empty ))

let mods s h0 h1 = HS.modifies_one (region_of s) h0 h1

let modifies_internal h0 s h1 =
    hs_inv s h1 /\
    mods s h0 h1
    // can't say it abstractly:
    // HS.modifies_ref (region_of s)  !{as_ref s.state} ( h0) ( h1)

// Idle client starts a full handshake on the current connection
val rehandshake: s:hs -> config -> ST bool
  (requires (fun h -> hs_inv s h /\ role_of s = Client))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))

// Idle client starts an abbreviated handshake resuming the current session
val rekey: s:hs -> config -> ST bool
  (requires (fun h -> hs_inv s h /\ role_of s = Client))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))

// (Idle) Server requests an handshake
val request: s:hs -> config -> ST bool
  (requires (fun h -> hs_inv s h /\ role_of s = Server))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))

val invalidateSession: s:hs -> ST unit
  (requires (hs_inv s))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1)) // underspecified


(* ------------------ Outgoing -----------------------*)

open TLSError //17-04-07 necessary to TC the | Correct pattern?
//val next_fragment: see .fsti
let next_fragment_ensures (#i:TLSInfo.id) (s:hs) h0 (result: result (HandshakeLog.outgoing i)) h1 =
    let es = logT s h0 in
    let w0 = iT s Writer h0 in
    let w1 = iT s Writer h1 in
    let r0 = iT s Reader h0 in
    let r1 = iT s Reader h1 in
    hs_inv s h1 /\
    mods s h0 h1 /\
    r1 == r0 /\
    Seq.length (logT s h1) >= Seq.length (logT s h0) /\
    ( let open FStar.Error in
      match result with
      | Correct (HandshakeLog.Outgoing frg nextKeys complete) ->
          w1 == (if Some? nextKeys then w0 + 1 else w0) /\
          (b2t complete ==> r1 = w1 /\ Seq.indexable (logT s h1) w1 (*/\ completed (eT s Writer h1)*) )
      | _ -> True )

let next_fragment_requires (#i:TLSInfo.id) (s:hs) h0 =
  let es = logT s h0 in
  let j = iT s Writer h0 in
  j < Seq.length es /\ //17-04-08 added verification hint
  hs_inv s h0 /\
  (if j < 0 then TLSInfo.PlaintextID? i else let e = Seq.index es j in i = Epochs.epoch_id e)

val next_fragment_bounded: s:hs -> i:TLSInfo.id -> nax:nat -> ST (result (HandshakeLog.outgoing i))
  (requires (fun h0 -> next_fragment_requires #i s h0))
  (ensures (fun h0 r h1 -> next_fragment_ensures #i s h0 r h1))

val next_fragment: s:hs -> i:TLSInfo.id -> ST (result (HandshakeLog.outgoing i))
  (requires (fun h0 -> next_fragment_requires #i s h0))
  (ensures (fun h0 r h1 -> next_fragment_ensures #i s h0 r h1))

val to_be_written: s:hs -> ST nat
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(* ----------------------- Incoming ----------------------- *)

let recv_ensures (s:hs) (h0:HS.mem) (result:incoming) (h1:HS.mem) =
    let w0 = iT s Writer h0 in
    let w1 = iT s Writer h1 in
    let r0 = iT s Reader h0 in
    let r1 = iT s Reader h1 in
    hs_inv s h1 /\
    mods s h0 h1 /\
    w1 == w0 /\
    r1 == (if in_next_keys result then r0 + 1 else r0) /\
    (b2t (in_complete result) ==> r1 >= 0 /\ r1 = w1 /\ iT s Reader h1 >= 0 (*/\ completed (eT s Reader h1)*) )

val recv_fragment: s:hs -> #i:TLSInfo.id -> rg:Range.frange i -> f:Range.rbytes rg -> ST incoming (* incoming transitions for our state machine *)
  (requires (hs_inv s))
  (ensures (recv_ensures s))

// special case: CCS before 1p3; could merge with recv_fragment
val recv_ccs: s:hs -> ST incoming
  (requires (hs_inv s))
  (ensures (fun h0 result h1 ->
    recv_ensures s h0 result h1 /\
    (InError? result \/ result = InAck true false))
    )

val authorize: s:hs -> Cert.chain -> ST incoming // special case: explicit authorize (needed?)
  (requires (hs_inv s))
  (ensures (fun h0 result h1 ->
    (InAck? result \/ InError? result) /\ recv_ensures s h0 result h1 ))
