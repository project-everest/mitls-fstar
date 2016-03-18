module Handshake

// current limitations: 
// - no abstract type for encrypted handshake traffic
// - no support for 0RTT and false-start
// - partnering between handshakes is static (needs fixing)

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found
open FStar.Set  

open Platform.Error
open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
open Range
open StatefulLHAE

// represents the outcome of a successful handshake, 
// providing context for the derived epoch
type handshake = 
  | Fresh of sessionInfo
  | Resumed of abbrInfo * sessionInfo //changed: was hs * seq epoch (creating cycle)
// We use SessionInfo as unique session indexes.
// We tried using instead hs, but this creates circularities
// We'll probably need a global log to reason about them.
// We should probably do the same in the session store.

// extracts a transport key identifier from a handshake record
val hsId: handshake -> Tot id

// relocate?
type fresh_subregion r0 r h0 h1 = fresh_region r h0 h1 /\ extends r r0

type epoch_region_inv (#i:id) (rgn:rid) (peer:rid) (r:reader (peerId i)) (w:writer i) =
  parent (region r) = rgn /\ 
  parent (region w) = rgn /\ 
  parent (peer_region r) = peer /\
  parent (peer_region w) = peer /\
  disjoint rgn peer /\
  disjoint (region r) (region w) /\
  disjoint (peer_region r) (peer_region w)
 
type epoch (rgn:rid) (peer:rid) =
  | Epoch: h: handshake ->
           r: reader (peerId (hsId h)) ->
           w: writer (hsId h) {epoch_region_inv rgn peer r w} -> epoch rgn peer
  // we would extend/adapt it for TLS 1.3,
  // e.g. to notify 0RTT/forwad-privacy transitions
  // for now epoch completion is a total function on handshake --- should be stateful

let set4 a b c d =   
  union  (singleton a) (union (singleton b) (union (singleton c) (singleton d)))

let regions (#p:rid) (#q:rid) (e:epoch p q) = 
  set4 (region e.r) (peer_region e.r) (region e.w) (peer_region e.w)

let epochs_footprint (#region:rid) (#peer:rid) (es: seq (epoch region peer)) =
  forall (i:nat { i < Seq.length es })
    (j:nat { j < Seq.length es /\ i <> j}).{:pattern (Seq.index es i); (Seq.index es j)}
    let ei = Seq.index es i in
    let ej = Seq.index es j in
    disjoint_regions (regions ei) (regions ej)
 
let epochs (r:rid) (p:rid) = es: seq (epoch r p) { epochs_footprint es }

// internal stuff: state machine, reader/writer counters, etc.
// (will take other HS fields as parameters)
abstract type handshake_state 

type hs =
  | HS: #region: rid ->
        #peer: rid ->
        r:role ->
        resume: option (sid:sessionID { r = Client }) ->
        cfg:config ->
        id: random ->  // unique for all honest instances; locally enforced; proof from global HS invariant? 
        log: rref region (epochs region peer) ->  // append-only; use monotonic? 
        state: rref region handshake_state  ->  // opaque, subject to invariant
        hs

(* the handshake internally maintains epoch 
   indexes for the current reader and writer *)

let stateType (s:hs) = epochs s.region s.peer * handshake_state 

let stateT (s:hs) (h:HyperHeap.t) : stateType s = (sel h s.log, sel h s.state)

let non_empty h s = Seq.length (sel h s.log) > 0

let logIndex (#t:Type) (log: seq t) = n:int { -1 <= n /\ n < Seq.length log }

// returns the current index in the log for reading or writing, or -1 if there is none.
// depends only on the internal state of the handshake
val iT0: s:hs -> rw:rw -> st:stateType s -> Tot (logIndex (fst st))
let iT s rw h = iT0 s rw (stateT s h) 


// returns the epoch for reading or writing
let eT s rw (h:HyperHeap.t { iT s rw h >= 0 }) = Seq.index (sel h s.log) (iT s rw h)

let readerT s h = eT s Reader h 
let writerT s h = eT s Writer h

// this function increases (how to specify it once for all?)
val i: s:hs -> rw:rw -> ST int 
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> h0 = h1 /\ i = iT s rw h1))

// name-clashing
// let reader s = i s Reader
// let writer s = i s Reader


let forall_epochs (hs:hs) h (p:(epoch (hs.region) (hs.peer) -> Type)) = 
  (let es = sel h hs.log in 
   forall (i:nat{i < Seq.length es}).{:pattern (Seq.index es i)} p (Seq.index es i))
     
//vs modifies clauses?
let unmodified_epochs s h0 h1 = 
  forall_epochs s h0 (fun e -> 
    let rs = regions e in 
    (forall (r:rid{Set.mem r rs}).{:pattern (Set.mem r rs)} Map.sel h0 r = Map.sel h1 r))

//epochs in h1 extends epochs in h0 by one 
let fresh_epoch h0 s h1 =
  let es0 = sel h0 s.log in
  let es1 = sel h1 s.log in 
  Seq.length es1 > 0 &&
  es0 = Seq.slice es1 0 (Seq.length es1 - 1)

let latest h (s:hs{Seq.length (sel h s.log) > 0}) = // accessing the latest epoch
 let es = sel h (HS.log s) in
 Seq.index es (Seq.length es - 1)

// separation policy: the handshake mutates its private state, 
// only depends on it, and only extends the log with fresh epochs.


// placeholder, to be implemented as a stateful property.
assume type completed: #region:rid -> #peer:rid -> epoch region peer -> Type

// consider adding an optional (resume: option sid) on the client side
// for now this bit is not explicitly authenticated.

// Well-formed logs are all prefixes of (Epoch; Complete)*; Error
// This crucially assumes that TLS keeps track of OutCCS and InCCSAck
// so that it knows which reader & writer to use (not always the latest ones):
// - within InCCSAck..OutCCS, we still use the older writer
// - within OutCCS..InCCSAck, we still use the older reader
// - otherwise we use the latest readers and writers

// technicality: module dependencies?
// we used to pre-declare all identifiers in TLSInfo
// we used owe could also record (fatal) errors as log terminators
 
// abstract invariant; depending only on the HS state (not the epochs state)
// no need for an epoch states invariant here: the HS never modifies them
 
assume type hs_invT (s:hs) (epochs:seq (epoch s.region s.peer)) : handshake_state -> Type

let hs_footprint_inv (s:hs) (h:HyperHeap.t) = 
  HyperHeap.contains_ref s.log h   /\ 
  HyperHeap.contains_ref s.state h /\ 
  Map.contains h s.peer

let hs_inv (s:hs) (h: HyperHeap.t) = 
  hs_invT s (sel h (HS.log s)) (sel h (HS.state s)) 
  /\ hs_footprint_inv s h


// returns the protocol version negotiated so far
// (used for formatting outgoing packets, but not trusted)
val version: s:hs -> ST protocolVersion
  (requires (hs_inv s))
  (ensures (fun h0 pv h1 -> h0 = h1))

(* used to be part of TLS.pickSendPV, with 3 cases: 

   (1) getMinVersion hs; then 
   (2) fixed by ServerHello; then
   (3) read from the current writing epoch

   val epoch_pv: #region:rid -> #peer:rid -> epoch region peer -> Tot ProtocolVersion

   Instead, we could add an invariant: for all epochs e in hs.log, we have epoch_pv e = version hs.
*)


(*** Control Interface ***)

// Create instance for a fresh connection, with optional resumption for clients
val init: r0:rid -> peer:rid -> r: role -> cfg:config -> resume: option (sid: sessionID { r = Client })  ->
  ST hs
  (requires (fun h -> True))
  (ensures (fun h0 s h1 ->
    modifies Set.empty h0 h1 /\
    fresh_subregion r0   (HS.region s) h0 h1 /\
    fresh_subregion peer (HS.peer s)   h0 h1 /\ //NS: perhaps unreasonable; how to sync with peer's allocation?
    hs_inv s h1 /\
    HS.r s = r /\
    HS.resume s = resume /\
    HS.cfg s = cfg /\
    sel h1 (HS.log s) = Seq.createEmpty ))
    
let modifies_internal h0 s h1 =
    hs_inv s h1 /\
    modifies_one s.region h0 h1 /\ 
    modifies_rref s.region !{as_ref s.state} h0 h1

// Idle client starts a full handshake on the current connection
val rehandshake: s:hs -> config -> ST bool
  (requires (fun h -> hs_inv s h /\ HS.r s = Client))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))

// Idle client starts an abbreviated handshake resuming the current session
val rekey: s:hs -> config -> ST bool
  (requires (fun h -> hs_inv s h /\ HS.r s = Client))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))

// (Idle) Server requests an handshake
val request: s:hs -> config -> ST bool
  (requires (fun h -> hs_inv s h /\ HS.r s = Server))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))

val invalidateSession: s:hs -> ST unit
  (requires (hs_inv s))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1)) // underspecified


(*** Outgoing ***)

type outgoing = // by default the state changes but not the epochs
  | OutIdle
  | OutSome:     rg:frange_any -> rbytes rg -> outgoing   // send a HS fragment
  | OutCCS                                              // signal new epoch (sending a CCS fragment first, up to 1.2)
  | OutFinished: rg:frange_any -> rbytes rg -> outgoing   // signal false start (if enabled)
  | OutComplete: rg:frange_any -> rbytes rg -> outgoing   // signal completion of current epoch
val next_fragment: s:hs -> ST outgoing
  (requires (hs_inv s))
  (ensures (fun h0 result h1 -> 
    let w0 = iT s Writer h0 in
    let w1 = iT s Writer h1 in
    let r0 = iT s Reader h0 in
    let r1 = iT s Reader h1 in
    hs_inv s h1 /\
    HyperHeap.modifies_one s.region h0 h1 /\
    r1 = r0 /\
    w1 = (if result = OutCCS then w0 + 1 else w0)  /\
    (is_OutComplete result ==> (w1 >= 0 /\ r1 = w1 /\ iT s Writer h1 >= 0 /\ completed (eT s Writer h1)))))
                                              (*why do i need this?*)


(*** Incoming ***)

type incoming = // the fragment is accepted, and...
  | InAck
  | InQuery: Cert.chain -> bool -> incoming
  | InCCS             // signal new epoch (only in TLS 1.3)
//| InFinished        // signal false state before TLS 1.3 (if enabled)
  | InComplete        // signal completion of current epoch
  | InError of error  // how underspecified should it be?
val recv_fragment: s:hs -> rg:Range.range { wider fragment_range rg } -> rbytes rg -> ST incoming
  (requires (hs_inv s))
  (ensures (fun h0 result h1 ->
    let w0 = iT s Writer h0 in
    let w1 = iT s Writer h1 in
    let r0 = iT s Reader h0 in
    let r1 = iT s Reader h1 in
    hs_inv s h1 /\
    HyperHeap.modifies_one s.region h0 h1 /\
    w1 = w0 /\
    r1 = (if result = InCCS then r0 + 1 else r0) /\
    (result = InComplete ==> r1 >= 0 /\ r1 = w1 /\ iT s Reader h1 >= 0 /\ completed (eT s Reader h1))))

val recv_ccs: s:hs -> ST incoming  // special case: CCS before 1p3
  (requires (hs_inv s)) // could require pv <= 1p2
  (ensures (fun h0 result h1 ->
    let w0 = iT s Writer h0 in
    let w1 = iT s Writer h1 in
    let r0 = iT s Reader h0 in
    let r1 = iT s Reader h1 in
    (is_InError result \/ is_InCCS result) /\
    hs_inv s h1 /\
    HyperHeap.modifies_one s.region h0 h1 /\
    w1 = w0 /\
    r1 = (if result = InCCS then r0 + 1 else r0)))

val authorize: s:hs -> Cert.chain -> ST incoming // special case: explicit authorize (needed?)
  (requires (hs_inv s))
  (ensures (fun h0 result h1 ->
    let w0 = iT s Writer h0 in
    let w1 = iT s Writer h1 in
    let r0 = iT s Reader h0 in
    let r1 = iT s Reader h1 in
    (is_InAck result \/ is_InError result) /\
    hs_inv s h1 /\
    HyperHeap.modifies_one s.region h0 h1 /\
    w1 = w0 /\
    r1 = r0 ))


(* working notes towards covering both TLS 1.2 and 1.3, with 0RTT and falsestart

type sendMsg (i:id) = // writer-indexed
  | OutHS:
       rg:frange_any ->
       fragment i rg rbytes rg -> // first write this Handshake fragment, then
       next:bool     ->           // signal increment of the writer index
       finished:bool ->           // enable false-start sending (after sending this 1st Finished)
       complete:bool ->           // signal completion (after sending this 2nd Finished)
       outbox
  | OutCCS  // before TLS 1.3; same semantics as above with explicit CCS (true, false, false)
  | OutIdle // nothing to do

(* e.g. in TLS 1.3 1RTT server sends OutHS (Finished ...) next
                   0RTT server sends OutHS (Finished ...) next finished  (if 0.5RTT is enabled)
                   then client sends OutHS (Finished ...) next complete

        in TLS 1.2 full server sends OutHS (Finished ...) finished
                   then client sends OutHS (Finished ...) complete
                   sending CCS implicitly says next  *)

type recvMsg =
  | InAck:
       next:bool ->      // signal increment of the reader index (before receiving the next packet)
       finished:bool ->  // enable false-start receiving (in TLS 1.2, as we accepted the 1st Finished)
       complete:bool ->  // signal completion (as we accepted the 2nd Finished)
       inbox
  | InQuery of Cert.chain * bool  // asks for authorization (all flags cleared; will have cases)
  | InError of error

(* e.g. in TLS 1.3 1RTT client accepts Finished: InAck next
                   0RTT client accepts Finished: InAck next finished  (if 0.5RTT is enabled)
                   then server accepts Finished: InAck next complete

        in TLS 1.2 full server accepts Finished: InAck finished
                   then client accepts Finished: InAck complete
                   accepting CCS returns:        InAck next  *)

Not sure how to handle 0RTT switches.
"end_of_early_data" is not HS.
On the receiving server side,
- After processing ClientHello, HS signals switch to 0RTT-HS (or jump to 1RTT_HS) receive keys.
- After processing Finished0, HS signals switch to 0RTT-AD
- After receiving EED, the record calls HS, which signals switch to 1RTT-HS [too early?]
- After receiving Finished, HS signals switch to 1RTT-AD.

[a proper use of index 0]

If we introduce dummy reverse streams (specified to remain empty), we still have to interpret
the first client receive++ as +=3.
What would trigger it? a locally-explicit CCS after accepting the ServerHello.


Otherwise the "next" mechanism seems fine; we just bump a ghost index
from 2 to 4 by the time we reach AD.

Also 1.3 trouble for sending HS-encrypted data immediately *after* next:
we can increment after sending ClientHello, but we don't have the epoch yet!

Ad hoc cases? or just an extra case?
In fact, ~ keeping a local, explicit CCS signal. *)
