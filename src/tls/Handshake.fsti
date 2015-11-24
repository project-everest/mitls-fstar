module Handshake

// Outlining the new stateful Handshake interface
// So far, this reflects the HS visible transitions & local state machine
// ---not yet agreement with peer connections---but this exposes enough details
// to specify it (as the existence of a peer Connection such that ...)

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found

open Platform.Error
open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
open Range
open StatefulLHAE

// We use SessionInfo as unique session indexes.
// We tried using instead hs, but this creates circularities
// We'll probably need a global log to reason about them.
// We should probably do the same in the session store.

type error = alertDescription * string

type handshake = 
  | Fresh of SessionInfo
  | Resumed of abbrInfo * SessionInfo //changed: was hs * seq epoch (creating cycle)

// extracts a transport key identifier from a handshake record
val hs_id: handshake -> Tot id

type handshake_state // internal 

open FStar.Set  

opaque type disjoint_regions (s1:set rid) (s2:set rid) = 
       forall x y. {:pattern (Set.mem x s1); (Set.mem y s2)} (Set.mem x s1 /\ Set.mem y s2) ==> disjoint x y

opaque type epoch_region_inv (#i:_) (r:reader i) (w:writer i) =
  disjoint_regions (regions_of r) (regions_of w)
  
type epoch (parent:rid) =
  | Epoch: h: handshake ->
           r: reader (hs_id h) ->
           w: writer (hs_id h) 
           { extends (region r) parent /\ 
             extends (region w) parent /\ 
             epoch_region_inv r w }
       ->  epoch parent
  // we would extend/adapt it for TLS 1.3,
  // e.g. to notify 0RTT/forwad-privacy transitions
  // for now epoch completion is a total function on handshake --- should be stateful

//15-09-10 why do I need an explicit val here? this is forbidden in .fsti...
// for now rewriting as a spec.
//val regions_epoch: #region:rid -> epoch #region -> Tot (rid * rid)
//let regions_epoch region (Epoch h r w) = StatefulLHAE.reader_region r, StatefulLHAE.writer_region w

(* let op_HatAtPlus (r:rid) (rs:FStar.Set.set rid) = Set.union (Set.singleton r) rs *)
(* let op_HatAtHat (r:rid) (s:rid) = Set.union (Set.singleton r) (Set.singleton s) *)


let regions (#p:rid) (e:epoch p) = 
  union (singleton (region e.r))
            (union (singleton (peer_region e.r))
                       (union (singleton (region e.w))
                                  (singleton (peer_region e.w))))


//15-09-23 any abstract way to deal with pairwise disjointness? 
//15-09-23 test how we apply this assumption.
opaque type epochs_footprint (#region:rid) (es: seq (epoch region)) =
  forall (i:nat { i < Seq.length es }).
  forall (j:nat { j < Seq.length es /\ i <> j}).{:pattern (Seq.index es i); (Seq.index es j)}
    let ei = Seq.index es i in
    let ej = Seq.index es j in
      disjoint_regions (regions ei) (regions ej)

type epochs (r:rid) = es: seq (epoch r) { epochs_footprint es }

type hs =
  | HS: #region: rid ->
        r:role ->
        resume: option (sid:sessionID { r = Client }) ->
        cfg:config ->
        id: random ->  // unique for all honest instances; locally enforced; proof from global HS invariant? 
        log: rref region (epochs region) ->  // append-only 15-09-23 use monotonic? helpful for proofs? 
        state: rref region handshake_state  ->  // opaque, subject to invariant
        hs

type forall_epochs (hs:hs) h (p:(epoch (hs.region) -> Type)) = 
  (let es = sel h hs.log in 
   forall (i:nat{i < Seq.length es}).{:pattern (Seq.index es i)} p (Seq.index es i))
     
//vs modifies clauses?
opaque type unmodified_epochs s h0 h1 = 
  forall_epochs s h0 (fun e -> 
    let rs = regions e in 
    (forall (r:rid{Set.mem r rs}).{:pattern (Set.mem r rs)} Map.sel h0 r = Map.sel h1 r))

//epochs in h1 extends epoochs in h0 by one 
let fresh_epoch h0 s h1 =
  let es0 = sel h0 s.log in
  let es1 = sel h1 s.log in 
  Seq.length es1 > 0 &&
  es0 = Seq.slice es1 0 (Seq.length es1 - 1)

// 15-09-10 explicit val needed to express the trivial precondition
// 15-11-23: NS, not necessarily
(* val latest: h:HyperHeap.t -> s:hs { Seq.length (sel h s.log) > 0 } -> GTot (epoch s.region) *)
let latest h (s:hs{Seq.length (sel h s.log) > 0}) = // accessing the latest epoch
 let es = sel h (HS.log s) in
 Seq.index es (Seq.length es - 1)

// separation policy: the handshake mutates its private state, only depend on it, and only extends the log with fresh epochs.

assume type Completed: #region:rid -> epoch region -> Type

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
 
type hs_invT (s:hs) (epochs:seq (epoch (HS.region s))) : handshake_state -> Type
 
type hs_inv (s:hs) (h: HyperHeap.t) = hs_invT s (sel h (HS.log s)) (sel h (HS.state s)) 


(* ----------------- Control Interface ---------------------*)

// relocate?
type fresh_subregion r0 r h0 h1 = fresh_region r h0 h1 /\ extends r r0

// Create instance for a fresh connection, with optional resumption for clients
val init: r0:rid -> r: role -> cfg:config -> resume: option (sid: sessionID { r = Client })  ->
  ST hs
  (requires (fun h -> True))
  (ensures (fun h0 s h1 ->
    modifies Set.empty h0 h1 /\
    fresh_subregion r0 (HS.region s) h0 h1 /\
    hs_inv s h1 /\
    HS.r s = r /\
    HS.resume s = resume /\
    HS.cfg s = cfg /\
    sel h1 (HS.log s) = Seq.createEmpty ))
    
type modifies_internal h0 s h1 =
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

(* --------------------Network Interface -------------------*)


type outgoing = // by default the state changes but not the epochs
  | OutIdle
  | OutSome:     rg:Range.range { Wider DataStream.fragment_range rg } -> rbytes rg -> outgoing
  | OutCCS                // log += Epoch if first
  | OutFinished: rg:Range.range { Wider DataStream.fragment_range rg } -> rbytes rg -> outgoing
  | OutComplete: rg:Range.range { Wider DataStream.fragment_range rg } -> rbytes rg -> outgoing // log += Complete
let non_empty h s = Seq.length (sel h s.log) > 0
val next_fragment: s:hs -> ST outgoing
  (requires (hs_inv s))
  (ensures (fun h0 result h1 ->
    hs_inv s h1 /\
    HyperHeap.modifies_one s.region h0 h1 /\
    // preserves its invariant, modifies only its own region, and...
       (result = OutCCS       ==> fresh_epoch h0 s h1) /\
       (result <> OutCCS       ==> modifies_internal h0 s h1) /\
       (is_OutComplete result ==> (non_empty h1 s /\ Completed (latest h1 s)))))

type incoming = // the fragment is accepted, and...
  | InAck
  | InVersionAgreed of ProtocolVersion
  | InQuery of Cert.chain * bool
  | InFinished
  | InComplete        // log += Complete
  | InError of error  // log += Error
val recv_fragment: s:hs -> rg:Range.range { Wider DataStream.fragment_range rg } -> rbytes rg -> ST incoming
  (requires (hs_inv s)) //removed:  (fun h -> Seq.length (sel h (HS.log s)) > 0))
  (ensures (fun h0 result h1 ->
    hs_inv s h1 /\
    modifies_internal h0 s h1
    /\ (result = InComplete ==> non_empty h1 s /\ Completed (latest h1 s))))

val authorize: s:hs -> Cert.chain -> ST incoming
  (requires (hs_inv s))
  (ensures (fun h0 result h1 ->
    // preserves its invariant, modifies only its own region, and...
    modifies_internal h0 s h1 ))

type incomingCCS =
  | InCCSAck            // log += Epoch if first
  | InCCSError of error // log += Error
val recv_ccs: s:hs -> rg:Range.range { Wider DataStream.fragment_range rg } -> rbytes rg -> ST incomingCCS
  (requires (hs_inv s))
  (ensures (fun h0 result h1 ->
    // preserves its invariant, modifies only its own region, and...
    hs_inv s h1 /\
    fresh_epoch h0 s h1 ))

val getMinVersion: hs -> Tot ProtocolVersion

// val negotiate: list<'a> -> list<'a> -> option<'a> when 'a:equality
