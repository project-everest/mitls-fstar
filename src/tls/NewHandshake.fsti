module NewHandshake

(*** Updated Interface (Temp File) ***)

// current limitations: 
// - no abstract type for encrypted handshake traffic
// - no support for 0RTT and false-start
// - partnering between handshakes is static (needs fixing)

open FStar.Heap
open FStar.HyperHeap
//FIXME! Don't open so much ... gets confusing. Use module abbrevs instead
open FStar.Seq
open FStar.SeqProperties // for e.g. found
open FStar.Set  

open Platform.Error
open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
open Range
open HandshakeMessages
open HSCrypto
open StAE

module HH = FStar.HyperHeap
module MS = MonotoneSeq
module MR = FStar.Monotonic.RRef

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
val hsId: handshake -> Tot (i:id { is_stream_ae i }) //16-05-19 focus on TLS 1.3

//<expose for TestClient>
val ri : Type0
type b_log = bytes 
//or how about: 
//type log = list (m:bytes{exists ht d. m = messageBytes ht d})
type eph_s = option kex_s_priv
type eph_c = list kex_s_priv
type nego = {
     n_resume: bool;
     n_client_random: TLSInfo.random;
     n_server_random: TLSInfo.random;
     n_sessionID: option sessionID;
     n_protocol_version: protocolVersion;
     n_kexAlg: TLSConstants.kexAlg;
     n_aeAlg: TLSConstants.aeAlg;
     n_sigAlg: option TLSConstants.sigAlg;
     n_cipher_suite: cipherSuite;
     n_dh_group: option namedGroup;
     n_compression: option compression;
     n_extensions: negotiatedExtensions;
     n_scsv: list scsv_suite;
}                 

type hs_id = {
     id_cert: Cert.chain;
     id_sigalg: option sigHashAlg;
}

type ake = {
     ake_server_id: option hs_id;
     ake_client_id: option hs_id;
     ake_pms: bytes;
     ake_session_hash: bytes;
     ake_ms: bytes;
}

type session = {
     session_nego: nego;
     session_ake: ake;
}     

val prepareClientHello: config -> KeySchedule.ks -> HandshakeLog.log -> option ri -> option sessionID -> ST (hs_msg * bytes)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
val prepareServerHello: config -> KeySchedule.ks -> HandshakeLog.log -> option ri -> (hs_msg * bytes) -> ST (result (nego * (hs_msg * bytes)))
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
val processServerHello: c:config -> KeySchedule.ks -> HandshakeLog.log -> option ri -> ch -> (hs_msg * bytes) ->
                        ST (result (nego * option KeySchedule.recordInstance))
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))


//</expose for TestClient>

// relocate?
type fresh_subregion r0 r h0 h1 = fresh_region r h0 h1 /\ extends r r0

type epoch_region_inv (#i:id) (hs_rgn:rgn) (r:reader (peerId i)) (w:writer i) =
  disjoint hs_rgn (region w)                  /\
  parent (region w) <> FStar.HyperHeap.root    /\
  parent (region r) <> FStar.HyperHeap.root    /\
  parent hs_rgn = parent (parent (region w))  /\ //Grandparent of each writer is a sibling of the handshake
  disjoint (region w) (region r)              /\
  is_epoch_rgn (region w)                     /\ //they're all colored as epoch regions
  is_epoch_rgn (region r)                     /\
  is_epoch_rgn (parent (region w))            /\
  is_epoch_rgn (parent (region r))            /\
  is_hs_rgn hs_rgn                              //except for the hs_rgn, of course

abstract type epoch_region_inv' (#i:id) (hs_rgn:rgn) (r:reader (peerId i)) (w:writer i) =
  epoch_region_inv hs_rgn r w
  
module I = IdNonce

type epoch (hs_rgn:rgn) (n:TLSInfo.random) = 
  | Epoch: h: handshake ->
           r: reader (peerId (hsId h)) ->
           w: writer (hsId h) {epoch_region_inv' hs_rgn r w /\ I.nonce_of_id (hsId h) = n} 
	   -> epoch hs_rgn n
  // we would extend/adapt it for TLS 1.3,
  // e.g. to notify 0RTT/forwad-privacy transitions
  // for now epoch completion is a total function on handshake --- should be stateful

let reveal_epoch_region_inv_all (u:unit)
  : Lemma (forall i hs_rgn r w.{:pattern (epoch_region_inv' #i hs_rgn r w)}
	   epoch_region_inv' #i hs_rgn r w
	   <==>
   	   epoch_region_inv #i hs_rgn r w)
  = ()	   

let reveal_epoch_region_inv (#hs_rgn:rgn) (#n:TLSInfo.random) (e:epoch hs_rgn n) 
  : Lemma (let r = Epoch.r e in 
	   let w = Epoch.w e in 
	   epoch_region_inv hs_rgn r w)
  = ()

let writer_epoch (#hs_rgn:rgn) (#n:TLSInfo.random) (e:epoch hs_rgn n) 
  : Tot (w:writer (hsId (e.h)) {epoch_region_inv hs_rgn (Epoch.r e) w})
  = Epoch.w e

let reader_epoch (#hs_rgn:rgn) (#n:TLSInfo.random) (e:epoch hs_rgn n) 
  : Tot (r:reader (peerId (hsId (e.h))) {epoch_region_inv hs_rgn r (Epoch.w e)})
  = match e with | Epoch h r w -> r //16-05-20 Epoch.r e failed.

(* The footprint just includes the writer regions *)
abstract let epochs_inv (#r:rgn) (#n:TLSInfo.random) (es: seq (epoch r n)) =
  forall (i:nat { i < Seq.length es })
    (j:nat { j < Seq.length es /\ i <> j}).{:pattern (Seq.index es i); (Seq.index es j)}
    let ei = Seq.index es i in
    let ej = Seq.index es j in
    parent (region ei.w) = parent (region ej.w) /\  //they all descend from a common epochs sub-region of the connection
    disjoint (region ei.w) (region ej.w)           //each epoch writer lives in a region disjoint from the others

abstract let epochs_inv' (#r:rgn) (#n:TLSInfo.random) (es: seq (epoch r n)) = epochs_inv es

let epochs (r:rgn) (n:TLSInfo.random) = es: seq (epoch r n) { epochs_inv' es }

let reveal_epochs_inv' (u:unit)
  : Lemma (forall (r:rgn) (#n:TLSInfo.random) (es:seq (epoch r n)). {:pattern (epochs_inv' es)}
	     epochs_inv' es
	     <==>
	     epochs_inv es)
  = ()

// internal stuff: state machine, reader/writer counters, etc.
// (will take other HS fields as parameters)
val handshake_state : role -> Type0
(* #reset-options "--z3timeout 3 --initial_fuel 2 --max_fuel 2 --initial_ifuel 2 --max_ifuel 2" *)

let resume_id (r:role) = o:option sessionID{r=Server ==> o=None}

type hs =
  | HS: #region: rgn { is_hs_rgn region } ->
              r: role ->
         resume: resume_id r ->
            cfg: config ->
          nonce: TLSInfo.random ->  // unique for all honest instances; locally enforced; proof from global HS invariant? 
            log: MS.i_seq region (epoch region nonce) epochs_inv ->  // append-only, monotonic log of epochs
          state: rref region (handshake_state r)  ->       // opaque, subject to invariant
             hs


(* the handshake internally maintains epoch 
   indexes for the current reader and writer *)

let logT (s:hs) (h:HyperHeap.t) = MS.i_sel h s.log

let stateType (s:hs) = epochs s.region s.nonce * handshake_state (HS.r s)

let stateT (s:hs) (h:HyperHeap.t) : stateType s = (logT s h, sel h s.state)

let non_empty h s = Seq.length (logT s h) > 0

let logIndex (#t:Type) (log: seq t) = n:int { -1 <= n /\ n < Seq.length log }

// returns the current index in the log for reading or writing, or -1 if there is none.
// depends only on the internal state of the handshake
val iT0: s:hs -> rw:rw -> st:stateType s -> Tot (logIndex (fst st))
let iT s rw h = iT0 s rw (stateT s h) 

//A framing lemma with a very trivial proof, because of the way stateT abstracts the state-dependent parts
let frame_iT_trivial  (s:hs) (rw:rw) (h0:HH.t) (h1:HH.t) 
  : Lemma (stateT s h0 = stateT s h1
           ==> iT s rw h0 = iT s rw h1) 
  = ()	                               

//Here's a framing on stateT connecting it to the region discipline
let frame_stateT  (s:hs) (rw:rw) (h0:HH.t) (h1:HH.t) (mods:Set.set rid)
  : Lemma (requires HH.modifies_just mods h0 h1
		    /\ Map.contains h0 s.region
		    /\ not (Set.mem s.region mods))
          (ensures stateT s h0 = stateT s h1)
  = ()	                               

//This is probably the framing lemma that a client of this module will want to use
let frame_iT  (s:hs) (rw:rw) (h0:HH.t) (h1:HH.t) (mods:Set.set rid)
  : Lemma (requires HH.modifies_just mods h0 h1
		    /\ Map.contains h0 s.region
		    /\ not (Set.mem s.region mods))
          (ensures stateT s h0 = stateT s h1
		   /\ iT s rw h0 = iT s rw h1)
  = frame_stateT s rw h0 h1 mods;
    frame_iT_trivial s rw h0 h1
    
// returns the epoch for reading or writing
let eT s rw (h:HyperHeap.t { iT s rw h >= 0 }) = Seq.index (logT s h) (iT s rw h)

let readerT s h = eT s Reader h 
let writerT s h = eT s Writer h

// this function increases (how to specify it once for all?)
val i: s:hs -> rw:rw -> ST int 
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> h0 = h1 /\ i = iT s rw h1))

val processServerHelloDone: cfg:config -> nego:nego -> ks:KeySchedule.ks -> log:HandshakeLog.log ->
    			    list (hs_msg*bytes) -> list (hs_msg * bytes) -> ST (result (list (hs_msg * bytes)))
  (requires (fun h -> nego.n_protocol_version <> TLS_1p3))
  (ensures (fun h0 i h1 -> True))
val prepareClientFinished: KeySchedule.ks -> HandshakeLog.log -> ST (hs_msg * bytes)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
val processServerFinished: KeySchedule.ks -> HandshakeLog.log -> (hs_msg * bytes) -> ST (result bytes)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

val processServerFinished_13: cfg:config -> n:nego -> ks:KeySchedule.ks -> log:HandshakeLog.log ->
    			      list (hs_msg*bytes) -> ST (result (list (hs_msg * bytes) * bytes * KeySchedule.recordInstance))
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))


// name-clashing
// let reader s = i s Reader
// let writer s = i s Reader


let forall_epochs (hs:hs) h (p:(epoch hs.region hs.nonce -> Type)) = 
  (let es = logT hs h in
   forall (i:nat{i < Seq.length es}).{:pattern (Seq.index es i)} p (Seq.index es i))
     
(* //vs modifies clauses? *)
(* let unmodified_epochs s h0 h1 =  *)
(*   forall_epochs s h0 (fun e ->  *)
(*     let rs = regions e in  *)
(*     (forall (r:rid{Set.mem r rs}).{:pattern (Set.mem r rs)} Map.sel h0 r = Map.sel h1 r)) *)

//epochs in h1 extends epochs in h0 by one 
let fresh_epoch h0 s h1 =
  let es0 = logT s h0 in 
  let es1 = logT s h1 in 
  Seq.length es1 > 0 &&
  es0 = Seq.slice es1 0 (Seq.length es1 - 1)

let latest h (s:hs{Seq.length (logT s h) > 0}) = // accessing the latest epoch
 let es = logT s h in
 Seq.index es (Seq.length es - 1)

// separation policy: the handshake mutates its private state, 
// only depends on it, and only extends the log with fresh epochs.


// placeholder, to be implemented as a stateful property.
assume val completed: #region:rgn -> #nonce:TLSInfo.random -> epoch region nonce -> Type0

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
 
assume val hs_invT : s:hs -> epochs:seq (epoch s.region s.nonce) -> handshake_state (HS.r s) -> Type0

let hs_inv (s:hs) (h: HyperHeap.t) = 
  hs_invT s (logT s h) (sel h (HS.state s))  //An abstract invariant of HS-internal state
  /\ MS.i_contains s.log h                    //Nothing deep about these next two, since they can always 
  /\ HyperHeap.contains_ref s.state h                 //be recovered by 'recall'; carrying them in the invariant saves the trouble

//TODO: need a lemma to frame hs_inv across updates that don't clash with HS.region
//TODO: need a lemma to frame a write to one epoch across the state of the other epochs

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
val init: r0:rid -> r: role -> cfg:config -> resume: resume_id r -> 
  ST hs
  (requires (fun h -> True))
  (ensures (fun h0 s h1 ->
    modifies Set.empty h0 h1 /\
    fresh_subregion r0 (HS.region s) h0 h1 /\
    hs_inv s h1 /\
    HS.r s = r /\
    HS.resume s = resume /\
    HS.cfg s = cfg /\
    logT s h1 = Seq.createEmpty ))

let mods s h0 h1 = 
  HyperHeap.modifies_one s.region h0 h1
  
let modifies_internal h0 s h1 =
    hs_inv s h1 /\
    mods s h0 h1 /\ 
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

// payload of a handshake fragment, to be made opaque eventually
type message (i:id) = (| rg: frange i & rbytes rg |)

// What the HS asks the record layer to do, in that order.
type outgoing (i:id) (* initial index *) = 
  | Outgoing: 
      send_first: option (message i) -> // HS fragment to be sent;  (with current id)
      send_ccs  : bool               -> // CCS fragment to be sent; (with current id)
      next_keys : bool               -> // the writer index increases;
      complete  : bool               -> // the handshake is complete!
      outgoing i 
  | OutError: error -> outgoing i       // usage? in case something goes wrong when preparing messages. 

let out_next_keys (#i:id) (r:outgoing i) = is_Outgoing r && Outgoing.next_keys r
let out_complete (#i:id) (r:outgoing i)  = is_Outgoing r && Outgoing.complete r

let next_fragment_ensures (#i:id) (s:hs) h0 (result:outgoing i) h1 = 
    let es = logT s h0 in
    let w0 = iT s Writer h0 in
    let w1 = iT s Writer h1 in
    let r0 = iT s Reader h0 in
    let r1 = iT s Reader h1 in
    hs_inv s h1 /\
    mods s h0 h1 /\
    r1 == r0 /\
//  w1 == (match result with | Outgoing _ _ true _ -> w0 + 1 | _ -> w0 ) /\
    w1 == (if out_next_keys result then  w0 + 1 else w0 ) /\
    (b2t (out_complete result) ==> w1 >= 0 /\ r1 = w1 /\ iT s Writer h1 >= 0 /\ completed (eT s Writer h1)) 

val next_fragment: i:id -> s:hs -> ST (outgoing i)
  (requires (fun h0 -> 
    let es = logT s h0 in
    let j = iT s Writer h0 in 
    hs_inv s h0 /\
    (if j = -1 then i = noId else let e = Seq.index es j in i = hsId e.h)   
  ))
  (ensures (next_fragment_ensures s))

//<expose for TestClient>
val parseHandshakeMessages : option protocolVersion -> option kexAlg -> buf:bytes -> Tot  (result (rem:bytes * list (hs_msg * bytes)))
//</expose for TestClient>


(*** Incoming ***)

type incoming = 
  // the fragment is accepted, and...
  | InAck: 
      next_keys : bool -> // the reader index increases;
      complete  : bool -> // the handshake is complete!
      incoming

  | InQuery: Cert.chain -> bool -> incoming // could be part of InAck if no explicit user auth
  | InError: error -> incoming // how underspecified should it be?

let in_next_keys (r:incoming) = is_InAck r && InAck.next_keys r
let in_complete (r:incoming)  = is_InAck r && InAck.complete r

let recv_ensures (s:hs) (h0:HyperHeap.t) (result:incoming) (h1:HyperHeap.t) = 
    let w0 = iT s Writer h0 in
    let w1 = iT s Writer h1 in
    let r0 = iT s Reader h0 in
    let r1 = iT s Reader h1 in
    hs_inv s h1 /\
    mods s h0 h1 /\
    w1 == w0 /\
    r1 == (if in_next_keys result then r0 + 1 else r0) /\
    (b2t (in_complete result) ==> r1 >= 0 /\ r1 = w1 /\ iT s Reader h1 >= 0 /\ completed (eT s Reader h1))

val recv_fragment: s:hs -> #i:id -> message i -> ST incoming
  (requires (hs_inv s))
  (ensures (recv_ensures s))

val recv_ccs: s:hs -> ST incoming  // special case: CCS before 1p3; could merge with recv_fragment
  (requires (hs_inv s)) // could require pv <= 1p2
  (ensures (fun h0 result h1 ->
    ~(is_InQuery result) /\ recv_ensures s h0 result h1 ))

val authorize: s:hs -> Cert.chain -> ST incoming // special case: explicit authorize (needed?)
  (requires (hs_inv s))
  (ensures (fun h0 result h1 ->
    (is_InAck result \/ is_InError result) /\ recv_ensures s h0 result h1 ))
    

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
