module Connection

// 2015-08-25 largely rewritten to implement both stateful dispatch and TLS

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found
open FStar.Set
 
open Platform.Bytes
open Platform.Error
open Platform.Tcp

open TLSError
open TLSConstants
open TLSInfo
  
open Range
open Handshake    // via its interface

// using also Alert, Range, DataStream, TLSFragment, Record


// internal state machine (one for reading, one for writing; a bit much)
// TODO make it private? write invariant, to cut out cases in code
// e.g. , reading, and writing transitions are tighly related
// TODO recheck large logical invariants GState in Dispatch.fs7

// dispatch records the *record* protocol version (TLS 1.0 when using TLS 1.3)
type dispatch =
  | Init
//  | FirstHandshake of protocolVersion (* bound by ServerHello's inner pv *)
  | Finishing
  | Finished
  | Open
  | Closing of (* protocolVersion * *) string (* write-only, while sending a fatal alert *)
  | Closed

// revised from 2x dispatch 
type tlsState = 
//| Early       // TLS 1.3 0RTT in 
//| KeyUpdate   // TLS 1.3 after sending first KeyUpdate
//| Regeno      // TLS old after sending CCS
//| FalseStart  // TLS old client, between finished.
  | BC          // Before Completion of handshake 
  | AD          // Application Data (duplex), once the connection is established
  | Half of rw  // the other direction is closed (reachable from BC?)
  | Close 

type connection = | C:
  #region: rid{disjoint region tls_region} ->
  hs:      hs {extends (HS.region hs) region /\ is_hs_rgn (HS.region hs)} (* providing role, config, and uid *) ->
  alert:   Alert.state  { extends (Alert.region alert) region /\ HS.region hs <> Alert.region alert } (* review *) ->
  tcp:     networkStream ->
  state:   rref region tlsState -> 
  connection

let c_role c   = c.hs.r
let c_nonce c  = c.hs.nonce
let c_cfg c    = c.hs.cfg
let c_resume c = c.hs.resume
let c_log c    = c.hs.log

val reader_epoch: #region:rgn -> #nonce:_ -> e:epoch region nonce -> Tot (StAE.reader (peerId(hsId e.h)))
let reader_epoch #region #peer e = Epoch.r e

val writer_epoch: #region:rgn -> #nonce:_ -> e:epoch region nonce -> Tot (StAE.writer (hsId e.h))
let writer_epoch #region #peer e = Epoch.w e

(*** 
     WE WILL FOCUS VERIFICATION ON StreamAE and TLS-1.3 FOR NOW.
     Ignores StatefulLHAE, which needs to be upgraded
 ***)
#set-options "--initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0"
type st_inv c h = hs_inv (C.hs c) h 

//TODO: we will get the property that at most the current epochs' logs are extended, by making them monotonic in HS
val epochs : c:connection -> h:HyperHeap.t -> GTot (es:seq (epoch (HS.region c.hs) (HS.nonce c.hs)){
  Handshake.epochs_inv es /\ es = HyperHeap.sel h c.hs.log
})
let epochs c h = sel h (HS.log c.hs)

val frame_epochs: c:connection -> h0:HyperHeap.t -> h1:HyperHeap.t -> Lemma
  (requires (Map.contains h0 (HS.region c.hs)
             /\ equal_on (Set.singleton (HS.region c.hs)) h0 h1))
  (ensures (epochs c h0 = epochs c h1))
let frame_epochs c h0 h1 = ()

let epoch_i c h i = Seq.index (epochs c h) i

(** should go to Handshake *)

(*
   Aiming to prove that sending a message preserves the
   invariant for all the epochs in a connection.

   A connection c encapsulates the state machine of a connection.
   It contains within an hs, the handshake state machine.

   The hs.log field is a ref to a seq of epochs all residing in
   regions with the same parent region.

   Each epoch is an (h, r, w) triple,
     where the r:StatefulLHAE.reader
               w:StatefulLHAE.writer
     are each one end of a key pair (their peers are in a some other connection).
     
     The h field is the state of the handshake state machine and is
     irrelevant for this framing lemma.

   In the lemma below, we modify the writer of epoch j
   and aim to show that the invariant of some arbitrary k is preserved.
   
   Later, we generalize over k, using the ghost_lemma combinator to introduce the quantifier.
*)

val equal_on_disjoint: s1:set rid -> s2:set rid{disjoint_regions s1 s2} -> r:rid{mem r s1} -> h0:t -> h1:t{modifies (Set.singleton r) h0 h1} -> Lemma (equal_on s2 h0 h1)
let equal_on_disjoint s1 s2 r h0 h1 = ()

