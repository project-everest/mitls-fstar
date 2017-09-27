module Connection

// Connections are top-level instances of TLS clients and servers

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
// JP: please stop using opening so much stuff in scope srsly
open FStar.Seq
 // for e.g. found
//open FStar.Set
 
open FStar.Bytes
open Platform.Error

open TLSError
open TLSConstants
open TLSInfo
  
open Range

open Epochs
open Handshake

module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap

// using also Range, DataStream, TLSFragment, Record

(*
type tlsState = 
//| Early       // TLS 1.3 0RTT in 
//| KeyUpdate   // TLS 1.3 after sending first KeyUpdate
//| Regeno      // TLS old after sending CCS
//| FalseStart  // TLS old client, between finished.
  | BC          // Before Completion of handshake 
  | AD          // Application Data (duplex), once the connection is established
  | Half of rw  // the other direction is closed (reachable from BC?)
  | Close 
// translation:
// BC ~ Ctrl Ctrl
// AD ~ Open Open
// Half Read ~ Open Closed
// Close ~ Closed Closed
*)

type halfState =
  | Ctrl
  | Open
  | Closed
type tlsState = halfState * halfState // reader/writer

let string_of_halfState = function
  | Ctrl -> "Ctrl"
  | Open -> "Open"
  | Closed -> "Closed"
let string_of_state (r,w) =
  string_of_halfState r^"/"^string_of_halfState w

type c_rgn = r:TLSConstants.rgn { HH.disjoint r TLSConstants.tls_region } 

(*
 * AR: changing the type of state from rref to ref, with region captured in the refinement.
 *)
noeq type connection = | C:
  #region: c_rgn ->
  hs:      hs {extends (region_of hs) region /\ is_hs_rgn (region_of hs)} (* providing role, config, and uid *) ->
  tcp:     Transport.t ->
  recv: ref Record.input_state{recv.id = region} -> // added for buffering non-blocking reads
  state:   ref tlsState {state.id = region} -> 
  connection

// 17-04-08 helpful or not? 
let c_role c = Handshake.role_of c.hs
let c_nonce c = Handshake.random_of c.hs
let c_cfg c = Handshake.config_of c.hs
let c_resume c = Handshake.resumeInfo_of c.hs
let c_log c = Handshake.epochs_of c.hs

(* val reader_epoch: #region:rgn -> #nonce:_ -> e:epoch region nonce -> Tot (StAE.reader (peerId(hsId e.h))) *)
(* let reader_epoch #region #peer e = Epoch?.r e *)

(* val writer_epoch: #region:rgn -> #nonce:_ -> e:epoch region nonce -> Tot (StAE.writer (hsId e.h)) *)
(* let writer_epoch #region #peer e = Handshake.writer_epoch e *)

#set-options "--initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0"
type st_inv c h = hs_inv (C?.hs c) h

//TODO: we will get the property that at most the current epochs' logs are extended, by making them monotonic in HS
val epochs : c:connection -> h:HyperStack.mem -> GTot (es:seq (epoch (region_of c.hs) (random_of c.hs)){
  Epochs.epochs_inv es /\ es == logT c.hs h
})
let epochs c h = logT c.hs h


//16-05-30 unused?
val frame_epochs: c:connection -> h0:HyperStack.mem -> h1:HyperStack.mem -> Lemma
  (requires (
    Map.contains (HyperStack.HS?.h h0) (region_of c.hs) /\ 
    equal_on (Set.singleton (region_of c.hs)) (HyperStack.HS?.h h0) (HyperStack.HS?.h h1)))
  (ensures (epochs c h0 == epochs c h1))
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

val equal_on_disjoint: 
  s1:Set.set rid -> 
  s2:Set.set rid{disjoint_regions s1 s2} -> 
  r:rid{Set.mem r s1} -> 
  h0:HyperStack.mem -> h1:HyperStack.mem{modifies (Set.singleton r) h0 h1} -> Lemma (equal_on s2 (HyperStack.HS?.h h0) (HyperStack.HS?.h h1))
let equal_on_disjoint s1 s2 r h0 h1 = ()

