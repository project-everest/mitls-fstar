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
open StatefulLHAE // via its interface
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
  #region: rid ->
  peer:   rid{disjoint region peer} ->
  hs:      hs { extends (HS.region hs) region /\ extends (HS.peer hs) peer } (* providing role, config, and uid *) ->
  alert:   Alert.state  { extends (Alert.region alert) region /\ HS.region hs <> Alert.region alert } (* review *) ->
  tcp:     networkStream ->
  state: rref region tlsState -> 
  connection

let c_role c   = c.hs.r
let c_id c     = c.hs.id
let c_cfg c    = c.hs.cfg
let c_resume c = c.hs.resume
let c_log c    = c.hs.log


(*** top-level invariant ***) 

// we'll rely on the invariant to show we picked the correct index

inline let seq_forall (#a:Type) (p: a -> Type) (s:seq a) =
  forall (j: nat { j < Seq.length s }).{:pattern (Seq.index s j)} p (Seq.index s j)

let test_1 (p:nat -> Type) (s:seq nat { seq_forall p s }) = assert(p 12 ==> seq_forall p (snoc s 12))
let test_2 (p:nat -> Type) (s:seq nat { seq_forall p s }) (j:nat { j < Seq.length s }) =  let x = Seq.index s j in assert(p x)
//let test_3 (p:nat -> Type) (s:seq nat { seq_forall p s }) x = assert(SeqProperties.mem x s ==> p x)

(* usage? how to prove this lemma?  val exercise_seq_forall: #a:Type
-> p: (a -> Type) -> s:seq a -> x: a -> Lemma (u:unit { (seq_forall p
s /\ p x) ==> seq_forall p (snoc s x)}) *)

val reader_epoch: #region:rid -> #peer:rid -> e:epoch region peer -> Tot (reader (peerId(hsId e.h)))
let reader_epoch #region #peer (Epoch h r w) = r

val writer_epoch: #region:rid -> #peer:rid -> e:epoch region peer -> Tot (writer (hsId e.h))
let writer_epoch #region #peer (Epoch h r w) = w

type epoch_inv (#region:rid) (#peer:rid) (h:HyperHeap.t) (e: epoch region peer) = 
  st_dec_inv #(peerId (hsId e.h)) (reader_epoch e) h /\ 
  st_enc_inv #(hsId e.h) (writer_epoch e) h
  
type epochs_inv c h = 
  seq_forall (epoch_inv #(HS.region c.hs) #(HS.peer c.hs) h) (sel h c.hs.log) /\ 
  Handshake.hs_footprint_inv c.hs h
  
type st_inv c h = 
  hs_inv (C.hs c) h /\
  epochs_inv c h 

val test_st_inv: c:connection -> j:nat -> ST (epoch (HS.region c.hs) (HS.peer c.hs))
  (requires (fun h -> st_inv c h /\ j < Seq.length (sel h (HS.log c.hs))))
  (ensures (fun h0 e h1 -> 
    h0 == h1 /\ 
    st_dec_inv #(peerId (hsId e.h)) (reader_epoch e) h1 /\ 
    st_enc_inv #(hsId e.h) (writer_epoch e) h1))

let test_st_inv c j = 
  let h = ST.get() in
  let epochs = !c.hs.log in
  Seq.index epochs j

// we should have st_env_inv & st_dec_inv for all epochs, all the time. 
// + the property that at most the current epochs' logs are extended.
val epochs : c:connection -> h:HyperHeap.t -> GTot (es:seq (epoch (HS.region c.hs) (HS.peer c.hs)){epochs_footprint es /\ es = HyperHeap.sel h c.hs.log})

//val epochs : c:connection -> h:HyperHeap.t -> GTot (Handshake.epochs (HS.region c.hs) (HS.peer c.hs))
let epochs c h = sel h (HS.log c.hs)


val frame_epochs: c:connection -> h0:HyperHeap.t -> h1:HyperHeap.t -> Lemma
  (requires (Map.contains h0 (HS.region c.hs)
             /\ equal_on (Set.union (Set.singleton (HS.region c.hs))
      				 (Set.singleton (HS.peer c.hs))) h0 h1))
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

//Move this to the library 
val ghost_lemma2: #a:Type -> #b:Type -> #p:(a -> b -> GTot Type) -> #q:(a -> b -> unit -> GTot Type) 
		       -> =f:(x:a -> y:b -> Ghost unit (p x y) (q x y)) 
		       -> Lemma (forall (x:a) (y:b). p x y ==> q x y ())
let ghost_lemma2 (#a:Type) (#b:Type) (#p:(a -> b -> Type)) (#q:(a -> b -> unit -> Type)) f = 
  let f : x:a -> Lemma (forall (y:b). (p x y ==> q x y ())) = 
    fun x -> ghost_lemma (f x) in
  qintro f

val frame_writer_epoch_k: c:connection -> h0:HyperHeap.t -> h1:HyperHeap.t -> j:nat -> k:nat -> Ghost unit 
  (requires
    epochs_inv c h0 /\
    (let es = epochs c h0 in
     let hs_r = HS.region c.hs in 
      Map.contains h0 hs_r
      /\ k < Seq.length es
      /\ j < Seq.length es 
      /\ (let wr_j = writer_epoch (Seq.index es j) in
           modifies (Set.singleton (region wr_j)) h0 h1 
         /\ st_enc_inv wr_j h1)))
  (ensures (fun _ -> 
                epochs c h0 = epochs c h1
              /\ k < Seq.length (epochs c h1)
              /\ epoch_inv h1 (epoch_i c h1 k)
))
let frame_writer_epoch_k c h0 h1 j k =
  let es = epochs c h0 in
  let hs_r = HS.region c.hs in
  let e_j = Seq.index es j in
  let e_k = Seq.index es k in
  let wr_j = writer_epoch e_j in
  if k<>j
  then (equal_on_disjoint (regions e_j) (regions e_k) (region wr_j) h0 h1;
        frame_st_enc_inv #(hsId e_k.h) (writer_epoch e_k) h0 h1;
        frame_st_dec_inv #(peerId (hsId e_k.h)) (reader_epoch e_k) h0 h1)
  else (let r_k = reader_epoch e_k in
        equal_on_disjoint (regions_of wr_j) (regions_of (reader_epoch e_k)) (region wr_j) h0 h1;
        frame_st_dec_inv #(peerId (hsId e_k.h)) (reader_epoch e_k) h0 h1)

opaque type witness (#a:Type) (x:a) = True
val frame_writer_epoch: c:connection -> h0:HyperHeap.t -> h1:HyperHeap.t -> Lemma 
  (requires
    epochs_inv c h0 /\
    (exists (j:nat). {:pattern (witness j)}
      (let es = epochs c h0 in
       let hs_r = HS.region c.hs in 
       Map.contains h0 hs_r
       /\ j < Seq.length es 
       /\ (let wr_j = writer_epoch (Seq.index es j) in
           modifies (Set.singleton (region wr_j)) h0 h1 
          /\ st_enc_inv wr_j h1))))
  (ensures (epochs c h0 = epochs c h1
            /\ epochs_inv c h1))
let frame_writer_epoch c h0 h1 = ghost_lemma2 (frame_writer_epoch_k c h0 h1)

val frame_reader_epoch_k: c:connection -> h0:HyperHeap.t -> h1:HyperHeap.t -> j:nat -> k:nat -> Ghost unit 
  (requires
    epochs_inv c h0 /\
    (let es = epochs c h0 in
     let hs_r = HS.region c.hs in 
      Map.contains h0 hs_r
      /\ k < Seq.length es
      /\ j < Seq.length es 
      /\ (let rd_j = reader_epoch (Seq.index es j) in
           modifies (Set.singleton (region rd_j)) h0 h1 
         /\ st_dec_inv rd_j h1)))
  (ensures (fun _ -> 
                epochs c h0 = epochs c h1
              /\ k < Seq.length (epochs c h1)
              /\ epoch_inv h1 (epoch_i c h1 k)))
let frame_reader_epoch_k c h0 h1 j k =
  let es = epochs c h0 in
  let hs_r = HS.region c.hs in
  let e_j = Seq.index es j in
  let e_k = Seq.index es k in
  let rd_j = reader_epoch e_j in
  if k<>j
  then (equal_on_disjoint (regions e_j) (regions e_k) (region rd_j) h0 h1;
        frame_st_enc_inv (writer_epoch e_k) h0 h1;
        frame_st_dec_inv (reader_epoch e_k) h0 h1)
  else (let w_k = writer_epoch e_k in
        equal_on_disjoint (regions_of rd_j) (regions_of w_k) (region rd_j) h0 h1;
        frame_st_enc_inv w_k h0 h1)

val frame_reader_epoch: c:connection -> h0:HyperHeap.t -> h1:HyperHeap.t -> Lemma 
  (requires
    epochs_inv c h0 /\
    (exists (j:nat).{:pattern (witness j)}
     (let es = epochs c h0 in
      let hs_r = HS.region c.hs in 
      Map.contains h0 hs_r
      /\ j < Seq.length es 
      /\ (let rd_j = reader_epoch (Seq.index es j) in
           modifies (Set.singleton (region rd_j)) h0 h1 
         /\ st_dec_inv rd_j h1))))
  (ensures (epochs c h0 = epochs c h1
            /\ epochs_inv c h1))
let frame_reader_epoch c h0 h1 = ghost_lemma2 (frame_reader_epoch_k c h0 h1)            


val frame_unrelated_k: c:connection -> h0:HyperHeap.t -> h1:HyperHeap.t -> k:nat -> Ghost unit
  (requires (epochs_inv c h0 
	    /\ k < Seq.length (epochs c h0)
	    /\ equal_on (Set.union (Set.singleton (HS.region c.hs))
				  (Set.singleton (HS.peer c.hs))) h0 h1))
  (ensures (fun _ -> 
	      epochs c h0 = epochs c h1 
	    /\ k < Seq.length (epochs c h1)
	    /\ epoch_inv h1 (epoch_i c h1 k)))
let frame_unrelated_k c h0 h1 k =
  frame_epochs c h0 h1;
  let ek = Seq.index (epochs c h0) k in 
  frame_st_dec_inv (reader_epoch ek) h0 h1;
  frame_st_enc_inv (writer_epoch ek) h0 h1

val frame_unrelated: c:connection -> h0:HyperHeap.t -> h1:HyperHeap.t -> Lemma
  (requires (epochs_inv c h0 
	    /\ equal_on (Set.union (Set.singleton (HS.region c.hs))
				  (Set.singleton (HS.peer c.hs))) h0 h1))
  (ensures (epochs c h0 = epochs c h1 
	    /\ epochs_inv c h1))
let frame_unrelated c h0 h1 = 
  ghost_lemma (frame_unrelated_k c h0 h1);
  frame_epochs c h0 h1

val frame_modifies_internal_k: c:connection -> h0:HyperHeap.t -> h1:HyperHeap.t -> k:nat -> Ghost unit
  (requires (epochs_inv c h0 
	    /\ k < Seq.length (epochs c h0)
	    /\ modifies_internal h0 c.hs h1))
  (ensures (fun _ -> 
	      epochs c h0 = epochs c h1 
	    /\ k < Seq.length (epochs c h1)
	    /\ epoch_inv h1 (epoch_i c h1 k)))
let frame_modifies_internal_k c h0 h1 k =
    //frame_epochs c h0 h1;
  let ek = Seq.index (epochs c h0) k in 
  frame_st_dec_inv (reader_epoch ek) h0 h1;
  frame_st_enc_inv (writer_epoch ek) h0 h1

val frame_internal: c:connection -> h0:HyperHeap.t -> h1:HyperHeap.t -> Lemma
  (requires (epochs_inv c h0 
	    /\ modifies_internal h0 c.hs h1))
  (ensures (epochs c h0 = epochs c h1 
	    /\ epochs_inv c h1))
let frame_internal c h0 h1 = 
  ghost_lemma (frame_modifies_internal_k c h0 h1)
  


