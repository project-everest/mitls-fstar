module Epochs
open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties
open FStar.Monotonic.RRef
open MonotoneSeq
open Platform.Error
open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
open Range
open HandshakeMessages
open StAE
open Negotiation

module HH = FStar.HyperHeap

// No plaintext epoch
private type id = StAE.id

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
  | Epoch: h:handshake -> 
    	   #i: id ->
           r: reader (peerId i) ->
           w: writer i {epoch_region_inv' hs_rgn r w /\ nonce_of_id i = n} 
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
  : Tot (w:writer (handshakeId (e.h)) {epoch_region_inv hs_rgn (Epoch.r e) w})
  = Epoch.w e

let reader_epoch (#hs_rgn:rgn) (#n:TLSInfo.random) (e:epoch hs_rgn n) 
  : Tot (r:reader (peerId (handshakeId (e.h))) {epoch_region_inv hs_rgn r (Epoch.w e)})
  = match e with | Epoch hs #i r w -> r //16-05-20 Epoch.r e failed.

(* The footprint just includes the writer regions *)
let epochs_inv (#r:rgn) (#n:TLSInfo.random) (es: seq (epoch r n)) =
  forall (i:nat { i < Seq.length es })
    (j:nat { j < Seq.length es /\ i <> j}).{:pattern (Seq.index es i); (Seq.index es j)}
    let ei = Seq.index es i in
    let ej = Seq.index es j in
    parent (region ei.w) = parent (region ej.w) /\  //they all descend from a common epochs sub-region of the connection
    disjoint (region ei.w) (region ej.w)           //each epoch writer lives in a region disjoint from the others

abstract let epochs_inv' (#r:rgn) (#n:TLSInfo.random) (es: seq (epoch r n)) = epochs_inv es

let reveal_epochs_inv' (u:unit)
  : Lemma (forall (r:rgn) (#n:TLSInfo.random) (es:seq (epoch r n)). {:pattern (epochs_inv' es)}
	     epochs_inv' es
	     <==>
	     epochs_inv es)
  = ()

type epoch_ctr_inv (#a:Type0) (#p:(seq a -> Type)) (r:rid) (es:MonotoneSeq.i_seq r a p) =
  x:int{-1 <= x /\ witnessed (fun h -> x < Seq.length (m_sel h es))}

// Epoch counters i must satisfy -1 <= i < length !es
type epoch_ctr (#a:Type0) (#p:(seq a -> Type)) (r:rid) (es:MonotoneSeq.i_seq r a p) = 
  m_rref r (epoch_ctr_inv r es) increases

type epochs (r:rgn) (n:TLSInfo.random) = 
  | Epochs: es: MonotoneSeq.i_seq r (epoch r n) epochs_inv -> 
    	    read: epoch_ctr r es -> 
	    write: epoch_ctr r es ->
	    epochs r n  

let containsT (Epochs es r w) (h:HyperHeap.t) =
    MonotoneSeq.i_contains es h 

val epochs_init: r:rgn -> n:TLSInfo.random -> ST (epochs r n)
       (requires (fun h -> True))
       (ensures (fun h0 x h1 -> True))
let epochs_init (r:rgn) (n:TLSInfo.random) = 
    let esref = MonotoneSeq.alloc_mref_seq r Seq.createEmpty in
    witness esref (fun h -> -1 <= -1 /\ -1 < Seq.length (m_sel h esref));
    let (x:int{witnessed (fun h -> -1 <= x /\ x < Seq.length (m_sel h esref))}) = -1 in
    let mr = m_alloc r x in
    let mw = m_alloc r x in
    Epochs esref mr mw
(*
val add_epoch: #r:rgn -> #n:TLSInfo.random -> 
    	       es:epochs r n -> e: epoch r n -> ST unit
       (requires (fun h -> True))
       (ensures (fun h0 x h1 -> True))
let add_epoch #rg #n (Epochs es r w) e = 
    MonotoneSeq.i_write_at_end #rg es e

val incr_reader: #r:rgn -> #n:TLSInfo.random ->
               es:epochs r n -> ST unit
       (requires (fun h ->
         let Epochs mes mr _ = es in
         let cur = m_sel h mr in
         cur + 1 < Seq.length (m_sel h mes)))
       (ensures (fun h0 () h1 ->
         let Epochs mes mr _ = es in
         let oldr = m_sel h0 mr in
         let newr = m_sel h1 mr in
         modifies (Set.singleton r) h0 h1
         /\ HH.modifies_rref r !{HH.as_ref (as_rref mr)} h0 h1
         /\ newr = oldr + 1
         /\ witnessed (fun h -> -1 <= newr /\ newr < Seq.length (m_sel h mes))))
let incr_reader #r #n (Epochs es mr _) =
  m_recall mr;
  let cur = m_read mr in
  witness es (fun h -> -1 <= cur+1 /\ cur+1 < Seq.length (m_sel h es));
  m_write mr (cur + 1)

val incr_writer: #r:rgn -> #n:TLSInfo.random ->
               es:epochs r n -> ST unit
       (requires (fun h ->
         let Epochs mes _ mw = es in
         let cur = m_sel h mw in
         cur + 1 < Seq.length (m_sel h mes)))
       (ensures (fun h0 () h1 ->
         let Epochs mes _ mw= es in
         let oldw = m_sel h0 mw in
         let neww = m_sel h1 mw in
         modifies (Set.singleton r) h0 h1
         /\ HH.modifies_rref r !{HH.as_ref (as_rref mw)} h0 h1
         /\ neww = oldw + 1
         /\ witnessed (fun h -> -1 <= neww /\ neww < Seq.length (m_sel h mes))))
let incr_writer #r #n (Epochs es _ mw) =
  m_recall mw;
  let cur = m_read mw in
  witness es (fun h -> -1 <= cur+1 /\ cur+1 < Seq.length (m_sel h es));
  m_write mw (cur + 1)

let get_epochs (Epochs es r w) = es 

let epochsT (Epochs es r w) (h:HyperHeap.t) = MonotoneSeq.i_sel h es

let readerT (Epochs es r w) (h:HyperHeap.t) = m_sel h r

let writerT (Epochs es r w) (h:HyperHeap.t) = m_sel h w

*)
