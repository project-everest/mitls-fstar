(**
This modules implements the mutable state for the successive StAE epochs allocated by KeySchedule and used by TLS.
Its separation from Handshake and coding is somewhat arbitrary.
An elaboration would ensure that keys in old epochs are erased.
(i.e. we only keep old epoch AE logs for specifying authentication)
*)
module Epochs

(*
open FStar.Heap //17-10-27 TODO remove!
open FStar.HyperHeap //17-10-27 We'd like to remove it too. Conversely we miss HyperStack.ST 
open FStar.Seq // DO NOT move further below, it would shadow `FStar.HyperStack.mem`
open FStar.HyperStack
*)
open Mem 
open FStar.Monotonic.RRef
open FStar.Monotonic.Seq
open FStar.Error
open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
module Range = Range
open Range
//open HandshakeMessages
open StAE
//open Negotiation

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MR = FStar.Monotonic.RRef
module MS = FStar.Monotonic.Seq
type random = TLSInfo.random

(* debug printing *)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("EPO| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if Flags.debug_Epochs then print else (fun _ -> ())


type epoch_region_inv (#i:id) (hs_rgn:rgn) (r:reader (peerId i)) (w:writer i) =
  disjoint hs_rgn (region w) /\
  parent (region w) <> HH.root /\
  parent (region r) <> HH.root /\
  // grandparent of each writer is a sibling of the handshake
  parent hs_rgn = parent (parent (region w))  /\
  disjoint (region w) (region r) /\
  // they are all colored as epoch regions
  is_epoch_rgn (region w) /\
  is_epoch_rgn (region r) /\
  is_epoch_rgn (parent (region w)) /\
  is_epoch_rgn (parent (region r)) /\
  //except for the hs_rgn, of course
  is_hs_rgn hs_rgn

abstract type epoch_region_inv'
  (#i:id)
  (hs_rgn:rgn)
  (r:reader (peerId i))
  (w:writer i)
= epoch_region_inv hs_rgn r w

noeq type epoch (hs_rgn:rgn) (n:random) =
  | Epoch: #i:id{nonce_of_id i = n} ->
      h:Negotiation.handshake ->
      r: reader (peerId i) ->
      w: writer i {epoch_region_inv' hs_rgn r w} -> epoch hs_rgn n
// we would extend/adapt it for TLS 1.3,
// e.g. to notify 0RTT/forwad-privacy transitions
// for now epoch completion is a total function on handshake --- should be stateful

let epoch_id #r #n (e:epoch r n) : StAE.stae_id = Epoch?.i e

let reveal_epoch_region_inv_all (u:unit)
  : Lemma (forall i hs_rgn r w.{:pattern (epoch_region_inv' #i hs_rgn r w)}
       epoch_region_inv' #i hs_rgn r w   <==>
       epoch_region_inv #i hs_rgn r w)
=
  ()

let reveal_epoch_region_inv (#hs_rgn:rgn) (#n:random) (e:epoch hs_rgn n)
  : Lemma (let r = Epoch?.r e in
       let w = Epoch?.w e in
       epoch_region_inv hs_rgn r w)
=
  ()

let writer_epoch (#hs_rgn:rgn) (#n:random) (e:epoch hs_rgn n)
  : Tot (w:writer (e.i) {epoch_region_inv hs_rgn (Epoch?.r e) w})
=
  Epoch?.w e

let reader_epoch (#hs_rgn:rgn) (#n:random) (e:epoch hs_rgn n)
  : Tot (r:reader (peerId e.i) {epoch_region_inv hs_rgn r (Epoch?.w e)})
=
  Epoch?.r e

(* The footprint just includes the writer regions *)
let epochs_inv (#r:rgn) (#n:random) (es: seq (epoch r n)) =
  forall (i:nat { i < Seq.length es })
    (j:nat { j < Seq.length es /\ i <> j}).{:pattern (Seq.index es i); (Seq.index es j)}
    let ei = Seq.index es i in
    let ej = Seq.index es j in
    // they all descend from a common epochs sub-region of the connection
    parent (region ei.w) = parent (region ej.w) /\
    // each epoch writer lives in a region disjoint from the others
    disjoint (region ei.w) (region ej.w)

abstract let epochs_inv' (#r:rgn) (#n:random) (es: seq (epoch r n)) = epochs_inv es

let reveal_epochs_inv' (u:unit)
  : Lemma (forall (r:rgn) (#n:random) (es:seq (epoch r n)). {:pattern (epochs_inv' es)}
         epochs_inv' es
         <==>
         epochs_inv es)
  = ()

// Epoch counters i must satisfy -1 <= i < length !es
type epoch_ctr_inv (#a:Type0) (#p:(seq a -> Type)) (r:rid) (es:MS.i_seq r a p) =
  x:int{-1 <= x /\ witnessed (MS.int_at_most x es)}

type epoch_ctr (#a:Type0) (#p:(seq a -> Type)) (r:rid) (es:MS.i_seq r a p) =
  m_rref r (epoch_ctr_inv r es) increases

// As part of the handshake state,
// we keep a sequence of allocated epochs,
// together with counters for reading and writing
//NS: probably need some anti-aliasing invariant of these three references
//17-04-17 CF: consider switching to a single reference to a tuple
noeq type epochs (r:rgn) (n:random) = | MkEpochs:
  es: MS.i_seq r (epoch r n) (epochs_inv #r #n) ->
  read: epoch_ctr r es ->
  write: epoch_ctr r es -> 
  exporter: MS.i_seq r KeySchedule.exportKey (fun s -> Seq.length s <= 2)  ->
  epochs r n

/// Epochs stores all keys produced by the HS and used by TLS.
/// These keys consist of 
/// - the StAE reader or writer for 0RTT (client2server only)
/// - the 0RTT exporter secret key 
///
/// - StAE 1RTT reader or writer for 1RTT (in both directions)
/// - the 0RTT and 1RTT exporter keys.
/// We also need to keep track of which key is in use, if any, in each direction.
///
/// Proposal:
/// - have a single mutable state 
/// - instead of "-1", we could have a special "NULL" value for StAE.
/// - we need to think ahead for key erasure:
///   * we have a "ghost" sequence of readers (or writers) for overall integrity.
///   * we only keep concrete current keys + future keys
///   * (for DTLS, we may need to keep a few keys for the record layer)
///
/// Questions:
/// 
/// - what to do with the epoch context? We need to bind the keys to
///   the connection and to the handshake, in order to give
///   precise TLS-level security guarantees.
/// - how to guarantee synchronized configs between readers and writers?
/// - how to control the usage of these keys? Some of them CANNOT be
///   used for application data.
/// - should epochs track connection closure? 


let containsT (#r:rgn) (#n:random) (es:epochs r n) (h:mem) =
    MS.i_contains (MkEpochs?.es es) h

val alloc_log_and_ctrs: #a:Type0 -> #p:(seq a -> Type0) -> r:rgn ->
  ST (is:MS.i_seq r a p & c1:epoch_ctr r is & c2:epoch_ctr r is)
    (requires (fun h -> p Seq.createEmpty))
    (ensures (fun h0 x h1 ->
      modifies_one r h0 h1 /\
      modifies_rref r Set.empty (HS.HS?.h h0) (HS.HS?.h h1) /\
      (let (| is, c1, c2 |) = x in
      i_contains is h1 /\
      m_contains c1 h1 /\
      m_contains c2 h1 /\
      i_sel h1 is == Seq.createEmpty)))

#reset-options "--using_facts_from FStar --using_facts_from Prims --using_facts_from Epochs --using_facts_from Parse"

let alloc_log_and_ctrs #a #p r =
  let init = Seq.createEmpty in
  let is = alloc_mref_iseq p r init in
  witness is (int_at_most (-1) is);
  let c1 : epoch_ctr #a #p r is = m_alloc r (-1) in
  let c2 : epoch_ctr #a #p r is = m_alloc r (-1) in
  (| is, c1, c2 |)

#reset-options

val incr_epoch_ctr :
  #a:Type0 ->
  #p:(seq a -> Type0) ->
  #r:rgn ->
  #is:MS.i_seq r a p ->
  ctr:epoch_ctr r is ->
  ST unit
    (requires fun h -> 1 + m_sel h ctr < Seq.length (i_sel h is))
    (ensures (fun h0 _ h1 ->
      let ctr_as_hsref = MR.as_hsref ctr in
      modifies_one r h0 h1 /\
      modifies_rref r (Set.singleton (Heap.addr_of (as_ref ctr_as_hsref))) (HS.HS?.h h0) (HS.HS?.h h1) /\
      m_sel h1 ctr = m_sel h0 ctr + 1))
let incr_epoch_ctr #a #p #r #is ctr =
  m_recall ctr;
  let cur = m_read ctr in
  MS.int_at_most_is_stable is (cur + 1);
  witness is (int_at_most (cur + 1) is);
  m_write ctr (cur + 1)

val create: r:rgn -> n:random -> ST (epochs r n)
    (requires (fun h -> True))
    (ensures (fun h0 x h1 -> modifies_one r h0 h1 /\ modifies_rref r Set.empty (HS.HS?.h h0) (HS.HS?.h h1)))
let create (r:rgn) (n:random) =
  let (| esref, c1, c2 |) = alloc_log_and_ctrs #(epoch r n) #(epochs_inv #r #n) r in
  let xkr = alloc_mref_iseq (fun s -> Seq.length s <= 2) r Seq.createEmpty in 
  assume False; //17-06-30 TODO restore framing with extra field
  MkEpochs esref c1 c2 xkr

unfold let incr_pre #r #n (es:epochs r n) (proj:(es:epochs r n -> Tot (epoch_ctr r (MkEpochs?.es es)))) h : GTot Type0 =
  let ctr = proj es in
  let cur = m_sel h ctr in
  cur + 1 < Seq.length (i_sel h (MkEpochs?.es es))

unfold let incr_post #r #n (es:epochs r n) (proj:(es:epochs r n -> Tot (epoch_ctr r (MkEpochs?.es es)))) h0 (_:unit) h1 : GTot Type0 =
  let ctr = proj es in
  let oldr = m_sel h0 ctr in
  let newr = m_sel h1 ctr in
  let ctr_as_hsref = MR.as_hsref ctr in
  modifies_one r h0 h1 /\
  HH.modifies_rref r (Set.singleton (Heap.addr_of (HH.as_ref (MkRef?.ref ctr_as_hsref)))) (HS.HS?.h h0) (HS.HS?.h h1) /\
  newr = oldr + 1

val add_epoch :
  #r:rgn -> #n:random -> es:epochs r n -> e:epoch r n ->
  ST unit
    (requires fun h -> let is = MkEpochs?.es es in epochs_inv #r #n (Seq.snoc (i_sel h is) e))
    (ensures fun h0 x h1 ->
        let es = MkEpochs?.es es in
        let es_as_hsref = MR.as_hsref es in
        modifies_one r h0 h1 /\ modifies_rref r (Set.singleton (Heap.addr_of (as_ref es_as_hsref))) (HS.HS?.h h0) (HS.HS?.h h1) /\
        i_sel h1 es == Seq.snoc (i_sel h0 es) e)
let add_epoch #r #n (MkEpochs es _ _ _) e = MS.i_write_at_end es e

let get_epochs #r #n (es:epochs r n) = MkEpochs?.es es

let ctr (#r:_) (#n:_) (e:epochs r n) (rw:rw) = match rw with
  | Reader -> e.read
  | Writer -> e.write

let string_of_es #r #n (es:epochs r n) =
  let r = m_read (ctr es Reader) in
  let w = m_read (ctr es Writer) in
  string_of_int r^"/"^string_of_int w

let incr_reader #r #n (es:epochs r n) : ST unit
    (requires (incr_pre es MkEpochs?.read))
    (ensures (incr_post es MkEpochs?.read))
=
  incr_epoch_ctr (MkEpochs?.read es);
  trace ("reader++ "^string_of_es es)

let incr_writer #r #n (es:epochs r n) : ST unit
    (requires (incr_pre es MkEpochs?.write))
    (ensures (incr_post es MkEpochs?.write))
=
  incr_epoch_ctr (MkEpochs?.write es);
  trace ("writer++ "^string_of_es es)


val readerT: #rid:rgn -> #n:random -> e:epochs rid n -> mem -> GTot (epoch_ctr_inv rid (get_epochs e))
let readerT #rid #n (MkEpochs es r w _) (h:mem) = m_sel h r

val writerT: #rid:rgn -> #n:random -> e:epochs rid n -> mem -> GTot (epoch_ctr_inv rid (get_epochs e))
let writerT #rid #n (MkEpochs es r w _) (h:mem) = m_sel h w

unfold let get_ctr_post (#r:rgn) (#n:random) (es:epochs r n) (rw:rw) h0 (i:int) h1 =
  let epochs = MkEpochs?.es es in
  h0 == h1 /\
  i = m_sel h1 (ctr es rw) /\
  -1 <= i /\
  MS.int_at_most i epochs h1

let get_ctr (#r:rgn) (#n:random) (es:epochs r n) (rw:rw)
  : ST int (requires (fun h -> True)) (ensures (get_ctr_post es rw))
=
  let epochs = es.es in
  let n = m_read (ctr es rw) in
  testify (MS.int_at_most n epochs);
  n

let get_reader (#r:rgn) (#n:random) (es:epochs r n) = get_ctr es Reader
let get_writer (#r:rgn) (#n:random) (es:epochs r n) = get_ctr es Writer

let epochsT #r #n (es:epochs r n) (h:mem) = MS.i_sel h (MkEpochs?.es es)

let get_current_epoch
  (#r:_)
  (#n:_)
  (e:epochs r n)
  (rw:rw)
  : ST (epoch r n)
       (requires (fun h -> 0 <= m_sel h (ctr e rw)))
       (ensures (fun h0 rd h1 ->
           let j = m_sel h1 (ctr e rw) in
           let epochs = MS.i_sel h1 e.es in
           h0==h1 /\
           Seq.indexable epochs j /\
           rd == Seq.index epochs j))
=
  let j = get_ctr e rw in
  let epochs = MS.i_read e.es in
  Seq.index epochs j

val recordInstanceToEpoch:
  #r:rgn -> #n:random -> hs:Negotiation.handshake ->
  ks:KeySchedule.recordInstance -> Tot (epoch r n)
let recordInstanceToEpoch #hs_rgn #n hs ri =
  let KeySchedule.StAEInstance #i rd wr = ri in
  assume(nonce_of_id i = n); // ADL: KS will need to provove this
  assume(epoch_region_inv' hs_rgn rd wr);
  Epoch #hs_rgn #n #i hs rd wr
