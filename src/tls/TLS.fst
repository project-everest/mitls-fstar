module TLS

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
// TODO make it private?
// TODO write invariant, to cut out cases in code
// e.g. , reading, and writing transitions are tighly related
// TODO recheck large logical invariants GState in Dispatch.fs7

// private //TODO: restore this qualifier; NS:commenting for now
type dispatch =
  | Init
  | FirstHandshake of ProtocolVersion (* bound by ServerHello *)
  | Finishing
  | Finished
  | Open
  | Closing of ProtocolVersion * string (* write-only, while sending a fatal alert *)
  | Closed

type connection = | C:
  #region: rid ->
  hs:      hs { extends (HS.region hs) region } (* providing role, config, and uid *) ->
  alert:   Alert.state  { extends (Alert.State.region alert) region /\ HS.region hs <> Alert.State.region alert } (* review *) ->
  tcp:     networkStream ->
  reading: rref region dispatch ->
  writing: rref region dispatch ->
  connection

let c_role c   = c.hs.r
let c_id c     = c.hs.id
let c_cfg c    = c.hs.cfg
let c_resume c = c.hs.resume
let c_log c    = c.hs.log


(*** top-level invariant (TBC) ***) 

// we'll rely on the invariant to show we picked the correct index

opaque type Seq_forall (#a:Type) (p: a -> Type) (s:seq a) =
  forall (j: nat { j < Seq.length s }).{:pattern (Seq.index s j)} p (Seq.index s j)

let test_1 (p:nat -> Type) (s:seq nat { Seq_forall p s }) = assert(p 12 ==> Seq_forall p (snoc s 12))
let test_2 (p:nat -> Type) (s:seq nat { Seq_forall p s }) (j:nat { j < Seq.length s }) =  let x = Seq.index s j in assert(p x)
//let test_3 (p:nat -> Type) (s:seq nat { Seq_forall p s }) x = assert(SeqProperties.mem x s ==> p x)


(* usage? how to prove this lemma?  val exercise_seq_forall: #a:Type
-> p: (a -> Type) -> s:seq a -> x: a -> Lemma (u:unit { (Seq_forall p
s /\ p x) ==> Seq_forall p (snoc s x)}) *)

(* TODO, ~ TLSInfo.siId; a bit awkward with null_Id *)
let epoch_id (#region:rid) (o: option (epoch region)) =
  match o with 
  | Some e -> hs_id e.h
  | None   -> noId

val reader_epoch: #region:rid -> e:epoch region -> Tot (reader (hs_id e.h))
let reader_epoch region (Epoch h r w) = r

val writer_epoch: #region:rid -> e:epoch region -> Tot (writer (hs_id e.h))
let writer_epoch region (Epoch h r w) = w

type epoch_inv (#region:rid) (h:HyperHeap.t) (e: epoch region) = 
  st_dec_inv (reader_epoch e) h 
  /\ st_enc_inv (writer_epoch e) h

type epochs_inv c h = 
  Seq_forall (epoch_inv h) (sel h c.hs.log)

//type epochs_inv2 c h = 
//  Seq_forall (fun e -> epoch_inv e h)
//             (sel h  (HS.log (C.hs c)))

type st_inv c h = 
  hs_inv (C.hs c) h /\
  epochs_inv c h 

val test_st_inv: c:connection -> j:nat -> ST (e:epoch (HS.region (C.hs c)))
  (requires (fun h -> st_inv c h /\ j < Seq.length (sel h (HS.log (C.hs c)))))
  (ensures (fun h0 e h1 -> 
    h0 == h1 /\ 
    epochs_inv c h1 /\
    st_dec_inv (reader_epoch e) h1 /\ st_enc_inv (writer_epoch e) h1))

let test_st_inv c j = 
  let epochs = !c.hs.log in
  Seq.index epochs j

// we should have st_env_inv & st_dec_inv for all epochs, all the time. 
// + the property that at most the current epochs' logs are extended.
val epochs : c:connection -> h:HyperHeap.t -> GTot (es:seq (epoch (HS.region c.hs)){epochs_footprint es /\ es = HyperHeap.sel h c.hs.log})
let epochs c h = HyperHeap.sel h c.hs.log

// #reset-options
// #set-options "--logQueries"
// let test c h = assert (epochs c h = HyperHeap.sel #(seq (epochh c.hs.log)))

let epoch_i c h i = Seq.index (epochs c h) i

(** should go to Handshake *)

opaque type trigger2 (x:nat) (y:nat) = True

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
val ghost_lemma2: #a:Type -> #b:Type -> #p:(a -> b -> Type) -> #q:(a -> b -> unit -> Type) 
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
              /\ epoch_inv h1 (epoch_i c h1 k)))
let frame_writer_epoch_k c h0 h1 j k =
  let es = epochs c h0 in
  let hs_r = HS.region c.hs in
  let e_j = Seq.index es j in
  let e_k = Seq.index es k in
  let wr_j = writer_epoch e_j in
  if k<>j
  then (equal_on_disjoint (regions e_j) (regions e_k) (region wr_j) h0 h1;
        frame_st_enc_inv (writer_epoch e_k) h0 h1;
        frame_st_dec_inv (reader_epoch e_k) h0 h1)
  else (let r_k = reader_epoch e_k in
        equal_on_disjoint (regions_of wr_j) (regions_of r_k) (region wr_j) h0 h1;
        frame_st_dec_inv r_k h0 h1)

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

(*
(* a trivial variant as nothing gets modified; still no trivial proof... *) 
assume val frame_unmodified: c:connection -> h0:HyperHeap.t -> h1:HyperHeap.t -> Lemma 
  (requires
    epochs_inv c h0 /\
    modifies (Set.singleton (Alert.State.region c.alert)) h0 h1)
  (ensures (
    epochs c h0 = epochs c h1 /\ 
    epochs_inv c h1))

(* and another... *)
assume val frame_modified_one: c:connection -> h0:HyperHeap.t -> h1:HyperHeap.t -> Lemma
  (requires
    epochs_inv c h0 /\
    modifies_one c.region h0 h1)
  (ensures (
    epochs c h0 = epochs c h1 /\ 
    epochs_inv c h1))
// let frame_modified_one c h0 h1 = ()
*)
assume val frame_admit: c:connection -> h0:HyperHeap.t -> h1:HyperHeap.t -> Lemma 
  (requires
    epochs_inv c h0)
  (ensures (
    epochs c h0 = epochs c h1 /\ 
    epochs_inv c h1))

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

(*** control API ***)

// was connect, resume, accept_connected, ...
val create: r0:rid -> tcp:networkStream -> r:role -> cfg:config ->
            resume: option (sid: sessionID { r = Client }) ->
            ST connection
  (requires (fun h -> True))
  (ensures (fun h0 c h1 -> 
    modifies Set.empty h0 h1 /\
    fresh_region c.region h0 h1 /\
    extends c.region r0 /\
    c.tcp = tcp  /\
    c_role c = r /\
    c_cfg c = cfg /\
    c_resume c = resume /\
    (r = Server ==> resume = None) /\
    Map.contains h1 c.region /\
    (* sel h1 (c_log c) = Seq.createEmpty /\ *) //NS: this fails now ... not sure why
    sel h1 c.reading  = Init /\
    sel h1 c.writing  = Init
    ))


let create m0 tcp r cfg resume =
    let m = new_region m0 in
    let hs = Handshake.init m r cfg resume in
    let al = Alert.init m in
    let rd = ralloc m Init in 
    let wr = ralloc m Init in
    C hs al tcp rd wr

// painful to specify?
let connect m0 tcp r cfg        = create m0 tcp Client cfg None
let resume m0 tcp r cfg sid     = create m0 tcp Client cfg (Some sid)
let accept_connected m0 tcp cfg = create m0 tcp Server cfg None

let accept m0 listener cfg =
    let tcp = Platform.Tcp.accept listener in
    accept_connected m0 tcp cfg

let rehandshake c ops = Handshake.rehandshake (C.hs c) ops
let rekey c ops       = Handshake.rekey       (C.hs c) ops
let request c ops     = Handshake.request     (C.hs c) ops


(*** current epochs ***)

// the index of messages depends on the connection state, 
// and may be different for reading and for writing.
// also provide access to older epochs?

// not dealing with errors yet.

// relying on a function from dispatch state to completion status
// using polymorphism to retain the caller's epoch refinement
//val epochT: #e:Type -> p: (e -> Type) -> xs: seq e { Seq_forall p xs } -> dispatch -> Tot (option (x:e { p x }))
val epochT: #e:Type -> xs: seq e -> dispatch -> Tot (option (e * nat))
let epochT epochs other =
  let j : n:int { n < Seq.length epochs } =
    if other = Finishing || other = Finished
    then Seq.length epochs - 2
    else Seq.length epochs - 1 in
  if j < 0 then None else Some(Seq.index epochs j, j)

(** writing epochs **)

val epoch_wo: #region:rid -> o: option (epoch region){ is_Some o } -> Tot (writer (epoch_id o))
let epoch_wo _ o = writer_epoch (Some.v o)
 
// val epoch_w_h: c:connection -> h:HyperHeap.t -> GTot (option (e: epoch (HS.region (C.hs c)) { st_dec_inv (reader_epoch e) h } ))
let epoch_w_h c (h:t { st_inv c h }) =
  let log = sel h c.hs.log in 
  let other = sel h c.reading in 
  match epochT log other with 
  | None -> None
  | Some (e, _) -> Some e

val epoch_w: c:connection -> ST (option (epoch (HS.region c.hs)))// * nat))
  (requires (st_inv c))
  (ensures (fun h0 o h1 ->
    h0 == h1 /\ 
    st_inv c h0 /\ 
    st_inv c h1 /\
    o = epoch_w_h c h0 /\
    (is_Some o ==> st_enc_inv (writer_epoch (Some.v o)) h0)))
let epoch_w c =
  let log = !c.hs.log in
  let other = !c.reading in 
  match epochT log other with 
  | None -> None
  | Some (e, _) -> Some e

(** reading epochs **)

val epoch_ro: #region:rid -> o: option (epoch region){ is_Some o } -> Tot (reader (epoch_id o))
let epoch_ro _ o =
  match o with 
  | Some(Epoch _ r _) -> r

let epoch_r_h c h = 
  let log = sel h (c_log c) in 
  let other = sel h (C.writing c) in
  match epochT log other with 
  | None -> None
  | Some (e, _) -> Some e

val epoch_r: c:connection -> ST _
  (requires (fun h -> True))
  (ensures (fun h0 o h1 ->
    h0 = h1 /\
    o = epoch_r_h c h1 ))
let epoch_r c =
  let log = !c.hs.log in 
  let other = !c.writing in 
  match epochT log other with 
  | None -> None
  | Some (e, _) -> Some e

//-------------------------------- writing --------------------------------------------

type msg_o (i:id) = (r:range & DataStream.fragment i r)

type ioresult_w =
    // public results
    | Written             // Application data was written, and the connection remains writable
    | WriteError: o:option alertDescription -> txt: string -> ioresult_w // The connection is down, possibly after sending an alert
//  | WritePartial of unsent_data // worth restoring?

    // transient, internal results
    | MustRead            // Nothing written, and the connection is busy completing a handshake
    | WriteDone           // No more data to send in the current state
    | WriteHSComplete     // The handshake is complete [while reading]
    | SentClose           // [while reading]
    | WriteAgain          // there is more to send
    | WriteAgainFinishing // the outgoing epoch changed & more to send to finish the handshake
    | WriteAgainClosing   // we are tearing down the connection & must still send an alert

type ioresult_o = r:ioresult_w { is_Written r \/ is_WriteError r }

(*
// Outcomes for internal, one-message-at-a-time functions
// (now merged with TLS.ioresult_o)
type writeOutcome =
    // now WriteError(None,err)
    | WError of string (* internal *)

    // now Written
    | WAppDataDone (* App data have been sent, no more data to send *)

    // now MustRead
    | WriteFinished (* The finished message has been sent, but the handshake is not over *)

    // now WriteError(Some ad, err)
    | SentFatal of alertDescription * string (* The alert we sent *)

    // internal states only
    | WriteDone (* No more data to send in the current state *)
    | WriteHSComplete (* The handshake is complete *)
    | SentClose
    | WriteAgain (* Possibly more data to send *)
    | WriteAgainFinishing (* Possibly more data to send, and the outgoing epoch changed *)
    | WriteAgainClosing (* An alert must be sent before the connection is torn down *)
*)

//* used to be dynamically checked; trying static. Use assert instead?
//* was it strict on both sides?
val moveToOpenState: c:connection -> ST unit
  (requires (fun h ->
     st_inv c h /\
     (let s = sel h c.reading in s == Finishing \/ s == Finished) /\
     (let s = sel h c.writing in s == Finishing \/ s == Finished)))
  (ensures (fun h0 _ h1 ->
     st_inv c h1 /\
     modifies (Set.singleton (C.region c)) h0 h1 /\
     sel h1 c.reading == Open /\
     sel h1 c.writing == Open))

let moveToOpenState c =
    let h0 = ST.get() in
    C.reading c := Open;
    C.writing c := Open;
    frame_admit c h0 (ST.get())


assume val epoch_pv: #region:rid -> epoch region -> Tot ProtocolVersion


// too convenient
val unexpected: #a:Type -> v:string -> ST a
  (requires (fun h -> True))
  (ensures (fun _ _ _ -> False ))
 
let rec unexpected s = unexpected s

(* Dispatch dealing with network sockets *)
// we need st_inv h c /\ wr > FirstHandshake ==> is_Some epoch_w

val pickSendPV: c:connection -> ST ProtocolVersion
  (requires (st_inv c))
  (ensures (fun h0 pv h1 -> h0 = h1))
 
let pickSendPV c =
    let wr = !(C.writing c) in
    match wr with
    | Init -> getMinVersion (C.hs c)
    | FirstHandshake(pv) | Closing(pv,_) -> pv
    | Finishing | Finished | Open ->
        (match epoch_w c with
        | Some e -> epoch_pv e
        | None -> unexpected "todo"
        ) // (hs_id (Epoch.h e)).protocol_version)
    | Closed -> unexpected "[pickSendPV] invoked on a Closed connection"


//15-11-27 illustrating the overhead for "unrelated" updates; still missing modifies clauses 
val closeConnection: c: connection -> ST unit 
  (requires (fun h0 -> st_inv c h0))
  (ensures (fun h0 _ h1 -> st_inv c h1))

let closeConnection c =
    let h0 = ST.get() in
    invalidateSession (C.hs c);
    let h1 = ST.get() in 
    recall (HS.log c.hs); recall (HS.state c.hs); // needed to preserve hs_inv within inv
    C.reading c := Closed;
    C.writing c := Closed;
    frame_admit c h0 (ST.get()) 


// on some errors, we locally give up the connection
let unrecoverable c reason =
    closeConnection c;
    WriteError None reason

// send a final alert then tear down the connection
let abortWithAlert c ad reason =
    let closingPV = pickSendPV c in
    invalidateSession (C.hs c);
    (* TODO Alert.send_alert (C.alert c) ad ; *)
    C.reading c := Closed;
    C.writing c := Closing(closingPV,reason)

// on some errors, we attempt to send an alert before tearing down the connection
let closable c reason =
    admit();
    abortWithAlert c AD_internal_error reason;
    WriteAgainClosing

// -------------

(*
assume val epoch_w_h_inv: c: connection -> h0: HyperHeap.t -> h1: HyperHeap.t -> 
  Lemma (
    Let(epoch_w_h c h0) (fun o ->
      (st_inv c h0 /\ 
      (is_None o ==> HyperHeap.modifies Set.empty h0 h1) /\
      (is_Some o ==>
       Let(epoch_wo o)(fun wr -> 
        HyperHeap.modifies (Set.singleton (writer_region wr)) h0 h1)))
    ==> o = epoch_w_h c h1))

let epoch_w_h_inv c h0 h1 = 
  match epoch_w_h c h0 with 
  | None -> ()
  | Some(Epoch _ r w) -> 
    ( cut(b2t(extends (HS.region (C.hs c)) (C.region c)));
      cut(b2t(extends (writer_region w) (HS.region (C.hs c))));
      admit (); // something needed in st_inv
      ()
)
*)
 
val fragment_entry: #i:id -> e: entry i -> Tot (Content.fragment i)
let fragment_entry i (Entry c ad f) = f

(*
val fragment_entry: #i:id -> log: seq (entry i) { Seq.length log > 0 } -> Tot (rg:frange i & Content.fragment i)
let fragment_log i log = 
  match Seq.index log (Seq.length log - 1) with 
  | Entry c ad f -> 
    admitP(is_MACOnly i.aeAlg ==> is_SSL_3p0 i.pv);     // 15-09-12 Get rid of crazy pre on cipherRangeClass?? 
    let rg = Range.cipherRangeClass i (length c) in 
    let f: Content.fragment i  = f in
    (| rg, f |)
*)

(*
val append: #i:id -> log0: seq (entry i) -> log1: seq (entry i) -> f:Content.fragment i -> Tot bool
let append i log0 log1 f =  
  (Seq.length log1 = Seq.length log0 + 1)
// &&  log0 = Seq.slice log1 0 (Seq.length log1 - 1) 
// &&  f = Entry.p (Seq.index log1 (Seq.length log1 - 1))
 
val append_lemma: #i:id -> log0: seq (entry i) -> log1: seq (entry i) -> e:entry i -> 
  Lemma (
      log1  = snoc log0 e ==> 
      append log0 log1 (Entry.p e))

let append_lemma i log0 log1 e = 
  match e with Entry c ad f -> ()
*)

(* Note: We do not have polarities for subtyping. 
         So, a (ContentType * frange) </: (ContentType * range)
*)         
val ct_rg_test : i:id -> f:Content.fragment i -> Tot (ContentType * range)
let ct_rg_test i f = let x, y = Content.ct_rg i f in (x,y)
 
val send_payload: c:connection -> i:id -> f: Content.fragment i -> ST (StatefulPlain.cipher i)
  (requires (fun h -> 
    st_inv c h /\ 
    (let o = epoch_w_h c h in 
      i == epoch_id o /\
      (is_Some o ==> is_seqn (sel h (seqn (writer_epoch (Some.v o))) + 1)))))
  (ensures (fun h0 payload h1 -> 
    st_inv c h0 /\ (
    let ctrg: ContentType * frange i = Content.ct_rg i f in 
    let o:option (epoch (HS.region (C.hs c))) = epoch_w_h c h0 in
    //let j = Seq.length (sel h0 (c.hs.log)) - 1 in
    //let u = frame_writer_epoch c j h0 h1 in
    st_inv c h1 /\
    o == epoch_w_h c h1 /\ 
    i == epoch_id o /\
    (is_None o ==> h0 == h1) /\
    (is_Some o ==>
      ( let wr:writer (epoch_id o) =  epoch_wo o in
        HyperHeap.modifies (Set.singleton (region wr)) h0 h1
      /\ Heap.modifies (!{ as_ref (log wr), as_ref (seqn wr)}) (Map.sel h0 (region wr)) (Map.sel h1 (region wr))
      /\ sel h1 (seqn wr) = sel h0 (seqn wr) + 1
      /\ st_enc_inv #i wr h0
      /\ st_enc_inv #i wr h1
      /\ Seq.length (sel h1 (log wr)) = Seq.length (sel h0 (log wr)) + 1 
      //( = snoc (sel h0 (writer_log wr)) e /\ f = fragment_entry e))
      // /\ (is_MACOnly i.aeAlg ==> is_SSL_3p0 i.pv)  // 15-09-12 Get rid of crazy pre on cipherRangeClass??  
      // /\ Wider (Range.cipherRangeClass i (length payload)) (snd ctrg) 
      // /\ (exists (e:entry i). (sel h1 (writer_log wr) = snoc (sel h0 (writer_log wr)) e /\ f = fragment_entry e)) 
      // /\ sel h1 (log wr) = snoc (sel h0 (log wr)) (Entry payload (StatefulPlain.makeAD i (fst ctrg)) f) 
      // modifies at most the writer of (epoch_w c), adding f to its log
      )) 
)))

let send_payload c i f =
    let o = epoch_w c in
    match o with
      | None -> Content.repr i f
      | Some(Epoch h _ w) ->
        let h0 = ST.get() in
 	// assert (epochs_inv c h0);
        recall c.reading; 
	recall c.hs.log;
	// assert (Map.contains h0 (HS.region c.hs));
        let ct, rg = Content.ct_rg i f in
        let ad = StatefulPlain.makeAD i ct in
        let r = encrypt #i #ad #rg w f in
	let h1 = ST.get() in 
	// assert (modifies (singleton (region w)) h0 h1);
 	// assert (st_enc_inv w h1);
	cut (witness (snd (Some.v (epochT (sel h0 c.hs.log) (sel h0 c.reading)))));
	frame_writer_epoch c h0 h1;
        r

 
// check vs record
val send: c:connection -> #i:id -> f: Content.fragment i -> ST (Result unit)
  (requires (fun h -> 
    st_inv c h /\ 
    (let o = epoch_w_h c h in 
    i == epoch_id o /\
    (is_Some o ==> is_seqn (sel h (seqn (writer_epoch (Some.v o))) + 1)))))
  (ensures (fun h0 _ h1 -> 
    st_inv c h0 
  /\ st_inv c h1 
  /\ ( let o = epoch_w_h c h0 in
      o == epoch_w_h c h1 
    /\ (is_None o ==> h0 == h1) 
    /\ (is_Some o ==>
        ( let wr:writer (epoch_id o) = epoch_wo o in 
          HyperHeap.modifies (Set.singleton (region wr)) h0 h1
        /\ Heap.modifies (!{ as_ref (log wr), as_ref (seqn wr)}) (Map.sel h0 (region wr)) (Map.sel h1 (region wr)) 
        /\ sel h1 (seqn wr) = sel h0 (seqn wr) + 1
    // /\ sel h1 (log wr)  = snoc (sel h0 (log wr)) (Entry cipher ad f))
    // modifies at most the writer of (epoch_w c), adding f to its log
    ))
)))

// 15-09-09 Do we need an extra argument for every stateful index?
let send c i f =
  let ct, rg = Content.ct_rg i f in
  let payload = send_payload c i f in
  lemma_repr_bytes_values (length payload);
  //admitP(b2t(repr_bytes (length payload) <= 2)); (*TODO*)
  let record =
    let pv = pickSendPV c in
    Record.makePacket ct pv payload in

  // we need all that to cross an ST function with HyperHeap.modifies Set.empty!
  recall (c_log c); recall (C.reading c);
  (match epoch_w c with
  | None -> ()
  | Some(Epoch h _ w) -> recall (log w); recall (seqn w));

  //15-11-27 we need a trivial framing lemma and scaffolding to carry
  //15-11-27 st_inv c h1 across this call; what's a better style?
  let h0 = ST.get() in 
  let r = Platform.Tcp.send (C.tcp c) record in
  frame_admit c h0 (ST.get());
  match r with
    | Error(x)  -> Error(AD_internal_error,x)
    | Correct _ -> Correct()


(* not needed as long as st_inv is trivial
assume val admit_st_inv: c: connection -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 = h1 /\ st_inv h1 c))
*)


(* which fragment should we send next? *)
(* we must send this fragment before restoring the connection invariant *)

//* pick & send one pending message from any protocol state, in two modes:
//* when writing for the application code, we may send is_Some ghost.
//* when writing while reading, is_None ghost.
//* the result ranges over...
//* | WriteDone         when is_None ghost, notifying there is nothing left to send
//* | Written when is_Some ghost, notifying the appdata fragment was sent
//* | WriteError (unrecoverable \/ after sending alert)
//* | SentClose
//* | WriteAgain | WriteAgainFinishing | WriteAgainClosing
//* | WriteHSComplete
//* the state changes accordingly.
// 
val writeOne: c:connection -> i:id -> appdata: option (rg:frange i & DataStream.fragment i rg) -> ST ioresult_w
  (requires (fun h ->
    st_inv c h /\ 
    (let o = epoch_w_h c h in
      i == epoch_id o /\
      (is_Some o ==> is_seqn (sel h (seqn (writer_epoch (Some.v o))) + 1)))))
  (ensures (fun h0 r h1 ->
    st_inv c h1 /\
//    modifies (Set.singleton (C.region c)) h0 h1 /\
    // TODO: conditionally prove that i == epoch_id (epoch_w_h c h), at least when appdata is set.
    // TODO: account for (the TLS view of) the encryptor log
    True
  ))


let writeOne c i appdata =
  let writing = !c.writing in
  match writing with
  | Closed -> WriteError None (perror __SOURCE_FILE__ __LINE__ "Trying to write on a closed connection")
  | _      -> 
      recall (c_log c); recall (C.reading c); // needed to get stability for i across ST calls
      let o = epoch_w c in
      (match o with
      | None -> ()
      | Some(Epoch h _ w) -> recall (log w); recall (seqn w));
  
      let h0 = ST.get() in
      let alert_response = Alert.next_fragment i (C.alert c) in 
      let h1 = ST.get() in 
      frame_admit c h0 h1;
      match alert_response with // alerts have highest priority
      | Alert.ALFrag rg f ->
          ( match writing with
            | Init | FirstHandshake _ | Open | Closing _ ->
              ( match send c #i (Content.CT_Alert rg f) with
                | Correct()   -> WriteAgain
                | Error (x,y) -> unrecoverable c y)
            | _ -> unrecoverable c (perror __SOURCE_FILE__ __LINE__ "Sending alert message in wrong state"))

      | Alert.LastALFrag rg f ad ->
          ( match writing with
            | Init | FirstHandshake _ | Open | Closing _ ->
              (* We're sending a fatal alert. Send it, then close both sending and receiving sides *)
              ( match send c #i (Content.CT_Alert rg f) with
                | Correct() ->
                    let reason = match writing with | Closing(_,reason) -> reason | _ -> "" in
                    closeConnection c;
                    WriteError (Some ad) reason
                | Error (x,y) -> unrecoverable c y )
            | _ -> unrecoverable c (perror __SOURCE_FILE__ __LINE__ "Sending alert message in wrong state"))

      | Alert.LastALCloseFrag rg f ->
          ( match writing  with
            | Init | FirstHandshake(_) | Open ->
            (* Not Closing: this is a graceful closure, should not happen in case of fatal alerts *)
            (* We're sending a close_notify alert. Send it, then only close our sending side.
               If we already received the other close notify, then reading is already closed,
               otherwise we wait to read it, then close. But do not close here. *)
              ( match send c #i (Content.CT_Alert rg f) with
                | Correct()   -> c.writing := Closed; frame_admit c h1 (ST.get()); SentClose //FIXME
                | Error (x,y) -> unrecoverable c y)
            | _ -> unrecoverable c (perror __SOURCE_FILE__ __LINE__ "Sending alert message in wrong state"))

      | Alert.EmptyALFrag -> 
          ( let hs_response = Handshake.next_fragment c.hs in
            let h2 = ST.get() in 
            frame_admit c h1 h2;
            match hs_response with // next we check if there are outgoing Handshake messages
            | Handshake.OutCCS -> (* send a (complete) CCS fragment *)
                ( match writing with
(* 
                  | FirstHandshake(_) | Open ->
                      ( let i = epoch_id (epoch_w c) in // change epoch!
                        match send c #i (Content.CT_CCS #i) with //15-11-27 wrong epoch?
                        | Correct _ ->
                            (* We don't care about next write state, because we're going to reset everything after CCS *)
                            (* Now: - update the index and the state of other protocols
                                    - move the outgoing state to Finishing, to signal we must not send appData now. *)

                            // we should now get the new epoch's pristine state as a postcondition of Handshake.next_fragment
                            // let nextWCS = Record.initConnState nextID.id_out Writer nextWrite in
                            // let new_ad = AppData.reset_outgoing id c.appdata nextID in
                            c.writing := Finishing;
                            Alert.reset_outgoing c.alert;
                            frame_admit c h0 (ST.get());
                            WriteAgainFinishing
                        | Error (x,y) -> unrecoverable c y)
*)
                  | _ -> closable c (perror __SOURCE_FILE__ __LINE__ "Sending CCS in wrong state"))
            | Handshake.OutSome rg f -> (* send some handshake fragment *)
                ( match writing with
                  | Init | FirstHandshake(_) | Finishing | Open ->
                      ( match send c #i (Content.CT_Handshake rg f) with
                        | Correct()   -> WriteAgain
                        | Error (x,y) -> unrecoverable c y)
                  | _ -> closable c (perror __SOURCE_FILE__ __LINE__ "Sending handshake messages in wrong state"))

            | Handshake.OutFinished rg last_fragment -> (* check we are finishing & send last fragment *)
                ( match writing with
                  | Finishing ->
                      ( match send c #i (Content.CT_Handshake rg last_fragment) with
                        | Correct()   -> c.writing := Finished; frame_admit c h2 (ST.get()); WriteAgain (* TODO 15-09-11 recheck, was WriteFinished *)
                                                                          (* also move to the Finished state *)
                        | Error (x,y) -> unrecoverable c y)
                  | _ -> closable c (perror __SOURCE_FILE__ __LINE__ "Sending handshake message in wrong state"))

            | Handshake.OutComplete rg last_fragment ->
                ( match writing, !c.reading with
                  | Finishing, Finished -> (* Send the last fragment *)
                      ( match send c #i (Content.CT_Handshake rg last_fragment) with
                        | Correct() -> moveToOpenState c; WriteHSComplete (* Move to the new state *)
                            // removed sanity check: in and out session infos should be the same
                            //if !C_reading c) epochSI id.id_in = epochSI id.id_out then
                            //else unrecoverable c (perror __SOURCE_FILE__ __LINE__ "Invalid connection state")
                        | Error (x,y) -> unrecoverable c y)
                  | _ -> closable c (perror __SOURCE_FILE__ __LINE__ "Sending handshake message in wrong state"))

            | Handshake.OutIdle -> // finally attempt to send some application data if we're in Open state
                ( match writing with
                  | Open ->
                    ( match appdata with
                      | None          -> WriteDone
                      | Some (|rg,f|) ->
                        ( match send c (Content.CT_Data rg f) with
                          | Correct()   -> Written (* Fairly, tell we're done, and we won't write more data *)
                          | Error (x,y) -> unrecoverable c y))
                  | _ -> WriteDone) // We are finishing a handshake. Tell we're done; the next read will complete it.
          )


(*** VERIFIES UP TO HERE ***)


(* yuck.
type BufInvariant h c =
	CnBuf_o c = None \/
	(?r,f,s,d.
      MsgOBytes(c,(r,d)) = AppFragment.Payload(Id(ConnectionEpochOut(c)),r,f) /\
			CnBuf_o(c) = Some((r,f,s)) /\
			s = AppFragment.Extend(ConnectionEpochOut(c),CnStream_o(c),r,f))

private val writeAllClosing: c:Connection -> ST writeOutcome
  (requires (fun h -> BufInvariant h c))
  (ensures (fun h0 wo h1 ->
      c' is nextCn c /\ CnBuf_o c' = CnBuf_o c /\
      (is_WriteError wo /\ is_SentFatal wo \/
	    (wo = SentClose /\ (Auth(ConnectionEpochIn(c)) => EvClose(CnInfo(c).id_in,Bytes_i(c)))))))
*)


val no_seqn_overflow: c: connection -> ST bool 
  (requires (fun h -> st_inv c h))
  (ensures (fun h0 b h1 -> 
    h0 == h1 /\
    st_inv c h1 /\
    (let o = epoch_w_h c h1 in
    (b /\ is_Some o ==> is_seqn (sel h1 (seqn (writer_epoch (Some.v o))) + 1)))))

let no_seqn_overflow c = 
  recall (c_log c); recall (C.reading c); // needed to get stability for i across ST calls
  let o = epoch_w c in
  match o with
  | None -> true
  | Some(Epoch h _ w) -> 
      let n = !(seqn w) + 1 in
      if n >= 72057594037927936 && n < 18446744073709551616 
      then (lemma_repr_bytes_values n; true)
      else false


//* (ensures r = WriteError | SentClose)
//* unless we have a strong pre, this relies on dynamic checks

val writeAllClosing: c:connection -> i:id -> ST ioresult_w
  (requires (fun h -> st_inv c h /\ i == epoch_id (epoch_w_h c h)))
  (ensures (fun h0 r h1 ->
    st_inv c h1 /\
    //modifies (Set.singleton (C.region c)) h0 h1 /\
    (is_WriteError r \/ is_SentClose r)
  ))

let rec writeAllClosing c i =
    if no_seqn_overflow c then 
    match writeOne c i None with
    | WriteAgain          -> writeAllClosing c (admit(); epoch_id (epoch_w c)) // can't use i? // TODO
    | WriteError x y      -> WriteError x y
    | SentClose           -> SentClose
    | _                   -> unexpected "[writeAllClosing] writeOne returned wrong result"
    else                    unexpected "[writeAllClosing] seqn overflow"

//* (ensures r = ... WriteError | SentClose | MustRead | WriteHSComplete

val writeAllFinishing: c:connection -> i:id -> ST ioresult_w
  (requires (fun h -> st_inv c h /\ i == epoch_id (epoch_w_h c h)))
  (ensures (fun h0 r h1 ->
    st_inv c h1 /\
    //modifies (Set.singleton c.region) h0 h1 /\
    (is_WriteError r \/ is_SentClose r \/ is_MustRead r \/ is_Written r)
  ))
let rec writeAllFinishing c i =
    if no_seqn_overflow c then 
    match writeOne c i None with
    | WriteAgain          -> writeAllFinishing c (admit(); epoch_id (epoch_w c)) // TODO
    | WriteAgainClosing   -> writeAllClosing c (admit(); epoch_id (epoch_w c))  // TODO
    | WriteError x y      -> WriteError x y
    | SentClose           -> SentClose
    | MustRead            -> MustRead
    | Written             -> Written
    | _                   -> unexpected "[writeAllFinishing] writeOne returned wrong result"
    else                    unexpected "[writeAllFinishing] seqn overflow"

//* called both by read (ghost = None) and write (ghost = data being sent)
//* returns to both: WriteError
//* returns only to read: SentClose, WriteDone
//* returns only to write: Written, MustRead
//* what about WriteHSComplete ?

val writeAllTop: c:connection -> i:id -> appdata: option (rg:frange i & DataStream.fragment i rg) -> ST ioresult_w
  (requires (fun h -> st_inv c h /\ i == epoch_id (epoch_w_h c h)))
  (ensures (fun h0 r h1 ->
    st_inv c h1 /\
    //modifies (Set.singleton (C.region c)) h0 h1 /\
    True)
  )

let rec writeAllTop c i appdata =
    if no_seqn_overflow c then 
    match writeOne c i appdata with
//TODO | WriteAgain          -> writeAllTop c i appdata 
    | WriteAgainClosing   -> writeAllClosing c (admit(); epoch_id (epoch_w c)) // TODO
    | WriteAgainFinishing -> writeAllFinishing c (admit(); epoch_id (epoch_w c)) // TODO
    | WriteError x y      -> WriteError x y
    | SentClose           -> SentClose
    | WriteDone           -> WriteDone
    | MustRead            -> MustRead
    | Written             -> Written
    | _                   -> unexpected "[writeAllTop] writeOne returned wrong result"
    else                    unexpected "[writeAllTop] seqn overflow"

let write c i rg data = writeAllTop c i (Some (| rg, data |))

(*
// prior spec-level abbreviations?
let session h c = sel h (HS.log (C.hs c))
let writer h c = sel h (C.writing c), c_written h c
let reader h c = sel h (C.reading c), c_read h c

// We don't get MustRead with writing Open as precondition,
// assuming that read's DontWrite reliably signals it.
val write: c:connection -> i: id -> rg:frange i -> data:DataStream.fragment i rg -> ST ioresult_o
  (requires (fun h ->
    st_inv h c /\
    sel h (C.writing c) = Open
    ))
    // the connection is writable: see CanWrite(CnInfo(c))
  (ensures (fun h0 result h1 ->
    st_inv h1 c /\
    HyperHeap.modifies (Set.singleton (C.region c)) h0 h1 /\
    (result = Written ==> (
      session h1 c = session h0 c /\
      reader h1 c = reader h0 c /\
      writer h1 c = append  (writer h0 c) (Data d)
      //sel h1 (C.writing c) = Open  /\
      //c_written h1 c = snoc (c_written h0 c) d /\
      //sel h1 (C.reading c) = sel h0 (C.reading c) /\
      //c_read h1 c = c_read h0 c
      )) /\
    (is_WriteError result ==> (
      sel h1 (C.writing c) = Closed  /\
      sel h1 (C.reading c) = Closed  /\
      c_written h1 c = c_written h0 c /\
      c_read h1 c = c_read h0 c
      // not sure we can be so precise
      ))
  ))
*)

//---------------------reading (with inplicing writing)---------------------

// FIXME: Put the following definitions close to range and delta, and use them

type query = Cert.chain
type msg_i (i:id) = (range * DataStream.delta)

(* merged with ioresult_i
type readOutcome (e:epoch) =
    | WriteOutcome of writeOutcome    // now? { ReadError, DontWrite, CompletedSecond, Read(Close) }
    | RError of string (* internal *) // now ReadError(None,err)
    | CertQuery of query * bool       // now CertQuery
    | RHSDone                         // now CompletedFirst
    // now Read(delta e) with subcases Data, Close, Alert
    | RAppDataDone of msg_i | RClose
    | RFatal of alertDescription (* The alert we received *)
    | RWarning of alertDescription (* The alert we received *)
    // internal states only
    | ReadAgain | ReadAgainFinishing | ReadFinished *)



type ioresult_i (e:epoch) =
    | Read of DataStream.delta e
        // this delta has been added to the input stream; we may have read
        // - an application-data fragment or a warning (leaving the connection live)
        // - a closure or a fatal alert (tearing down the connection)
        // If the alert is a warning, the connection remains live.
        // If the alert is final, the connection has been closed by our peer;
        // the application may reuse the underlying TCP stream
        // only after normal closure (a = AD_close_notify)

    | ReadError of option alertDescription * string
        // We encountered an error while reading, so the connection dies.
        // we return the fatal alert we may have sent, if any,
        // or None in case of an internal error.
        // The connection is gone; its state is undefined.

    | CertQuery of query * bool
        // We received the peer certificates for the next epoch, to be authorized before proceeding.
        // the bool is what the Windows certificate store said about this certificate.
    | CompletedFirst
        // Handshake is completed, and we have already sent our finished message,
        // so only the incoming epoch changes
    | CompletedSecond
        // Handshake is completed, and we have already sent our finished message,
        // so only the incoming epoch changes
    | DontWrite
        // Nothing read yet, but we can't write anymore.

    // internal states only
    | ReadAgain
    | ReadAgainFinishing
    | ReadFinished


// frequent error handler
let alertFlush conn x y =
  abortWithAlert conn x y;
  let written = writeAllClosing conn in
  match written with
  | SentClose      -> Read Close // do we need this case?
  | WriteError x y -> ReadError x y

//* private val getHeader: c:Connection -> ST (Result ((ct:ContentType * len:nat){len > 0 /\ len <= max_TLSCipher_fragment_length}))
//*   (requires (fun h -> True))
//*   (ensures (fun h0 r h1 -> h0 = h1))
//* we should require the c.read is not Closing \/ Closed
let getHeader (Conn(id,c)) =
    match Platform.Tcp.read c.ns 5 with // read & parse the header
    | Error x -> Error(AD_internal_error,x)
    | Correct header ->
      match Record.parseHeader header with
      | Error x -> Error x
      | Correct(res) ->
        let (ct,pv,len) = res in
        let c_read = c.read in
        match c_read.disp with
        | Init                 -> correct(ct,len)
        | FirstHandshake expPV ->
            if pv = expPV then correct(ct,len)
            else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Protocol version check failed")
        | Finishing
        | Finished
        | Open ->
            let si = epochSI id.id_in in
            if pv = si.protocol_version then correct(ct,len)
            else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Protocol version check failed")
        | _ -> unexpected "[recv] invoked on a closed connection"

//* private val getFragment: c:connection -> ct:ct -> len:nat -> ST (rg * msg)
//* "stateful, but only affecting the StAE instance"
//* can we even deduce the range from len?
let getFragment (Conn(id,c)) ct len =
    match Platform.Tcp.read c.ns len with
    | Error x -> Error(AD_internal_error,x)
    | Correct payload ->
        let c_read = c.read in
        let c_read_conn = c_read.conn in
        Record.recordPacketIn id.id_in c_read_conn ct payload

(* we receive, decrypt, verify a record (ct,f); what to do with it? *)
//private val readOne: Connection -> ST ioresult_i //$ which epoch index to use??
//  (ensures ioresult is not CompletedFirst | CompletedSecond | DontWrite)

let readOne cn =
    let Conn(id,c) = cn in
    let reading = c.read.disp in
    match reading with
        | Closed -> //* statically exclude it?
            alertFlush cn AD_internal_error (perror __SOURCE_FILE__ __LINE__ "Trying to read from a closed connection")
        | _ ->
            match getHeader cn with
            | Error (x,y)      -> alertFlush cn x y
            | Correct (ct,len) ->
                let history = Record.history id.id_in Reader c_read.conn in
                match (ct,c_read.disp) with // process received content type depending on the current read state
                | (Alert, Init)
                | (Alert, FirstHandshake _)
                | (Alert, Open) ->
                    ( match getFragment cn ct len with
                      | Error (x,y)  -> alertFlush cn x y
                      | Correct fragment ->
                            let rg, frag = fragment in
                            let f = TLSFragment.recordPlainToAlertPlain id.id_in history rg frag in
                            match Alert.recv_fragment id c.alert rg f with
                              | Error (x,y) -> alertFlush cn x y
                              | Correct Alert.Ack -> ReadAgain
                              | Correct Alert.CloseNotify ->
                                     (* An outgoing close notify has already been buffered, if necessary *)
                                     (* Only close the reading side of the connection *)
                                   c.read := {c_read with disp = Closed};
                                   Read Close
                              | Correct (Alert.Description ad) ->
                                   if isFatal ad then closeConnection cn; // closing both directions
                                   // otherwise we carry on; the user will know what to do
                                   Read (Alert ad) )

                | (Handshake, Init)
                | (Handshake, FirstHandshake _)
                | (Handshake, Finishing)
                | (Handshake, Open) ->
                    ( match getFragment cn ct len with
                        | Error (x,y) -> alertFlush cn x y
                        | Correct (c_recv, rg, frag) ->
                          let c_read = {c_read with conn = c_recv} in
                          let c = {c0 with read = c_read} in
                          let f = TLSFragment.recordPlainToHSPlain id.id_in history rg frag in
                          let res = Handshake.recv_fragment id c.handshake rg f in
                          match res with
                          | Handshake.InError x y -> alertFlush cn x y
                          | Handshake.InAck       -> ReadAgain
                          | Handshake.InVersionAgreed pv ->
                              (match c_read.disp with
                              | Init ->
                                  (* Then, also c_write must be in Init state. It means this is the very first, unprotected,
                                      handshake of the connection, and we just negotiated the version.
                                      Set the negotiated version in the current sinfo (read and write side),
                                      and move to the FirstHandshake state, so that
                                      protocol version will be properly checked *)
                                  c.read  := {c_read  with disp = FirstHandshake pv };
                                  c.write := {c.write with disp = FirstHandshake pv };
                                  ReadAgain
                              | _ -> ReadAgain (* We are re-negotiating, using the current version number;
                                                  so no need to change --- but we should still check pv is unchanged. *)
                          | Handshake.InQuery query advice -> CertQuery query advice
                          | Handshake.InFinished ->
                                ( match c_read.disp with (* Ensure we are in Finishing state *)
                                    | Finishing ->
                                        c.read := {c_read with disp = Finished};
                                        ReadFinished
                                    | _ -> alertFlush cn AD_internal_error (perror __SOURCE_FILE__ __LINE__ "Finishing handshake in the wrong state"))
                          | Handshake.InComplete ->
                                ( match (c.read.disp, c.write.disp) with (* Ensure we are in the correct state *)
                                    | Finishing, Finished -> (* Sanity check: in and out session infos should be the same *)
                                        if epochSI(id.id_in) = epochSI(id.id_out) then
                                          match moveToOpenState cn with
                                          | Correct(c) -> CompletedFirstDone
                                          | Error(x,y) -> alertFlush cn x y
                                        else closeConnection cn; ReadError None (perror __SOURCE_FILE__ __LINE__ "Invalid connection state")
                                    | _ -> alertFlush cn AD_internal_error (perror __SOURCE_FILE__ __LINE__ "Invalid connection state"))))

                | (Change_cipher_spec, FirstHandshake _)
                | (Change_cipher_spec, Open) ->
                      ( match getFragment cn ct len with
                        | Error (x,y) -> alertFlush cn x y
                        | Correct recf ->
                            let rg, frag = recf in
                            let f = TLSFragment.recordPlainToCCSPlain id.id_in history rg frag in
                            match Handshake.recv_ccs id c.handshake rg f with
                              | InCCSError (x,y) -> alertFlush cn x y
                              | InCCSAck (nextID,nextR) ->
                                  (* We know statically that Handshake and Application data buffers are empty.
                                   * We check Alert. We are going to reset the Alert buffer anyway, so we
                                   * never concatenate buffers of different epochs. But it is nicer to abort the
                                   * session if some buffers are not in the expected state. *)
                                  if Alert.is_incoming_empty id c.alert then
                                      let nextRCS = Record.initConnState nextID.id_in Reader nextR in
                                      let new_ad = AppData.reset_incoming id c.appdata nextID in
                                      let new_al = Alert.reset_incoming id c.alert nextID in
                                      c.read := {c_read with disp = Finishing; conn = nextRCS};
                                      c.appdata := new_ad;
                                      c.alert := new_al;
                                      c.id := nextID; //* adjust
                                      ReadAgainFinishing
                                   else
                                      alertFLush (Conn(id,c)) AD_handshake_failure (perror __SOURCE_FILE__ __LINE__ "Changing epoch with non-empty buffers"))

                | Application_data, Open ->
                    ( match getFragment cn ct len with
                        | Error (x,y) -> alertFlush cn x y
                        | Correct (rg,frag) ->
                            let f = TLSFragment.recordPlainToAppPlain id.id_in history rg frag in
                            let d = AppData.recv_fragment id c.appdata rg f in
                            Read (Data rg d) )

                | _, Init
                | _, FirstHandshake(_)
                | _, Finishing
                | _, Finished
                | _, Closed
                | _, Closing(_,_) ->  alertFlush cn AD_unexpected_message (perror __SOURCE_FILE__ __LINE__ "Message type received in wrong state")

//* ?
//* private val sameID: c0:Connection -> c1:Connection ->
//* 	o0: readOutcome c0 {IOResult_i(c0,c1,o0)} ->
//* 	c2: nextCn c0 { CnStream_i(c0) = CnStream_i(c2) /\
//*                   CnStream_o(c0) = CnStream_o(c2)} ->
//* 	o1: readOutcome c2 {o0 = o1 /\ IOResult_i(c2,c1,o1)}
(*
let sameID (c0:Connection) (c1:Connection) res (c2:Connection) =
    match res with
    | WriteOutcome(x) -> WriteOutcome(x)
    | RError(x) -> RError(x)
    | ReadAgain -> ReadAgain
    | ReadAgainFinishing -> ReadAgainFinishing
    | RAppDataDone(x) -> RAppDataDone(x)
    | CertQuery(x,y) -> CertQuery(x,y)
    | ReadFinished -> ReadFinished
    | RHSDone -> RHSDone
    | RClose -> RClose
    | RFatal(x) -> RFatal(x)
    | RWarning(x) -> RWarning(x)

let sameID2 (c0:Connection) (c1:Connection) res (c2:Connection) =
    match res with
    | WriteOutcome(x) -> WriteOutcome(x)
    | RError(x) -> RError(x)
    | ReadAgain -> ReadAgain
    | ReadAgainFinishing -> ReadAgainFinishing
    | RAppDataDone(x) -> RAppDataDone(x)
    | CertQuery(x,y) -> CertQuery(x,y)
    | ReadFinished -> ReadFinished
    | RHSDone -> RHSDone
    | RClose -> RClose
    | RFatal(x) -> RFatal(x)
    | RWarning(x) -> RWarning(x)

let sameIDRAF (c0:Connection) (c1:Connection) res (c2:Connection) =
    match res with
    | WriteOutcome(x) -> WriteOutcome(x)
    | RError(x) -> RError(x)
    | ReadAgain -> ReadAgain
    | ReadAgainFinishing -> ReadAgainFinishing
    | RAppDataDone(x) -> RAppDataDone(x)
    | CertQuery(x,y) -> CertQuery(x,y)
    | ReadFinished -> ReadFinished
    | RHSDone -> RHSDone
    | RClose -> RClose
    | RFatal(x) -> RFatal(x)
    | RWarning(x) -> RWarning(x)
*)

let rec readAllFinishing cn =
    let outcome = readOne cn in
    match outcome with
    | ReadAgain      -> readAllFinishing cn //? cut: let ro = sameIDRAF c newConn ro c0 in
    | CompletedFirst -> CompletedFirst
    | Read (Alert ad) when isFatal ad -> outcome
    | ReadError _    -> unexpected "[readAllFinishing] Read error can never be returned by read one"
    | ReadFinished   ->
        ( let written = writeAllTop c None in
          match written with
          | WriteHSComplete
          | WriteError _ _ -> WriteOutcome outcome
          | SentFatal(x,y) -> unexpected "[readAllFinishing] There should be no way of sending a fatal alert after we validated the peer Finished message"
          | SentClose      -> unexpected "[readAllFinishing] There should be no way of sending a closure alert after we validated the peer Finished message"
          | _              -> unexpected "[readAllFinishing] writeAllTop should never return such write outcome")
    | ReadAgainFinishing | RAppDataDone(_) | CertQuery(_,_) -> unexpected "[readAllFinishing] readOne returned wrong result"
    | WriteOutcome(SentFatal(x,y)) -> WriteOutcome(SentFatal(x,y))
    | WriteOutcome(WError(x))      -> WriteOutcome(WError(x))
        (* This and the following two corner cases are underspecified in RFC 5246, and we handle them by tearing down the connection.
           These are inconsistent states of the protocol that should be explicitly forbidden by the RFC.
           In this case, sending our CCS already implicitly closed the previous sending epoch, and the new epoch is not open
           yet, so there's nothing to close. *)

    | Read Close
        (* This is the dual of the case above: we received the CCS, which implicitly closed the receiving epoch,
           and the new epoch is not open yet, so we can neither receive authenticated data, nor close this epoch.  *)
    | Read (Alert ad) when not (isFatal ad) ->
        (* As above, the receiving epoch is closed, so we cannot receive authenticated data. *)
         ReadError None (perror __SOURCE_FILE__ __LINE__ "Trying to close an epoch after CCS has been sent, but before new epoch opened.")

let rec read cn =
    match writeAllTop cn None with
    | SentClose       -> Read Close
    | WriteError x y  -> ReadError x y
    | WriteFinished   -> DontWrite
    | WriteDone       -> // There was nothing to write
      ( let res = readOne c in
        match res with
        | ReadAgain          -> read c             //*? removed: sameID c newConn res c0 in
        | ReadAgainFinishing -> readAllFinishing c //*? removed: sameID2 c newConn res c0 in
        | Read delta         -> Read delta
        | ReadError x y      -> ReadError x y
        | CertQuery q adv    -> CertQuery q adv
        | Read Close         -> //*$ review this postprocessing
          ( let (Conn(id,conn)) = cn in
            match conn.write.disp with
            | Closed -> Read Close // we already sent a close_notify, tell the user it's over
            | _ ->
                let written = writeAllClosing c in
                match written with
                | SentClose      -> Read Close // clean shutdown
                | WriteError x y -> ReadError x y
                | _              -> ReadError None (perror __SOURCE_FILE__ __LINE__ "") // internal error
                ))
        //_ CompletedFirst | CompletedSecond | DontWrite -> unexpected "[read] readOne should never return such write outcome"

// -----------------------------------------------------------------------------


let authorize c q =
    let res = Handshake.authorize (C.hs c) q in
    // AP: BEGIN: Inlined from handleHandshakeOutcome
    match res with
    | Handshake.InAck -> read c
        //? removed: let res = sameID (Conn(id,c1)) newConn res (Conn(id,c)) in
    | Handshake.InVersionAgreed pv ->
        (match !c.reading, !c.writing with
        | Init, Init  ->
            (* Then, also c_write must be in Init state. It means this is the very first, unprotected,
                handshake on the connection, and we just negotiated the version.
                Set the negotiated version in the current sinfo (read and write side),
                and move to the FirstHandshake state, so that
                protocol version will be properly checked *)
            c.reading := FirstHandshake pv;
            c.writing := FirstHandshake pv
            read c
            //? removed: let res = sameID (Conn(id,c1)) newConn res (Conn(id,c)) in

        | _ -> (* It means we are doing a re-negotiation. Don't alter the current version number, because it
                    is perfectly valid. It will be updated after the next CCS, along with all other session parameters *)
            read c)
            //? removed: let res = sameID (Conn(id,c1)) newConn res (Conn(id,c)) in

    | Handshake.InQuery _    -> unexpected "[authorize] A query should never be received"
    | Handshake.InFinished   -> unexpected "[authorize] The finished message should never be received right after a query"
    | Handshake.InComplete   -> unexpected "[authorize] Handshake should never complete right after a query"
    | Handshake.InError(x,y) -> alertFlush c x y

    // AP: END: Inlined from handleHandshakeOutcome

let refuse c (q:query) =
    let reason = perror __SOURCE_FILE__ __LINE__ "Remote certificate could not be verified locally" in
    abortWithAlert c AD_unknown_ca reason;
    writeAllClosing c

let full_shutdown c = Alert.send_alert id !c.alert AD_close_notify

let half_shutdown c =
    Alert.send_alert id !c.alert AD_close_notify;
    writeAllClosing c

//let getEpochIn  (Conn(id,state)) = id.id_in
//let getEpochOut (Conn(id,state)) = id.id_out
//let getInStream  (Conn(id,state)) = AppData.inStream  id state.appdata
//let getOutStream (Conn(id,state)) = AppData.outStream id state.appdata
