module TLS

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found
open FStar.Set

open Platform
open Platform.Bytes
open Platform.Error
open Platform.Tcp

open TLSError
open TLSConstants
open TLSInfo

open Range
open StAE
open Handshake
open Connection

open MonotoneSeq
open FStar.Monotonic.RRef
module HH = HyperHeap

(* #set-options "--lax" *)

(* #set-options "--initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0" *)

//allowing inverting optResult without having to globally increase the fuel just for this
// Will add a lemma to Platform.Error so that we don't have this ugly assume here
assume InvertOptResult: forall (a:Type) (b:Type) (x:optResult a b). is_Error x \/ is_Correct x 
(* let invertOptResult (a:Type)  (b:Type) (x:optResult a b) *)
(*   : Lemma (requires True) *)
(* 	  (ensures (is_Error x \/ is_Correct x)) *)
(* 	  [] *)
(*   = () *)


// using also Alert, DataStream, Content, Record

//16-05-10 TEMPORARY disable StatefulLHAE.fst to experiment with StreamAE.

let id = i:id{ is_stream_ae i }

// temporary scaffolding
assume val frame_admit: c:connection -> h0:HyperHeap.t -> h1:HyperHeap.t -> Lemma
  (requires True)
  (ensures epochs c h0 = epochs c h1)

// too convenient; should move to a library
// JP: isn't failwith sufficient enough? CF: this one works in ST. 
val unexpected: #a:Type -> v:string -> ST a
  (requires (fun h -> True))
  (ensures (fun _ _ _ -> False ))

let rec unexpected #a s = unexpected s


(*** control API ***)


type rid = r: HH.rid { disjoint r TLSConstants.tls_region } 
//16-05-12 should we use a color for connection regions?

// was connect, resume, accept_connected, ...
val create: r0:rid -> tcp:networkStream -> r:role -> cfg:config ->
//            resume: option (sid: sessionID { r = Client }) -> //NS: This style should be considered an anti-pattern; it requires an inversion of option to prove this post-condition:     (r = Server ==> resume = None) /\ 
            resume: resume_id r  ->
            ST connection
  (requires (fun h ->  True))
  (ensures (fun h0 c h1 ->
    fresh_region c.region h0 h1 /\
    c_role c = r /\
    c_cfg c = cfg /\
    c_resume c = resume /\
    c.tcp = tcp  /\
    modifies Set.empty h0 h1 /\
    extends c.region r0 /\
    (* (r = Server ==> resume = None) /\  *)
    Map.contains h1 c.region /\ //NS: may be removeable: we should get it from fresh_region
    sel h1 (c_log c) = Seq.createEmpty /\ 
    sel h1 c.state = BC /\
    True
    ))



let create parent tcp role cfg resume =
    let m = new_region parent in
    let hs = Handshake.init m role cfg resume in
    let al = Alert.init m in
    let state = ralloc m BC in
    C #m hs al tcp state

//TODO upgrade commented-out types imported from TLS.fsti
// type initial (role: role) (ns:Tcp.networkStream) (c:config) (resume: option sessionID) (cn:connection) (h: HyperHeap.t) =
//     extends (c_rid cn) root /\ // we allocate a fresh, opaque region for the connection
//     c_role cn   = role /\
//     c_tcp cn    = ns /\
//     c_resume cn = resume /\
//     c_cfg cn = c /\
//     HyperHeap.sel h (C.reading cn) = Init /\ // assuming Init epoch implicitly have no data sent/received
//     HyperHeap.sel h (C.writing cn) = Init

// painful to specify?
//* should we still return ConnectionInfo ?
//* merging connect and resume with an optional sessionID
//val connect: ns:Tcp.networkStream -> c:config -> resume: option sessionID -> ST connection
//  (requires (fun h0 -> True))
//  (ensures (fun h0 cn h1 ->
//    modifies Set.empty h0 h1 /\
//    initial Client ns c resume cn h1
//    //TODO: even if the server declines, we authenticate the client's intent to resume from this sid.
//  ))
let connect m0 tcp r cfg        = create m0 tcp Client cfg None
let resume  m0 tcp r cfg sid    = create m0 tcp Client cfg (Some sid)
//val accept_connected: ns:Tcp.networkStream -> c:config -> ST connection
//  (requires (fun h0 -> True))
//  (ensures (fun h0 cn h1 ->
//    modifies Set.empty h0 h1 /\
//    initial Server ns c None cn h1
//  ))
let accept_connected m0 tcp cfg = create m0 tcp Server cfg None

//* do we need accept and accept_connected?
//val accept: Tcp.tcpListener -> c:config -> ST connection
//  (requires (fun h0 -> True))
//  (ensures (fun h0 cn h1 ->
//    modifies Set.empty h0 h1 /\
//    (exists ns. initial Server ns c None cn h1)
//  ))
let accept m0 listener cfg =
    let tcp = Platform.Tcp.accept listener in
    accept_connected m0 tcp cfg

//val rehandshake: cn:connection { c_role cn = Client } -> c:config -> ST unit
//  (requires (fun h0 -> True))
//  (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 // no visible change in cn
//  ))
let rehandshake c ops = Handshake.rehandshake (C.hs c) ops
// the client can ask for rekeying --- no immediate effect
//val rekey: cn:connection { c_role cn = Client } -> ST unit
//  (requires (fun h0 -> True))
//  (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 // no visible change in cn
//  ))
let rekey c ops       = Handshake.rekey       (C.hs c) ops
//val request: cn:connection { c_role cn = Server } -> c:config -> ST unit
//  (requires (fun h0 -> True))
//  (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 // no visible change in cn
//  ))
let request c ops     = Handshake.request     (C.hs c) ops


(*** current epochs ***)

// the index of messages depends on the connection state,
// and may be different for reading and for writing.

val no_seqn_overflow: c: connection -> ST bool
  (requires (fun h -> st_inv c h))
  (ensures (fun h0 b h1 ->
    let es = sel h1 c.hs.log in
    let j = iT c.hs Writer h1 in
    j < Seq.length es /\
    h0 == h1 /\
    (b /\ j >= 0) ==> (
    let e = Seq.index es j in
    incrementable (writer_epoch e)) h0))

let no_seqn_overflow c =
  let es = !c.hs.log in
  let j = Handshake.i c.hs Writer in
  if j < 0 then
    true
  else (
    let e = Seq.index es j in 
    let h = ST.get() in 
    assume(incrementable (writer_epoch e) h); 
    true )
// JP: placeholder while I fix the int64 problem
    (* 
    let n = !(seqn w) + 1 in
    if n >= 72057594037927936 && n < 18446744073709551616
    then (lemma_repr_bytes_values n; true)
    else false *)
    

(*** outgoing ***)

type ioresult_w =
    // public results returned by TLS.send
    | Written             // the application data was written; the connection remains writable
    | WriteError: o:option alertDescription -> txt: string -> ioresult_w // The connection is down, possibly after sending an alert
//  | WritePartial of unsent_data // worth restoring?

    // transient internal results returned by auxiliary send functions
//  | MustRead            // Nothing written, and the connection is busy completing a handshake
    | WriteDone           // No more data to send in the current state
    | WriteHSComplete     // The handshake is complete [while reading]
    | SentClose           // [while reading]
    | WriteAgain          // sent something; there may be more to send (loop)
    | WriteAgainFinishing // outgoing epoch changed; there may be more to send to finish the handshake (loop)
    | WriteAgainClosing   // we are tearing down the connection & must still send an alert (loop)

type ioresult_o = r:ioresult_w { is_Written r \/ is_WriteError r }

// type msg_o (i:id) = (r:range & DataStream.fragment i r)


val moveToOpenState: c:connection -> ST unit
  (requires (fun h ->
     st_inv c h /\ sel h c.state = BC))
  (ensures (fun h0 _ h1 ->
     st_inv c h1 /\
     modifies (Set.singleton (C.region c)) h0 h1 /\
     sel h1 c.state = AD))

let moveToOpenState c = c.state := AD
    

(* Dispatch dealing with network sockets *)
// we need st_inv h c /\ wr > Init ==> is_Some epoch_w

let outerPV c =
  match Handshake.version c.hs with
  | TLS_1p3 -> TLS_1p0
  | pv      -> pv

//15-11-27 illustrating overhead of "unrelated" updates; still missing modifies clauses
val closeConnection: c: connection -> ST unit
  (requires (fun h0 -> st_inv c h0))
  (ensures (fun h0 _ h1 -> st_inv c h1 /\ modifies (Set.singleton (C.region c)) h0 h1))

let closeConnection c =
    invalidateSession c.hs; //changes (HS.region c.hs)
    c.state := Close


// on some errors, we locally give up the connection
let unrecoverable c reason =
    closeConnection c;
    WriteError None reason

// send a final alert then tear down the connection

val abortWithAlert: c:connection -> ad:alertDescription{isFatal ad} -> reason:string -> ST unit
  (requires (fun h0 -> st_inv c h0 /\ sel h0 c.state <> Close))
  (ensures (fun h0 _ h1 ->
    st_inv c h1 /\
    modifies (Set.singleton (C.region c)) h0 h1 /\
    sel h1 c.state = Half Writer
  ))


let abortWithAlert c ad reason =
    invalidateSession c.hs;
    Alert.send c.alert ad;
    c.state := Half Writer

// on some errors, we attempt to send an alert before tearing down the connection
val closable: c:connection -> reason:string -> ST ioresult_w
  (requires (fun h0 -> st_inv c h0 /\ sel h0 c.state <> Close))
  (ensures (fun h0 r h1 ->
    st_inv c h1 /\ modifies (Set.singleton (C.region c)) h0 h1 /\
    sel h1 c.state = Half Writer /\ r = WriteAgainClosing))
let closable c reason =
    abortWithAlert c AD_internal_error reason;
    WriteAgainClosing

// -------------



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

val ct_rg_test : i:id -> f:Content.fragment i -> Tot (ContentType * range)
let ct_rg_test i f = let x, y = Content.ct_rg i f in (x,y)
*)

// sends one fragment in the current epoch;
// except for the null epoch, the fragment is appended to the epoch's writer log.

let epochsT c h = Handshake.logT c.hs h

val send_payload: c:connection -> i:id -> f: Content.fragment i -> ST (encrypted f)
  (requires (fun h ->
    let es = epochsT c h in // implying epochs_inv es
    let j = iT c.hs Writer h in
    st_inv c h /\
    (if j < 0 then i == noId else
       let e = Seq.index es j in
       i = hsId e.h /\
       incrementable (writer_epoch e) h)))
  (ensures (fun h0 payload h1 ->
    let es = epochsT c h0 in
    let j = iT c.hs Writer h0 in
    st_inv c h0 /\
    st_inv c h1 /\
    op_Equality #int j (iT c.hs Writer h1) /\  //16-05-16 would be nice to write just j = iT c.hs Writer h1
    (if j < 0 then i == noId /\ h0 == h1 else 
       let e = Seq.index es j in   
       i = hsId e.h /\ (
       let wr: writer i = writer_epoch e in
       modifies (Set.singleton (region wr)) h0 h1 /\
       seqnT wr h1 = seqnT wr h0 + 1 /\
       (authId i ==> StAE.fragments #i wr h1 = snoc (StAE.fragments #i wr h0) f)
//		     /\ StAE.frame_f (StAE.fragments #i wr) h1 (Set.singleton (StAE.log_region wr)))
       )) /\
    True ))

(* #reset-options "--log_queries --initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0" *)
let send_payload c i f =
    let j = Handshake.i c.hs Writer in
    if j<0 
    then Content.repr i f
    else let es = !c.hs.log in
	 let e = Seq.index es j in 
	 (* let _ = reveal_epoch_region_inv e in *)
	 StAE.encrypt (writer_epoch e) f


(* assume val frame_ae:  *)
(*   h0:HH.t -> h1: HH.t -> c:connection -> Lemma( *)
(*     // restrictions of h0 and h1 to the footprint of st_inv and iT in c are the same /\ *)
(*     st_inv c h0 ==> st_inv c h1 /\ op_Equality #int (iT c.hs Writer h0) (iT c.hs Writer h1)) *)

// used e.g. for writing while reading
let currentId (c:connection) (rw:rw) = 
  let j = Handshake.i c.hs rw in 
  if j<0 then noId 
  else 
    let es = !c.hs.log in
    let e = Seq.index es j in
    let id = hsId e.h in
    if rw = Writer then id else peerId id


// check vs record
let send_requires (c:connection) (i:id) (h:HH.t) = 
    let st = sel h c.state in
    let es = sel h c.hs.log in
    let j = iT c.hs Writer h in
    // j < Seq.length es /\
    st_inv c h /\
    st <> Close /\
    st <> Half Reader /\
    (j < 0 ==> i = noId) /\
    (j >= 0 ==> (
       let e = Seq.index es j in
       let wr = writer_epoch e in 
       Map.contains h (StAE.region wr) /\ //NS: Needed to add this explicitly here. TODO: Soon, we will get this by just requiring mc_inv h, which includes this property
       Map.contains h (StAE.log_region wr) /\ //NS: Needed to add this explicitly here. TODO: Soon, we will get this by just requiring mc_inv h, which includes this property
       i = hsId e.h /\
       incrementable (writer_epoch e) h))
       
val send: c:connection -> #i:id -> f: Content.fragment i -> ST (result unit)
  (requires (send_requires c i))
  (ensures (fun h0 _ h1 ->
    let es = sel h0 c.hs.log in
    let j = iT c.hs Writer h0  in
    let st = sel h0 c.state in
    st_inv c h0 /\
    st_inv c h1 /\
    j == iT c.hs Writer h1 /\ // should follow from the modifies clause
    (if j < 0 then i == noId /\ h0 = h1 else
       let e = Seq.index es j in
       i = hsId e.h /\ (
       let wr: writer i = writer_epoch e in
       modifies (Set.singleton (region wr)) h0 h1 /\
       seqnT wr h1 = seqnT wr h0 + 1 /\
       (authId i ==> StAE.fragments #i wr h1 = snoc (StAE.fragments #i wr h0) f )))))

let send c #i f =
  let pv = outerPV c in
  let ct, rg = Content.ct_rg i f in
  let payload = send_payload c i f in
  lemma_repr_bytes_values (length payload);
  let record = Record.makePacket ct pv payload in
  let r  = Platform.Tcp.send (C.tcp c) record in
  (* let h1 = ST.get() in *)
  (* cut (trigger_frame h1); *)
  match r with
    | Error(x)  -> Error(AD_internal_error,x)
    | Correct _ -> Correct()



(* 
assume val admit_st_inv: c: connection -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 = h1 /\ st_inv h1 c))
*)


// auxiliary functions for projections; floating.
let appfragment (i:id) (o: option (rg:frange i & DataStream.fragment i rg) { is_Some o }) : Content.fragment i =
  match o with
  | Some (| rg, f |) -> Content.CT_Data rg f

let datafragment (i:id) (o: option (rg:frange i & DataStream.fragment i rg) { is_Some o }) : DataStream.delta i =
  match o with
  | Some (| rg, f |) -> let f: DataStream.pre_fragment i = f in //16-05-16 unclear why we now need this step
                       DataStream.Data f

(* 16-05-16 handled in StAE? 

// we should rely on nice libraries... for now inlined from Content.fst
//val fragments_log: #i:id -> es: seq (entry i) -> Tot (seq Content.fragment i)
//let fragments_log i es = Seq.map fragment_entry es

val project_one: #i:id -> entry i -> Tot (option (DataStream.delta i))
let project_one #i en = match fragment_entry en with
   | Content.CT_Data (rg: frange i) d ->
     cut(wider fragment_range rg);
     Some (DataStream.Data d)

   | Content.CT_Alert rg alf -> // alert parsing may fail, or return several deltas
     if length alf = 2
     then match Alert.parse alf with
          | Correct ad -> Some (DataStream.Alert ad)
          | Error _    -> None // ill-formed alert contents are ignored
     else None                 // ill-formed alert packets are ignored

   | _  -> None // other fragments are internal to TLS

let maybe_snoc a b = match b with
  | None -> a
  | Some x -> SeqProperties.snoc a x

val project: #i:id -> fs:seq (entry i) -> Tot(seq (DataStream.delta i))
  (decreases %[Seq.length fs]) // not-quite-stuctural termination
let rec project #i fs =
  if Seq.length fs = 0
  then Seq.createEmpty
  else let fs, f = Content.split #(entry i) fs in
       maybe_snoc (project fs) (project_one f)


val project_snoc: #i:id -> s:seq (entry i) -> e:entry i -> Lemma
  (requires True)
  (ensures (project (snoc s e) = maybe_snoc (project s) (project_one e)))
  [SMTPat (project (snoc s e))]
let project_snoc #i s e =
  let hd, tl = Content.split (snoc s e) in
  cut (Seq.equal hd s)
*)



(* Several test functions to drive the Handshake manually until the big
 [writeOne] function is complete. *)

let test_send_alert (c: connection) (i: id) (ad: alertDescription) =
  match send c #i (Content.ct_alert i ad) with
  | Correct () ->
      closeConnection c; WriteError (Some ad) ""
  | Error (x,y) ->
      unrecoverable c y

let test_send (c:connection) (i:id) =
  let hs_response = Handshake.next_fragment c.hs in
  match hs_response with
  | Handshake.OutSome rg f ->
     send c #i (Content.CT_Handshake rg f)
  | _ -> failwith "ERROR"

let test_send_hs_fragment (c: connection) (i: id) (rg: frange i) (f: rbytes rg) =
  match send c #i (Content.CT_Handshake rg f) with
  | Correct ()   -> WriteAgain
  | Error (x,y) -> unrecoverable c y

let test_send_data (c: connection) (i: id) (rg: frange i) (f: rbytes rg) =
  match send c (Content.CT_Data rg f) with
  | Correct ()   -> Written (* Fairly, tell we're done, and we won't write more data *)
  | Error (x,y) -> unrecoverable c y




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

//Question: NS, BP, JL: What happens when (writeOne _ _ (Some appdata) returns WriteAgain and then is called again (writeOne _ _ None)?
//            How do we conclude that after these two calls all the appData was written?
// CF: this is guarantees only when returning Written.
val writeOne: c:connection -> i:id -> appdata: option (rg:frange i & DataStream.fragment i rg) -> ST ioresult_w
  (requires (fun h ->
    send_requires c i h
    /\ (let st = sel h c.state in
       let j = iT c.hs Writer h in
       j >= 0 ==> st=AD)))
  (ensures (fun h0 r h1 -> True))
(*     let st = sel h0 c.state in *)
(*     let es = sel h0 c.hs.log in *)
(*     let j = iT c.hs Writer h0  in *)
(*     st_inv c h0 /\ *)
(*     st_inv c h1 /\ *)
(*     j == iT c.hs Writer h1 /\ //16-05-16 used to be =; see other instance above *)
(*     (if j < 0 then i == noId /\ h0 = h1 else *)
(*        let e = Seq.index es j in *)
(*        i == hsId e.h /\ ( *)
(*        let wr:writer i = writer_epoch e in *)
(*        modifies (Set.singleton (C.region c)) h0 h1 *)
(* )))) *)

(* the rest of the spec below still uses the old state machine
    // TODO: conditionally prove that i == epoch_id (epoch_w_h c h), at least when appdata is set.
    // TODO: account for (the TLS view of) the encryptor log
    ( (r = WriteAgain /\
       sel h1 c.writing <> Closed /\
       (let o = epoch_w_h c h1 in
       i == epoch_id o /\
       is_Some o)
      )
    \/ (r = WriteAgainClosing /\ // after calling closable
       is_Closing (sel h1 c.writing)
///\      (let o = epoch_w_h c h1 in
//       i == epoch_id o /\
//       is_Some o)
      )
    \/ (r = Written /\
       is_Some appdata /\
       sel h1 c.writing = Open /\
       ( let o = epoch_w_h c h1 in
         i == epoch_id o /\
         is_Some o /\
         ( let wr: writer (epoch_id o) = epoch_wo o in
//           HyperHeap.modifies (Set.singleton (region wr)) h0 h1 /\
//           Heap.modifies (!{ as_ref (log wr), as_ref (seqn wr)}) (Map.sel h0 (region wr)) (Map.sel h1 (region wr)) /\
           sel h1 (seqn wr) = sel h0 (seqn wr) + 1 /\
           (Seq.length (sel h0 (log wr)) < Seq.length (sel h1 (log wr))) /\
           ( let e : entry i = Seq.index (sel h1 (log wr)) (Seq.length (sel h0 (log wr))) in
             sel h1 (log wr) = snoc (sel h0 (log wr)) e /\
             fragment_entry e = appfragment i appdata
           /\ project (sel h1 (log wr)) = snoc (project (sel h0 (log wr))) (datafragment i appdata)
))
       ))
    \/ (r = WriteDone /\ is_None appdata) // /\ h0 = h1)
    \/ (r = WriteHSComplete /\ sel h1 c.reading = Open   /\ sel h1 c.writing = Open)
    \/ (r = SentClose                                   /\ sel h1 c.writing = Closed)
    \/ (is_WriteError r) // /\ sel h1 c.reading = Closed /\ sel h1 c.writing = Closed)
  )
*)

// outcomes?
// | WriteAgain -> sent any higher-priority fragment, same index, same app-level log (except warning)
// | Written    -> sent application fragment (when is_Some appdata)
// | WriteDone  -> sent nothing              (when appdata = None)
// | WriteError None      _ -> closed the connection on unrecoverable error (same log, unclear app-level signal)
// | WriteError (Some ad) _ -> closed the connection (log extended with fatal alert)
// | WriteAgainClosing      -> will attempt to send an alert before closing
// | SentClose              -> similar
// | WriteAgainFinishing    -> incremented the writer epoch.

(* old implementation, with old state machine:
let writeOne c i appdata =
  let writing = !c.writing in
  recall (c_log c);  //NS: Should not be necessary; it's part of hs_inv now
  recall (C.reading c); // needed to get stability for i across ST calls
  let o = epoch_wo c in
  ( match o with
    | None -> ()
    | Some(Epoch h _ w) ->
      recall (log w); recall (seqn w));
      let h0 = ST.get() in
      let alert_response = Alert.next_fragment c.alert in
      let h1 = ST.get() in
      frame_unrelated c h0 h1;
      match alert_response with // alerts have highest priority
      | Some AD_close_notify ->
          ( match writing  with
            | Init | Open ->
            (* Not Closing: this is a graceful closure, should not happen in case of fatal alerts *)
            (* We're sending a close_notify alert. Send it, then only close our sending side.
               If we already received the other close notify, then reading is already closed,
               otherwise we wait to read it, then close. But do not close here. *)
              ( match send c #i (Content.ct_alert i AD_close_notify) with
                | Correct()   ->
		  let h2 = ST.get () in
		  c.writing := Closed;
		  frame_unrelated c h2 (ST.get());
		  SentClose //FIXME
                | Error (x,y) -> unrecoverable c y)
            | _ -> unrecoverable c (perror __SOURCE_FILE__ __LINE__ "Sending alert message in wrong state"))
      | Some ad ->
          ( match writing with
            | Init | Open | Closing _ ->
              (* We're sending a fatal alert. Send it, then close both sending and receiving sides *)
              ( match send c #i (Content.ct_alert i ad) with
                | Correct() ->
                    let reason = match writing with | Closing(_,reason) -> reason | _ -> "" in
                    closeConnection c;
                    WriteError (Some ad) reason
                | Error (x,y) -> unrecoverable c y )
            | _ -> unrecoverable c (perror __SOURCE_FILE__ __LINE__ "Sending alert message in wrong state"))
      | None ->
          ( let hs_response = Handshake.next_fragment c.hs in
            let h2 = ST.get() in
            match hs_response with // next we check if there are outgoing Handshake messages
            | Handshake.OutCCS -> (* send a (complete) CCS fragment *)
                frame_admit c h1 h2; //NS: not an instance of frame_internal, since it may change the epochs log if the result is OutCCS
                ( match writing with
(*
                  | Init | Open ->
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
                frame_internal c h1 h2;
                ( match writing with
                  | Init | Finishing | Open ->
                      ( match send c #i (Content.CT_Handshake rg f) with
                        | Correct()   -> WriteAgain
                        | Error (x,y) -> unrecoverable c y)
                  | _ -> closable c (perror __SOURCE_FILE__ __LINE__ "Sending handshake messages in wrong state"))
*)

#set-options "--initial_fuel 0 --initial_ifuel 1 --max_fuel 0 --max_ifuel 1"

let send_requires' (c:connection) (i:id) (h:HH.t) = 
    let st = sel h c.state in
    let es = sel h c.hs.log in
    let j = iT c.hs Writer h in
    (* j < Seq.length es /\ *)
    st_inv c h /\
    st <> Close /\
    st <> Half Reader   /\
    (j < 0 ==> i = noId) /\
    (j >= 0 ==> (
       let e = Seq.index es j in
       let wr = writer_epoch e in
       Map.contains h (StAE.region wr) /\ //NS: Needed to add this explicitly here. TODO: Soon, we will get this by just requiring mc_inv h, which includes this property
       Map.contains h (StAE.log_region wr)))(*  /\ //NS: Needed to add this explicitly here. TODO: Soon, we will get this by just requiring mc_inv h, which includes this property *)
       (* i = hsId e.h))(\*  /\ *\) *)
       (* (\* incrementable (writer_epoch e) h)) *\) *)

let writeOne c i appdata =
  let h0 = ST.get() in
  let st = !c.state in
  assert (send_requires c i h0);
  // alerts have highest priority; we send only close_notify and fatal alerts
  let alert_response = Alert.next_fragment c.alert in
  let h1 = ST.get() in

  frame_iT c.hs Writer h0 h1 (Set.singleton (Alert.region c.alert));
  (* assume false; // TODO can't get the precondition of send below.  *)
  (match alert_response with
  | Some ad -> 
    begin match ad with 
      | AD_close_notify -> // graceful closure
        (match send c #i (Content.ct_alert i AD_close_notify) with
	 | Correct()   ->
          let h2 = ST.get () in
          c.state := (if st = Half Writer then Close else Half Reader);
          SentClose
         | Error (x,y) -> unrecoverable c y )
     | _ ->
      (match send c #i (Content.ct_alert i ad) with
      | Correct() ->
          // let reason = match writing with | Closing(_,reason) -> reason | _ -> "" in
          closeConnection c;
          WriteError (Some ad) ""
      | Error (x,y) -> unrecoverable c y)
    end
    
  | _ ->  // next we check if there is outgoing Handshake traffic
        let hs_response = Handshake.next_fragment c.hs in
        let h2 = ST.get() in
        (match hs_response with
        | Handshake.OutCCS -> (
            // we know j has just been incremented.
            // we send the CCS fragment on the prior epoch
            frame_admit c h1 h2; //NS: not an instance of frame_internal, since it may change the epochs log if the result is OutCCS
	    admit();
            match send c #i (Content.CT_CCS #i (abyte 1z)) with
            | Correct _ ->
                c.state := BC; // use renego/key-update states instead? anyway AD writing is temporarily forbidden.
                //Alert.reset_outgoing c.alert;
                frame_admit c h0 (ST.get());
                WriteAgainFinishing
            | Error (x,y) -> unrecoverable c y)

            //$ | _ -> closable c (perror __SOURCE_FILE__ __LINE__ "Sending CCS in wrong state"))

        | Handshake.OutSome rg f -> (
            // we send some handshake fragment
	    (* assert (iT c.hs Writer h1 == iT c.hs Writer h2); *)
	    frame_admit c h1 h2;
	    (* admit(); *)
            match send c #i (Content.CT_Handshake rg f) with
            | Correct()   -> WriteAgain
            | Error (x,y) -> unrecoverable c y)

            //$ | _ -> closable c (perror __SOURCE_FILE__ __LINE__ "Sending handshake messages in wrong state"))
(*
        | Handshake.OutFinished rg last_fragment -> (* check we are finishing & send last fragment *)
                frame_internal c h1 h2;
                ( match writing with
                  | Finishing ->
                      ( match send c #i (Content.CT_Handshake rg last_fragment) with
                        | Correct()   ->
			  let h3 = ST.get () in
			  c.writing := Finished;
			  frame_unrelated c h3 (ST.get());
			  WriteAgain (* TODO 15-09-11 recheck, was WriteFinished *)
                                     (* also move to the Finished state *)
                        | Error (x,y) -> unrecoverable c y)
                  | _ -> closable c (perror __SOURCE_FILE__ __LINE__ "Sending handshake message in wrong state"))
*)
        | Handshake.OutComplete rg f -> (
            // we send the final handshake fragment and open AD
            frame_admit c h1 h2; //NS: may change the epochs log if the result is OutComplete
            match st with
            | BC -> ( match send c #i (Content.CT_Handshake rg f) with
                     | Correct() -> moveToOpenState c; WriteHSComplete
                            // removed sanity check: reader and writer indexes should be the same
                            //if !C_reading c) epochSI id.id_in = epochSI id.id_out then
                            //else unrecoverable c (perror __SOURCE_FILE__ __LINE__ "Invalid connection state")
                     | Error (x,y) -> unrecoverable c y)
            | _ -> closable c (perror __SOURCE_FILE__ __LINE__ "Sending handshake message in wrong state"))

        | Handshake.OutIdle -> 
        // finally attempt to send some application data
          frame_admit c h1 h2; 
          begin match st, appdata with
          | AD, Some (|rg,f|) ->
               ( match send c (Content.CT_Data rg f) with
                 | Correct()   -> Written (* Fairly, tell we're done, and we won't write more data *)
                 | Error (x,y) -> unrecoverable c y)
          | _ -> WriteDone // We are finishing a handshake. Tell we're done; the next read will complete it.
	  end 
       
       | _ -> unexpected "NYI"))



val writeAllClosing: c:connection -> i:id -> ST ioresult_w
  (requires (fun h ->
    let st = sel h c.state in
    let es = sel h c.hs.log in
    let j = iT c.hs Writer h in
    j < Seq.length es /\
    st_inv c h /\
    st <> Close /\
    st <> Half Reader /\
    (j < 0 ==> i == noId) /\
    (j >= 0 ==> (
      let e = Seq.index es j in
      st = AD /\
      i = hsId e.h /\
      incrementable (writer_epoch e) h))))
  (ensures (fun h0 r h1 ->
    st_inv c h1 /\  modifies (Set.singleton (C.region c)) h0 h1 /\
    (is_WriteError r \/ is_SentClose r)
  ))
let rec writeAllClosing c i =
    if no_seqn_overflow c then
    match assume false; writeOne c i None  //16-05-16 can't prove it, although same PRE syntactically?
    with
    | WriteAgain          -> writeAllClosing c i
    | WriteError x y      -> WriteError x y
    | SentClose           -> SentClose
    | _                   -> unexpected "[writeAllClosing] writeOne returned wrong result"
    else                    unexpected "[writeAllClosing] seqn overflow"

// in TLS 1.2 we send the Finished messages immediately after CCS
// in TLS 1.3 we send e.g. ServerHello in plaintext then encrypted HS


val writeAllFinishing: c:connection -> i:id -> ST ioresult_w
  (requires (fun h ->
    st_inv c h /\
    sel h c.state <> Close /\
    sel h c.state <> Half Reader //16-05-16  TBC
  ))
  (ensures (fun h0 r h1 ->
    st_inv c h1 /\ modifies (Set.singleton c.region) h0 h1 /\
    (is_WriteError r \/ is_SentClose r \/ is_Written r)
  ))

let rec writeAllFinishing c i =
    if no_seqn_overflow c then
    match assume false; writeOne c i None with
    // we disable writing temporarily
    | WriteAgain          -> writeAllFinishing c i
//   | WriteDone           -> MustRead

    // all other cases disable writing permanently
    | WriteAgainClosing   -> assume false; writeAllClosing c i
    | WriteError x y      -> WriteError x y
    | SentClose           -> SentClose // why would we do that?

//  | MustRead            // excluded since responded only here
//  | Written             // excluded since we are not sending AD
//  | WriteAgainFinishing // excluded by the handshake logic (not easily proved)
    | WriteHSComplete     // excluded since we need an incoming CCS (not easily proved)
                          -> unexpected "[writeAllFinishing] writeOne returned wrong result"
    else                    unexpected "[writeAllFinishing] seqn overflow"



// called both by read (with no appData) and write (with some appData fragment)
// returns to read  { WriteError, SentClose, WriteDone, WriteHSComplete }
// returns to write { WriteError, Written }
// (TODO: write returns { WriteHSComplete, MustRead } in renegotiation)
val writeAllTop: c:connection -> i:id -> appdata: option (rg:frange i & DataStream.fragment i rg) -> ST ioresult_w
  (requires (fun h ->
    st_inv c h //16-05-16  TBC
(*
    (let o = epoch_w_h c h in
     let st = sel h c.state in
      st <> Close  /\
      (is_Some appdata ==> st = AD) /\
      i == epoch_id o /\
      (is_Some o ==> is_seqn (sel h (seqn (writer_epoch (Some.v o))) + 1)))
*)      
      ))
  (ensures (fun h0 r h1 ->
    st_inv c h1 /\ modifies (Set.singleton c.region) h0 h1
  ))
let rec writeAllTop c i appdata =
    if no_seqn_overflow c then
    (assume false; // TODO
    match writeOne c i appdata with
//TODO | WriteAgain          -> writeAllTop c i appdata
    | WriteAgainClosing   -> writeAllClosing c (admit(); i) // TODO, using updated epoch_id (epoch_w c)
    | WriteAgainFinishing -> // next writer epoch!
                            writeAllFinishing c (admit(); i) // TODO, using updated epoch_id (epoch_w c)
    | WriteError x y      -> WriteError x y
    | SentClose           -> SentClose
    | WriteDone           -> WriteDone
//  | MustRead            -> MustRead
    | Written             -> Written
    | _                   -> unexpected "[writeAllTop] writeOne returned wrong result")
    else                    unexpected "[writeAllTop] seqn overflow"

//Question: NS, BP, JL: Is it possible for write to return WriteAgain or a partially written data?
// no: we always write the whole fragment or we get a fatal error.


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

let write c i rg data = writeAllTop c i (Some (| rg, data |))

let full_shutdown c =
    Alert.send c.alert AD_close_notify

let half_shutdown c =
    Alert.send c.alert AD_close_notify;
    writeAllClosing c


(*** incoming (with implicit writing) ***)

// By default, all i:id are reader identifiers, i.e. peerId (hsId (reader_epoch.h)
// Tricky for noId?       

// FIXME: Put the following definitions close to range and delta, and use them

type query = Cert.chain
type msg_i (i:id) = (range * DataStream.delta i)

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


type ioresult_i (i:id) =
    | Read of DataStream.delta i
        // this delta has been added to the input stream; we may have read
        // - an application-data fragment or a warning (leaving the connection live)
        // - a closure or a fatal alert (tearing down the connection)
        // If the alert is a warning, the connection remains live.
        // If the alert is final, the connection has been closed by our peer;
        // the application may reuse the underlying TCP stream
        // only after normal closure (a = AD_close_notify)

    | ReadError: o:option alertDescription -> txt:string -> ioresult_i i
        // We encountered an error while reading, so the connection dies.
        // we return the fatal alert we may have sent, if any,
        // or None in case of an internal error.
        // The connection is gone; its state is undefined.

    | CertQuery: query -> bool -> ioresult_i i
        // We received the peer certificates for the next epoch, to be authorized before proceeding.
        // the bool is what the Windows certificate store said about this certificate.
    | CompletedFirst
        // Handshake is completed, and we have already sent our finished message,
        // so only the incoming epoch changes
    | CompletedSecond
        // Handshake is completed, and we have already sent our finished message,
        // so only the incoming epoch changes

    // internal states only
    | ReadAgain
    | ReadAgainFinishing

//  | ReadFinished
//  | DontWrite
//      // Nothing read yet, but we can't write anymore.



let live_i e r = // is the connection still live?
  match r with
  | Read d        -> not(DataStream.final e d)
  | ReadError _ _ -> false
  | _             -> true

// let's specify reading d off the input DataStream (incrementing the reader pos)

val sel_reader: h:HyperHeap.t -> connection -> Tot (option (| i:id & StAE.reader i |)) // self-specified
let sel_reader h c =
  let es = sel h (c_log c) in
  let j = iT c.hs Reader h in
  (if j < 0 then None else 
  let e = Seq.index es j in 
  let i = peerId (hsId e.h) in
  assume(is_stream_ae i);
  Some (| i, reader_epoch e|))
  
  // todo: add other cases depending on dispatch state

type delta h c = 
  (match sel_reader h c with 
  | Some (| i , _ |) -> DataStream.delta i
  | None             -> DataStream.delta noId)

(*
val append_r: h0:HH.t -> HH.t -> c:connection -> d: delta h0 c -> Type0
let append_r h0 h1 c d =
  match sel_reader h0 c with  // we statically know those are unchanged
  | Some (| i, r |) -> 
    let pos0 = StAE.seqnT r h0  in
    let pos1 = StAE.seqnT r h1  in
    pos1 = pos0 + 1  /\
    (if authId i then 
    let log0 = StAE.fragments r h0 in 
    let log1 = StAE.fragments r h1 in 
    (log1 = log0 /\
    Seq.index log1 pos0 = d ))
  | None -> True
*)

// frequent error handler
let alertFlush c i x y: ioresult_i i =
  abortWithAlert c x y;
  let written = writeAllClosing c i in
  match written with
  | SentClose      -> Read DataStream.Close // do we need this case?
  | WriteError x y -> ReadError x y

val readFragment: c:connection -> i:id -> ST (result (Content.fragment i))
  (requires (fun h0 ->
    let es = epochsT c h0 in 
    let j = iT c.hs Reader h0 in 
    st_inv c h0 /\
    (if j < 0 then i == noId else 
      let e = Seq.index es j in
      i = peerId (hsId e.h) /\
      incrementable (reader_epoch e) h0)))
  (ensures (fun h0 r h1 -> 
    let es = epochsT c h0 in 
    let j = iT c.hs Reader h0 in 
    st_inv c h0 /\
    st_inv c h1 /\
    j == iT c.hs Reader h1 /\
    (if j < 0 then i == noId /\ h0 == h1 else 
      let e = Seq.index es j in
      i = peerId (hsId e.h) /\
      (let rd: reader i = reader_epoch e in 
      modifies (Set.singleton (region rd)) h0 h1 /\
      (match r with 
      | Error e -> True // don't know what seqnT is, don't care.
      | Correct f -> 
          seqnT rd h1 = seqnT rd h0 + 1 /\
          (authId i ==>
            (let frs = StAE.fragments #i rd h0 in
            let n = seqnT rd h0 in 
            n < Seq.length frs /\
            f == Seq.index frs n) 
  ))))))

let readFragment c i = 
  assume false; // 16-05-19 can't prove POST.
  match Record.read c.tcp i.pv with 
  | Correct(ct,pv,payload) -> 
     begin
       // either payload is a plaintext protocol fragment, or we decrypt
       let j = Handshake.i c.hs Reader in 
       if j = 0 then 
         let rg = Range.point (length payload) in 
         Correct(Content.mk_fragment i ct rg payload)
       else
         let es = !c.hs.log in 
         let e = Seq.index es j in 
         match StAE.decrypt (reader_epoch e) payload with 
         | Some f -> Correct f
         | None   -> Error(AD_internal_error,"") //16-05-19 ADJUST! 
     end
  | Error e       -> Error e


// We receive, decrypt, verify a record (ct,f); what to do with it?
// i is the presumed reader, threaded from the application.

private val readOne: c:connection -> i:id -> St (ioresult_i i) 
//  (ensures ioresult is not CompletedFirst | CompletedSecond | DontWrite)

let readOne c i =
  assume false; //16-05-19 
  match readFragment c i with 
  | Error (x,y) ->  alertFlush c i x y
  | Correct(Content.CT_Alert rg f) -> 
      begin 
        match Alert.recv_fragment c.alert rg f with
        | Error (x,y)   -> alertFlush c i x y
        | Correct AD_close_notify ->          // an outgoing close_notify has already been buffered, if necessary
              if !c.state = Half Reader
              then c.state := Close
              else c.state := Half Writer; // we close the reading side
              Read DataStream.Close
        | Correct alert ->
              if isFatal alert then closeConnection c; // else we carry on; the user will know what to do
              Read (DataStream.Alert alert)
      end
      // recheck we tolerate alerts in all states; used to be just Init|Open, otherwise:
      // alertFlush c AD_unexpected_message (perror __SOURCE_FILE__ __LINE__ "Message type received in wrong state")

  | Correct (Content.CT_Handshake rg f) -> 
      begin
        match Handshake.recv_fragment c.hs rg f with
        | Handshake.InError (x,y) -> alertFlush c i x y
        | Handshake.InAck         -> ReadAgain
        | Handshake.InQuery q a   -> CertQuery q a
      //| Handshake.InFinished    -> ReadAgain // should we care? probably before e.g. accepting falseStart traffic
        | Handshake.InComplete    ->
          ( match !c.state with
            | BC -> // TODO: additional sanity check: in and out epochs should be the same
                   // if epoch_r c = epoch_w c then 
                   (c.state := AD; CompletedFirst)
                   // else (closeConnection c; ReadError None "Invalid connection state")
                   )
      // recheck correctness for all states; used to be just Init|Finishing|Open
      end
  | Correct(Content.CT_CCS _) ->
      begin
        match Handshake.recv_ccs c.hs with
        | InError (x,y)        -> alertFlush c i x y
        | InAck                -> // We know statically that Handshake and Application data buffers are empty.
                                 ReadAgainFinishing
      end
  | Correct(Content.CT_Data rg d) ->
      begin
        match !c.state with
        | AD | Half Reader        -> let d : DataStream.fragment i fragment_range = d in Read #i (DataStream.Data d)
        | _                       -> alertFlush c i AD_unexpected_message "Application Data received in wrong state"
      end


(*** VERIFIES UP TO HERE (WITH GAPS) ***)


  (* JP: the definitions below were in the .fst but didn't match what was in the
   .fsti -- the definitions above are from the .fsti, and the (commented-out)
   definitions below are from the .fst.  *)

val readAllFinishing: connection -> i:id -> St(ioresult_i i) 
let rec readAllFinishing c i = 
    assume false; //16-05-19 
    let outcome = readOne c i in 
    match outcome with
    | ReadAgain      -> readAllFinishing c i
    | CompletedFirst -> CompletedFirst #i
    | Read (DataStream.Alert ad) ->
       begin
         if isFatal ad
         then outcome  (* silently dropping the error? recheck *)
         else ReadError None (perror __SOURCE_FILE__ __LINE__ "Trying to close an epoch after CCS has been sent, but before new epoch opened.")
       end
    | ReadError _ _  -> unexpected "[readAllFinishing] should not return ReadError"
    | Read DataStream.Close ->
        (* This is the dual of the case above: we received the CCS, which implicitly closed the receiving epoch,
           and the new epoch is not open yet, so we can neither receive authenticated data, nor close this epoch.  *)
         ReadError None (perror __SOURCE_FILE__ __LINE__ "Trying to close an epoch after CCS has been sent, but before new epoch opened.")
(* 16-05-19 ?
    | ReadFinished   ->
        begin
          let i = epoch_id (epoch_w c) in
          let written = writeAllTop c i None in
          match written with
          | WriteHSComplete
          | WriteError _ _ -> outcome (* hiding the error? double-check *)
          | SentClose      -> unexpected "[readAllFinishing] There should be no way of sending a closure alert after we validated the peer Finished message"
          | _              -> unexpected "[readAllFinishing] writeAllTop should never return such write outcome"
        end 
*)        
//    | ReadAgainFinishing | Read _  | CertQuery _ -> unexpected "[readAllFinishing] readOne returned wrong result"

//    | WriteOutcome(SentFatal(x,y)) -> WriteOutcome(SentFatal(x,y))
//    | WriteOutcome(WError(x))      -> WriteOutcome(WError(x))
        (* This and the following two corner cases are underspecified in RFC 5246, and we handle them by tearing down the connection.
           These are inconsistent states of the protocol that should be explicitly forbidden by the RFC.
           In this case, sending our CCS already implicitly closed the previous sending epoch, and the new epoch is not open
           yet, so there's nothing to close. *)



// scheduling: we always write up before reading.
// those writes are never AppData; they may be for other/changing epochs
val read: connection -> i:id -> St (ioresult_i i)
let rec read c i =
    assume false;//16-05-19 
    let wi = currentId c Writer in
    match writeAllTop c wi None with
    | SentClose       -> Read DataStream.Close // TODO: add support for Half Reader?
    | WriteError x y  -> ReadError x y         // TODO: review error result is unambiguous
//  | WriteFinished   -> DontWrite
    | WriteHSComplete -> CompletedFirst        // return at once, so that the app can authorize
    | WriteDone       ->                       // nothing happened; now we can read

    // TODO: deal with updates of i
    let res = readOne c i in (
    match res with
    // TODO: specify which results imply that c.state & epochs are unchanged
    | ReadAgain             -> read c i
    | ReadAgainFinishing    -> read c i //was: readAllFinishing c
    | ReadError x y         -> ReadError x y
    | CertQuery q adv       -> CertQuery q adv
    | Read delta            -> Read delta
    )


(* readOne already updated the state, so no special case for Read DataStream.Close
    | Read DataStream.Close ->
            let st = !c.state in
            match st with
            | Half Reader  ->

            | Closed -> Read DataStream.Close // we already sent a close_notify, tell the user it's over
            | _ ->
                let written = writeAllClosing c (rd_i c) (*FIXME*) in
                match written with
                | SentClose      -> Read DataStream.Close // clean shutdown
                | WriteError x y -> ReadError x y
                | _              -> ReadError None (perror __SOURCE_FILE__ __LINE__ "") // internal error
                )
*)

// -----------------------------------------------------------------------------

(* =================///////////////////================

//* we used to specify the resulting connection in ioresult_i,
//* now we do that in the read postcondition

// responding to a certificate-validation query,
// so that we have an explicit user decision to blame,
// but in fact a follow-up read would do as well.
// to be adapted once we have a proper PKI model
//val authorize : c:Connection -> q:query -> ST ioresult_i
//  (requires (fun h0 -> True))
//  (ensures (fun h0 result h1))

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
*)

