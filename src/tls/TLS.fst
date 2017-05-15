module TLS

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
open FStar.Set

open Platform
open Platform.Bytes
open Platform.Error

open TLSError
open TLSConstants
open TLSInfo

open Range
//open Negotiation
open Epochs
//open Handshake
open Connection

module HH   = FStar.HyperHeap
module HST  = FStar.HyperStack
module MR   = FStar.Monotonic.RRef
module MS   = FStar.Monotonic.Seq
module DS   = DataStream
module SD   = StreamDeltas
module Conn = Connection
module EP   = Epochs

(* A flag for runtime debugging of TLS data. 
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false *)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("TLS| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if Flags.debug_TLS then print else (fun _ -> ())


unfold let op_Array_Access (#a:Type) (s:Seq.seq a) n = Seq.index s n // s.[n] 

// using also DataStream, Content, Record
#set-options "--initial_ifuel 0 --max_ifuel 0 --initial_fuel 0 --max_fuel 0"

// too convenient; use sparingly. Should move to a library
// JP: isn't failwith sufficient enough? CF: this one works in ST. 
val unexpected: #a:Type -> v:string -> ST a
  (requires (fun h -> True))
  (ensures (fun _ _ _ -> False ))
let rec unexpected #a s = unexpected s


(** misc ***)

// the (now fake) protocol version in the record header
let outerPV (c:connection) : ST protocolVersion
  (requires (Handshake.hs_inv c.hs))
  (ensures (fun h0 pv h1 -> h0 == h1)) =
  match Handshake.version_of c.hs with
  | TLS_1p3 -> TLS_1p0
  | pv      -> pv


(** control API ***)

// subsumes connect, resume, accept_connected, ...
val create: r0:c_rgn -> tcp:Transport.t -> r:role -> cfg:config -> resume: resumeInfo r -> ST connection
  (requires (fun h -> True))
  (ensures (fun h0 c h1 ->
    modifies Set.empty h0 h1 /\
    extends c.region r0 /\ 
    stronger_fresh_region c.region h0 h1 /\
    Map.contains (HST.HS?.h h1) c.region /\ //NS: may be removeable: we should get it from fresh_region
    st_inv c h1 /\
    c_role c = r /\
//17-04-08 commented out as their access is now stateful
//    c_cfg c == cfg /\
//    c_resume c = resume /\
    c.tcp == tcp  /\
    //17-04-07 went back to static refinements on resumeInfo r
    //(r = Server ==> resume = None) /\ //16-05-28 style: replacing a refinement under the option
    epochs c h1 == Seq.createEmpty /\ // we probably don't care---but we should say nothing written yet
    HST.sel h1 c.state = (Ctrl,Ctrl) ))

#set-options "--z3rlimit 50"
let create parent tcp role cfg resume =
    let m = new_region parent in
    let hs = Handshake.create m cfg role resume in
    let state = ralloc m (Ctrl,Ctrl) in
    assume (is_hs_rgn m);
    C #m hs tcp state


//TODO upgrade commented-out types imported from TLS.fsti
// type initial (role: role) (ns:Transport.t) (c:config) (resume: option sessionID) (cn:connection) (h: HyperHeap.t) =
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
//val connect: ns:Transport.t -> c:config -> resume: option sessionID -> ST connection
//  (requires (fun h0 -> True))
//  (ensures (fun h0 cn h1 ->
//    modifies Set.empty h0 h1 /\
//    initial Client ns c resume cn h1
//    //TODO: even if the server declines, we authenticate the client's intent to resume from this sid.
//  ))
let connect m0 tcp cfg        = create m0 tcp Client cfg (None,[])
let resume  m0 tcp cfg sid    = create m0 tcp Client cfg (Some sid,[])
//val accept_connected: ns:Transport.t -> c:config -> ST connection
//  (requires (fun h0 -> True))
//  (ensures (fun h0 cn h1 ->
//    modifies Set.empty h0 h1 /\
//    initial Server ns c None cn h1
//  ))
let accept_connected m0 tcp cfg = create m0 tcp Server cfg (None,[])

//* do we need accept and accept_connected?
//val accept: Tcp.tcpListener -> c:config -> ST connection
//  (requires (fun h0 -> True))
//  (ensures (fun h0 cn h1 ->
//    modifies Set.empty h0 h1 /\
//    (exists ns. initial Server ns c None cn h1)
//  ))
let accept m0 listener cfg =
    let tcp = Transport.accept listener in
    accept_connected m0 tcp cfg

//val rehandshake: cn:connection { c_role cn = Client } -> c:config -> ST unit
//  (requires (fun h0 -> True))
//  (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 // no visible change in cn
//  ))
let rehandshake c ops = Handshake.rehandshake (C?.hs c) ops
// the client can ask for rekeying --- no immediate effect
//val rekey: cn:connection { c_role cn = Client } -> ST unit
//  (requires (fun h0 -> True))
//  (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 // no visible change in cn
//  ))
let rekey c ops       = Handshake.rekey       (C?.hs c) ops
//val request: cn:connection { c_role cn = Server } -> c:config -> ST unit
//  (requires (fun h0 -> True))
//  (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 // no visible change in cn
//  ))
let request c ops     = Handshake.request     (C?.hs c) ops


(** current epochs ***)

// the index of messages depends on the connection state,
// and may be different for reading and for writing.

#set-options "--initial_ifuel 0 --max_ifuel 1 --initial_fuel 0 --max_fuel 0"
//16-05-28 we need pattern matching! 

// to be replaced with check_incrementable (and pushed).
// dynamically checks for overflows
val no_seqn_overflow: c: connection -> rw:rw -> ST bool
  (requires (fun h -> st_inv c h))
  (ensures (fun h0 b h1 ->
    let es = epochs c h1 in
    let j = Handshake.iT c.hs rw h1 in
    j < Seq.length es /\
    h0 == h1 /\
    (b /\ j >= 0) ==> (
    let e = es.(j) in
    match rw with 
    | Reader -> StAE.incrementable (reader_epoch e) h0
    | Writer -> StAE.incrementable (writer_epoch e) h0
    )))

let no_seqn_overflow c rw =
  let es = MS.i_read (Handshake.es_of c.hs) in //MR.m_read c.hs.log in
  let j = Handshake.i c.hs rw in // -1 <= j < length es
  if j < 0 then //16-05-28 style: ghost constraint prevents using j < 0 || ... 
    true
  else ( //indexable es j
    let e = es.(j) in 
    let h = ST.get() in 
    let _ = match rw with 
    | Reader -> assume(StAE.incrementable (reader_epoch e) h)
    | Writer -> assume(StAE.incrementable (writer_epoch e) h) in
    true  )
// JP: placeholder while I fix the int64 problem
    (* 
    let n = !(seqn w) + 1 in
    if n >= 72057594037927936 && n < 18446744073709551616
    then (lemma_repr_bytes_values n; true)
    else false *)
    
#set-options "--initial_ifuel 0 --max_ifuel 0 --initial_fuel 0 --max_fuel 0"


(** outgoing ***)

type ioresult_w =
    // public results returned by TLS.send
    | Written             // the application data was written; the connection remains writable
    | WriteClose          // a final closeNotify was written; the connection is either closed or read-only
    | WriteError: o:option alertDescription -> txt: string -> ioresult_w 
                          // The connection is gone, possibly after sending a fata alert 
//  | WritePartial of unsent_data // worth restoring?

    // transient internal results returned by auxiliary send functions
    | WrittenHS: newWriter:option bool -> complete:bool -> ioresult_w // the handshake progressed
(*
//  | MustRead            // Nothing written, and the connection is busy completing a handshake
    | WriteDone           // No more data to send in the current state
    | WriteHSComplete     // The handshake is complete [while reading]
    | WriteClose           // a closeNotify was finally written.
    | WriteAgain          // sent something; there may be more to send (loop)
    | WriteAgainFinishing // outgoing epoch changed; there may be more to send to finish the handshake (loop)
    | WriteAgainClosing   // we are tearing down the connection & must still send an alert
*)

type ioresult_o = r:ioresult_w { Written? r \/ WriteError? r }


// error-handling

// the connection fails now, and should not be resumed.
val disconnect: c: connection -> ST unit
  (requires (fun h0 -> st_inv c h0 /\ h0 `HST.contains` c.state))
  (ensures (fun h0 _ h1 -> st_inv c h1 /\ modifies (Set.singleton (C?.region c)) h0 h1))

let disconnect c =
    Handshake.invalidateSession c.hs; //changes (HS?.region c.hs)
    c.state := (Closed,Closed);
    let h = ST.get () in
    assume (st_inv c h)

// on some errors, we locally give up the connection
val unrecoverable: c: connection -> r:string -> ST ioresult_w
  (requires (fun h0 -> st_inv c h0 /\ h0 `HST.contains` c.state))
  (ensures (fun h0 i h1 -> st_inv c h1 /\ 
		        modifies (Set.singleton (C?.region c)) h0 h1 /\
			i = WriteError None r))
let unrecoverable c reason =
  disconnect c;
  WriteError None reason

let currentId_T (c:connection) (rw:rw) (h:HST.mem) : GTot id =  
  let j = Handshake.iT c.hs rw h in 
  if j < 0 
  then PlaintextID (c_nonce c)
  else epoch_id (Handshake.eT c.hs rw h)
  
let currentId (c:connection) (rw:rw) 
  : ST id 
      (requires (fun h -> True)) 
      (ensures (fun h0 r h1 -> h0==h1 /\ r=currentId_T c rw h1))
= 
  let j = Handshake.i c.hs rw in 
  if j<0 then PlaintextID (c_nonce c)
  else let e = Epochs.get_current_epoch (Handshake.epochs_of c.hs) rw in epoch_id e

let maybe_indexable (es:seq 'a) (i:int) = i=(-1) \/ indexable es i


(* 
assume val admit_st_inv: c: connection -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 = h1 /\ st_inv h1 c))
*)


// auxiliary functions for projections; floating.
let appfragment (i:id{~ (PlaintextID? i)}) (o: option (rg:frange i & DataStream.fragment i rg) { Some? o }) : Content.fragment i =
  match o with
  | Some (| rg, f |) -> Content.CT_Data rg f

let datafragment (i:id{~ (PlaintextID? i)}) (o: option (rg:frange i & DataStream.fragment i rg) { Some? o }) : DataStream.delta i =
  match o with
  | Some (| rg, f |) -> let f: DataStream.pre_fragment i = f in //16-05-16 unclear why we now need this step
                       DataStream.Data f

(* which fragment should we send next? *)
(* we must send this fragment before restoring the connection invariant *)

//* pick & send one pending message from any protocol state, in two modes:
//* when writing for the application code, we may send Some? ghost.
//* when writing while reading, None? ghost.
//* the result ranges over...
//* | WriteDone         when None? ghost, notifying there is nothing left to send
//* | Written when Some? ghost, notifying the appdata fragment was sent
//* | WriteError (unrecoverable \/ after sending alert)
//* | WriteClose
//* | WriteAgain | WriteAgainFinishing | WriteAgainClosing
//* | WriteHSComplete
//* the state changes accordingly.

////////////////////////////////////////////////////////////////////////////////
// Current writers
////////////////////////////////////////////////////////////////////////////////
let trigger_peer (#a:Type) (x:a) = True

let cwriter (i:id) (c:connection) = 
  w:StAE.writer i{exists (r:StAE.reader (peerId i)).{:pattern (trigger_peer r)}
		    epoch_region_inv' (Handshake.region_of c.hs) r w}

let current_writer_pre (c:connection) (i:id) (h:HST.mem) : GTot bool = 
  let hs = c.hs in 
  let ix = Handshake.iT hs Writer h in
  if ix < 0
  then PlaintextID? i
  else 
    let epoch_i = Handshake.eT hs Writer h in 
    i = epoch_id epoch_i

let current_writer_T (c:connection) (i:id) (h:HST.mem{current_writer_pre c i h})
  : GTot (option (cwriter i c))
= 
  let i = Handshake.iT c.hs Writer h in
  if 0 <= i
  then 
    let e = Handshake.eT c.hs Writer h in
    let _ = cut (trigger_peer (Epoch?.r e)) in
    Some (Epoch?.w e)
  else None

val current_writer : c:connection -> i:id -> ST (option (cwriter i c))
       (requires (fun h -> current_writer_pre c i h))
       (ensures (fun h0 wo h1 -> 
	       current_writer_pre c i h1
	       /\ h0==h1
	       /\ wo==current_writer_T c i h1
	       /\ (None? wo <==> PlaintextID? i)))
let current_writer c i = 
  let ix = Handshake.i c.hs Writer in 
  if ix < 0
  then None
  else 
    let epochs = MS.i_read (Handshake.es_of c.hs) in
    let e = epochs.(ix) in
    let _ = cut (trigger_peer (Epoch?.r e)) in
    Some (Epoch?.w e)

let recall_current_writer (c:connection) 
  : ST unit (fun h -> True) (fun h0 _ h1 -> 
    let i = currentId_T c Writer h0 in
    let wopt = current_writer_T c i h0 in
    h0 == h1 
    /\ (match wopt with
       | None -> True
       | Some wr -> Map.contains (HST.HS?.h h0) (StAE.region wr)
	         /\ Map.contains (HST.HS?.h h0) (StAE.log_region wr)))
  = let i = currentId c Writer in
    let wopt = current_writer c i in
    match wopt with
    | None -> ()
    | Some wr -> 
      recall_region (StAE.region wr);
      recall_region (StAE.log_region wr)

//16-05-29 duplicating no_seqn_overflow?
private let check_incrementable (#c:connection) (#i:id) (wopt:option (cwriter i c))
  : ST bool
    (requires (fun h -> True))
    (ensures (fun h0 b h1 -> 
	      h0 == h1 
	      /\ (b <==> (match wopt with 
		        | None -> True
			| Some w -> StAE.incrementable w h1))))
  = assume(False); true // admit()

////////////////////////////////////////////////////////////////////////////////
// Sending fragments on a given writer (not necessarily the current one)
////////////////////////////////////////////////////////////////////////////////
let opt_writer_regions (#i:id) (#c:connection) (wopt:option (cwriter i c)) : Tot (set HH.rid) = 
  match wopt with 
  | None -> Set.empty
  | Some wr -> Set.singleton (StAE.region wr)

let sendFragment_inv (#c:connection) (#i:id) (wo:option(cwriter i c)) h = 
     st_inv c h 
  /\ (match wo with 
     | None    -> PlaintextID? i
     | Some wr ->  Map.contains (HST.HS?.h h) (StAE.region wr)
	        /\ Map.contains (HST.HS?.h h) (StAE.log_region wr))

#set-options "--initial_fuel 0 --initial_ifuel 1 --max_fuel 0 --max_ifuel 1"  

//16-05-29 note that AD_record_overflow os for oversized incoming records, not seqn overflows! See slack.
// let ad_overflow : result unit = Error (AD_internal_error, "seqn overflow")
let ad_overflow : result unit = Error (AD_record_overflow, "seqn overflow")

let sendFragment_success (mods:set rid) (c:connection) (i:id) (wo:option (cwriter i c)) (f: Content.fragment i) (h0:HST.mem) (h1:HST.mem) =
      Some? wo ==> 
      (let wr = Some?.v wo in
       modifies_just (Set.union mods (Set.singleton (StAE.region wr))) (HST.HS?.h h0) (HST.HS?.h h1) 
     /\ StAE.seqnT wr h1 = StAE.seqnT wr h0 + 1 
     /\ (authId i ==>
	     //fragment was definitely snoc'd
	     StAE.fragments wr h1 == snoc (StAE.fragments wr h0) f 
     	     //delta was maybe snoc'd, if f is not a handshake fragment
	     /\ SD.stream_deltas wr h1 == Seq.append (SD.stream_deltas wr h0) (SD.project_one_frag f)
	     //and the deltas associated with wr will forever more contain deltas1 as a prefix
             /\ MR.witnessed (SD.deltas_prefix wr (SD.stream_deltas wr h1))))

val sendFragment: c:connection -> #i:id -> wo:option (cwriter i c) -> f: Content.fragment i -> ST (result unit)
  (requires (sendFragment_inv wo))
  (ensures (fun h0 r h1 -> 
    //we still have st_inv, etc.
    sendFragment_inv wo h1 
    //we didn't advance any epochs
    /\ (current_writer_pre c i h0 ==> current_writer_pre c i h1
				   /\ current_writer_T c i h0 == current_writer_T c i h1)
    /\ (currentId_T c Writer h1 = currentId_T c Writer h0)
    //behavior in the erroneous cases				   
    /\ (None? wo \/ r=ad_overflow ==> modifies Set.empty h0 h1)
    /\ (r=ad_overflow ==> Some? wo /\ not(StAE.incrementable (Some?.v wo) h1))
    //correct behavior, including projections suitable for both the handshake (fragments) and the application (deltas)
    /\ (r<>ad_overflow ==> sendFragment_success Set.empty c i wo f h0 h1)))

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let sendFragment c #i wo f =
  reveal_epoch_region_inv_all ();
  let ct, rg = Content.ct_rg i f in
  let idt = if ID12? i then "ID12" else if ID13? i then "ID13" else "PlaintextID" in
  trace ("send "^Content.ctToString ct^" fragment with index "^idt);
  if not (check_incrementable wo)
  then ad_overflow 
  else begin
       let payload: Content.encrypted f =
           match wo with
	   | None    -> 
	     assert (PlaintextID? i);
	     Content.repr i f
	   | Some wr -> 
	     SD.encrypt wr f 
       in
       let pv = Handshake.version_of c.hs in
       lemma_repr_bytes_values (length payload);
       assume (repr_bytes (length payload) <= 2); //NS: How are we supposed to prove this?
       let record = Record.makePacket ct (PlaintextID? i) pv payload in
       let r  = Transport.send c.tcp record in
       match r with
       | Error(x)  -> Error(AD_internal_error,x)
       | Correct _ -> Correct()
  end

////////////////////////////////////////////////////////////////////////////////
// Sending alerts: this always happens on the current writer
////////////////////////////////////////////////////////////////////////////////
//Cedric says on slack:
//  Functionally, you can only send alerts on the current epoch; so
//  indeed, it is not necessarily the index known at the TLS API level. We
//  have to reflect it in the postconditions of TLS read/write, but we
//  don't have to be fully precise: If we report an error, we can e.g. say
//  that an alert may have been sent on the current epoch.

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
private let sendAlert (c:connection) (ad:alertDescription) (reason:string)
  :  ST ioresult_w
	(requires (fun h -> 
	  let i = currentId_T c Writer h in 
	  current_writer_pre c i h
	  /\ sendFragment_inv (current_writer_T c i h) h))
	(ensures (fun h0 r h1 -> 
	    let i = currentId_T c Writer h1 in 
    	    current_writer_pre c i h1 /\
	    st_inv c h1 /\
	    (match r with 
	     | WriteError None _ ->
	       modifies (Set.singleton (C?.region c)) h0 h1
	       //the spec of disconnect is too weak to prove this now
               (* /\ sel h1 c.state = Close *)
	       (* /\ StAE.fragments wr h1 == snoc (StAE.fragments wr h0) f *)
	     | WriteError (Some _) _ ->
	       modifies (Set.singleton (C?.region c)) h0 h1
	       //the spec of disconnect is too weak to prove more than this now
	     | WriteClose -> 
	       let wopt = current_writer_T c i h1 in
	       let frag = Content.CT_Alert #i (point 2) ad in
	       let st = sel h0 c.state in
	       sendFragment_success (Set.singleton (C?.region c)) c i wopt frag h0 h1
	       /\ sel h1 c.state = (fst st, Closed)
	     | _ -> False)))
=
    trace ("sendAlert "^TLSError.string_of_error (ad,reason));
    reveal_epoch_region_inv_all ();
    let i = currentId c Writer in
    let wopt = current_writer c i in 
    let st = !c.state in
    let res = sendFragment c #i wopt (Content.CT_Alert #i (point 2) ad) in
    match res with 
    | Error xy -> unrecoverable c (snd xy) // or reason?
    | Correct _   ->
        if ad = AD_close_notify then
          begin // graceful closure
            c.state := (fst st, Closed);
            WriteClose
          end
        else
          begin
            disconnect c;
            WriteError (Some ad) reason
          end

////////////////////////////////////////////////////////////////////////////////
// Sending handshake messages on a given writer
////////////////////////////////////////////////////////////////////////////////
let sendHandshake_post (#c:connection) (#i:id) (wopt:option (cwriter i c)) 
		       (om:option (HandshakeLog.fragment i)) (send_ccs:bool) (h0:HST.mem) r (h1:HST.mem) = 
      modifies_just (opt_writer_regions wopt) (HST.HS?.h h0) (HST.HS?.h h1)    //didn't modify more than the writer's regions
      /\ (match wopt with
 	 | None -> True
	 | Some wr ->
	   StAE.seqnT wr h0 <= StAE.seqnT wr h1
	   /\ StAE.seqnT wr h1 <= StAE.seqnT wr h0 + 2  //sent at most 2 fragments
	   /\ (authId i ==> 
	      (let frags1 = StAE.fragments wr h1 in
 	       let frags0 = StAE.fragments wr h0 in
	       Seq.equal (SD.stream_deltas wr h1) (SD.stream_deltas wr h0) //all the fragments sent are internal to TLS
	       /\ (match r with 
		  | Error _ ->  
		    //either the handshake message failed or the ccs failed
		    //but we can't really distinguish those cases precisely
		    //Also, the post-condition of sendFragment in the error case is not yet very informative
		    True
		  | _ ->
		    r<>ad_overflow ==>  //if both sends succeeded
		    (match om with 
		     | None ->  //if no msg, then we sent at most the CCS
		       if send_ccs 
		       then frags1==snoc frags0 (Content.CT_CCS #i (point 1))
		       else frags1==frags0
		     | Some(| rg, f |) -> //we sent the message
		       let frags0' = snoc frags0 (Content.CT_Handshake rg f) in
		       if send_ccs //and the CCS, if requested
		       then frags1==snoc frags0' (Content.CT_CCS #i (point 1))
		       else frags1==frags0')))))

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
private let sendHandshake (#c:connection) (#i:id) (wopt:option (cwriter i c)) (om:option (HandshakeLog.fragment i)) (send_ccs:bool)
  : ST (result unit)
       (requires (sendFragment_inv wopt))
       (ensures (fun h0 r h1 -> 
		sendFragment_inv wopt h1
		/\ sendHandshake_post wopt om send_ccs h0 r h1))
  =  let h0 = ST.get() in
     trace "sendHandshake";
     let result0 = // first try to send handshake fragment, if any
         match om with
         | None             -> Correct()
         | Some (| rg, f |) -> sendFragment c wopt (Content.CT_Handshake rg f) in
     let h1 = ST.get() in
     // then try to send CCS fragment, if requested
     match result0 with
     | Error e -> Error e
     | _ ->
       if not send_ccs
       then result0
       else
         begin
	   // Don't pad
	   let frags = sendFragment c wopt (Content.CT_CCS #i (point 1)) in
	   let h2 = ST.get() in
	   begin
	     match wopt with
	     | Some wr -> 
	       begin
	       lemma_modifies_just_trans (HST.HS?.h h0) (HST.HS?.h h1) (HST.HS?.h h2)
	         (Set.singleton (StAE.region wr)) 
		 (Set.singleton (StAE.region wr));
	         cut (modifies_just (Set.singleton (StAE.region wr)) (HST.HS?.h h0) (HST.HS?.h h2))
	       end
	     | None -> 
	       begin
	       lemma_modifies_just_trans (HST.HS?.h h0) (HST.HS?.h h1) (HST.HS?.h h2) Set.empty Set.empty;
	       cut (modifies_just (Set.empty) (HST.HS?.h h0) (HST.HS?.h h2))
	       end
	   end;
	   frags
	 end

////////////////////////////////////////////////////////////////////////////////
// writeHandshake and helpers: repeatedly sending handshake messages
////////////////////////////////////////////////////////////////////////////////
// simplified to loop over Handshake traffic only;
// called both when writing and reading 
// returns WriteError or WrittenHandshake
//TODO: consider sending handshake warnings
//TODO: consider keeping some errors private
//TODO: consider inlining sendHandshake to save a spec.
//TODO: consider immediately sending post-completion traffic (e.g. TLS 1.2 Finished and TLS 1.3 Tickets)

//First, a wrapper around Handshake.next_fragment; 
//using monotonicity to show that the i'th epoch doesn't change

//07.29: should eventually move to Handshake.fst
//       although that module isn't verified yet 
//       so moving it there will cause us to lose 
//       regression testing for this function
let next_fragment_pre (i:id) (c:connection) h0 = 
    let s = c.hs in
    let es = Handshake.logT s h0 in
    let j = Handshake.iT s Writer h0 in 
    i=currentId_T c Writer h0 /\
    current_writer_pre c i h0 /\
    Handshake.hs_inv s h0 /\
    maybe_indexable es j /\
    (if j = -1 then PlaintextID? i else i == epoch_id es.(j))
val next_fragment: i:id -> c:connection -> ST (result (HandshakeLog.outgoing i))
  (requires (next_fragment_pre i c))
  (ensures (fun h0 result h1 -> 
    Handshake.next_fragment_ensures #i c.hs h0 result h1 /\
    (let w0 = Handshake.iT c.hs Writer h0 in   //Augmenting the post-condition of Handhshake.next_fragment 
     let es = Handshake.logT c.hs h0 in        //with this monotonicity propery
     indexable (Handshake.logT c.hs h0) w0 ==> (Handshake.logT c.hs h0).(w0) == (Handshake.logT c.hs h1).(w0)))) 
let next_fragment i c =  
  let s = c.hs in
  let h0 = ST.get() in 
  let ilog = Handshake.es_of s in 
  let w0 = Handshake.i s Writer in 
  let _  = if w0 >= 0 
	   then (MS.i_at_least_is_stable w0 (MS.i_sel h0 ilog).(w0) ilog;
		 FStar.Seq.contains_intro (MS.i_sel h0 ilog) w0 (MS.i_sel h0 ilog).(w0);
	         MR.witness ilog (MS.i_at_least w0 (MS.i_sel h0 ilog).(w0) ilog)) in
  trace ("HS.next_fragment "^(if ID12? i then "ID12" else (if ID13? i then "ID13" else "PlaintextID"))^"?"); 
  let res = Handshake.next_fragment s i in
  if w0 >= 0 then MR.testify (MS.i_at_least w0 (MS.i_sel h0 ilog).(w0) ilog);
  res


#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
unfold let writeHandshake_requires h_init c new_writer h = 
     	  let i_init = currentId_T c Writer h_init in 
   	  let i = currentId_T c Writer h in 
	  current_writer_pre c i h
	  /\ next_fragment_pre i c h
	  /\ (let wopt_init = current_writer_T c i_init h_init in
	     let wopt = current_writer_T c i h in
	     sendFragment_inv wopt h
	     /\ (None?new_writer ==> i == i_init /\ wopt == wopt_init) //the flag really indicates a potential change in the writer
	     /\ (authId i_init /\ authId i //TODO: would be nice to make this condition weaker, i.e., conditioned on each authId separately
		 ==> (if None? new_writer
		      then Some? wopt ==> SD.stream_deltas #i (Some?.v wopt) h == SD.stream_deltas #i (Some?.v wopt) h_init
		      else True)))(* (Some? wopt ==> SD.stream_deltas #i (Some?.v wopt) h == Seq.createEmpty) //haven't sent any application data yet on the new write *)
		        (* /\  *)//(Some? wopt_init ==> SD.stream_deltas #i_init (Some?.v wopt_init) h_init == SD.stream_deltas #i_init (Some?.v wopt_init) h)))))) //and the old writer's app data hasn't changed

unfold let writeHandshake_ensures h_init c new_writer h0 r h1 = 
      let i_init = currentId_T c Writer h_init in
      let i = currentId_T c Writer h1 in
      current_writer_pre c i h1
      /\ (match r with
      	 | WriteError _ _
      	 | WriteClose -> True
	 | WrittenHS new_writer' _ -> //the epoch didn't change
       	   let wopt_init = current_writer_T c i_init h_init in
       	   let wopt = current_writer_T c i h1 in
	   sendFragment_inv wopt h1
	   /\ (b2t (Some? new_writer) ==> b2t (Some? new_writer'))
	   /\ (None? new_writer' ==>
	       i_init == i
	       /\ wopt_init == wopt
	       /\ sendFragment_inv wopt h1
	       /\ (authId i ==> SD.stream_deltas #i (Some?.v wopt) h1 == SD.stream_deltas #i (Some?.v wopt) h_init)) //and we didn't write any application data
      	 | _ ->
      	   let wopt = current_writer_T c i h1 in
	   r <> Written /\
      	   sendFragment_inv wopt h1)

// Try to send a fragment for outgoing Handshake/CCS traffic, if any.
val writeHandshake: h_init:HST.mem //initial heap, for stating an invariant on deltas
		  -> c:connection
		  -> new_writer:option bool
		  -> ST ioresult_w 
  (requires (writeHandshake_requires h_init c new_writer))
  (ensures (writeHandshake_ensures h_init c new_writer))

#reset-options "--z3rlimit 1000 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let rec writeHandshake h_init c new_writer = 
  reveal_epoch_region_inv_all ();
  let i = currentId c Writer in
  let wopt = current_writer c i in
  trace ("writeHandshake"^(if Some? wopt then " (encrypted)" else " (plaintext)"));
  (* let h0 = get() in  *)
  match next_fragment i c with
  | Error (ad,reason) -> sendAlert c ad reason
  | Correct(HandshakeLog.Outgoing om next_keys complete) ->
      //From Handshake.next_fragment ensures, we know that if next_keys = false
      //then current_writer didn't change;
      //We also know that this only modifies the handshake region, so the delta logs didn't change
      let new_writer, send_ccs =
        match next_keys with
        | Some (appdata,ccs) -> Some appdata, ccs
        | None -> new_writer, false in
      trace ("HS.next_fragment returned "^
        (if Some?om then "a fragment" else "nothing")^
        (if send_ccs then "; CCS" else "")^
        (match next_keys with
          | None -> ""
          | Some (true, _) -> "; next_keys (for all data)"
          | Some (false,_) -> "; next_keys (for handshake only)")^
        (if complete then "; complete" else ""));
      match sendHandshake wopt om send_ccs with
      // we may have sent an handshake message and/or a CCS message;
      // as a post-condition of sendHandshake, we know that the deltas didn't change
      | Error (ad,reason) -> (
          recall_current_writer c;
          sendAlert c ad reason )
      | _   -> (
          recall_current_writer c;
          let j_ = Handshake.i c.hs Writer in  //just to get (maybe_indexable es j_)
          if Some? next_keys then Epochs.incr_writer (Handshake.epochs_of c.hs); // much happening ghostly
          let (str,stw) = !c.state in
          if complete then c.state := (Open, Open)  // much happening ghostly too
          else
          ( match next_keys with
            | Some(b, _) -> c.state := (str, (if b then Open else Ctrl))
            | None -> () );
          if complete || new_writer = Some true || (None? om && not send_ccs)
          then WrittenHS new_writer complete // done, either to writable/completion or because there is nothing left to do
          else if Some? new_writer //splitting cases just to narrow in on the assertion failure that prompted the assume
          then (
            let h = get () in 
            let j_ = Handshake.i c.hs Writer in  //just to get (maybe_indexable es j_)
            let _ =
              let s = c.hs in
              let es = Handshake.logT s h in
              assume (j_ < Seq.length es) in  //NS: weird; not sure why this is not provable
            writeHandshake h_init c new_writer)
          else writeHandshake h_init c new_writer)


////////////////////////////////////////////////////////////////////////////////
#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
val write: c:connection -> #i:id -> #rg:frange i -> data:DataStream.fragment i rg -> ST ioresult_w
  (requires (fun h -> 
    current_writer_pre c i h /\
    writeHandshake_requires h c (None #bool) h))
  (ensures (fun h0 r h1 -> 
    current_writer_pre c i h0 /\ ( 
    let wopt = current_writer_T c i h0 in
        match r with 
        | Written -> 
         (authId i ==> 
            (let d : DataStream.pre_fragment i = data in //A widening coercion as a proof hint, unpacking (d:fragment i rg) to a pre_fr
             Seq.equal (SD.stream_deltas #i (Some?.v wopt) h1) (snoc (SD.stream_deltas #i (Some?.v wopt) h0) (DataStream.Data d))))
       | _ -> True)))

#reset-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let write c #i #rg data =
  reveal_epoch_region_inv_all();
  let wopt = current_writer c i in
  let h0 = get () in 
  match writeHandshake h0 c None with
  | WrittenHS None _ ->
      // the caller index is still valid, so we attempt to send our application data
      // TODO static enforcement of appdata writability
      let frag = Content.CT_Data rg data in
      begin 
        match sendFragment c #i wopt frag with
        | Error(ad,reason) -> sendAlert c ad reason
        | _ -> Written
      end
  | r -> r 
      // we didn't write any application data
      // we report some handshake action; the user may retry at a different index.
      // variants may be more convenient,
      // e.g WrittenHS true false signals 0.5 writing, and we could then write AD and report completion.

////////////////////////////////////////////////////////////////////////////////
// NOT DESIGNED TO BE VERIFIED BEYOND THIS POINT
////////////////////////////////////////////////////////////////////////////////
#set-options "--lax"
// (old) outcomes?
// | WriteAgain -> sent any higher-priority fragment, same index, same app-level log (except warning)
// | Written    -> sent application fragment (when Some? appdata)
// | WriteDone  -> sent nothing              (when appdata = None)
// | WriteError None      _ -> closed the connection on unrecoverable error (same log, unclear app-level signal)
// | WriteError (Some ad) _ -> closed the connection (log extended with fatal alert)
// | WriteAgainClosing      -> will attempt to send an alert before closing
// | WriteClose              -> similar
// | WriteAgainFinishing    -> incremented the writer epoch.

//16-05-27 updated post-condition branches;
//         to be share between writing functions (each returning a subset of results); still missing details.

let write_ensures (c:connection) (i:id) (appdata: option (rg:frange i & DataStream.fragment i rg)) (r: ioresult_w) h0 h1 =
  let st0 = HST.sel h0 c.state in
  let st1 = HST.sel h1 c.state in
  let es0 = epochs c h0 in
  let es1 = epochs c h1 in
  let j = Handshake.iT c.hs Writer h0 in
  st_inv c h0 /\
  st_inv c h1 /\
  begin
    match r with
    | Written -> // writer view += Data appdata; no other visible effects.
        (match appdata with
        | None -> False
        | Some  (| rg, f |) ->
        j >= 0 /\ snd st0 = Open (* 16-05-27 not typechecking:  /\
        ( let wr = writer_epoch (Seq.index es0 j) in
          modifies_one (region wr) h0 h1 /\
          seqnT wr h1 = seqnT wr h0 + 1 /\
          (authId i ==> StAE.fragments wr h1 = snoc (StAE.fragments wr h0) (Content.CT_Data rg f))) *)
          // add something on the projection?
        )
    | WriteClose -> // writer view += Close (so we can't send anymore); only from calling sendAlert.
        snd st1 = Closed
    | WriteError oad reason ->
        // Something bad happened while writing (underspecified, for convenience)
        // * if appdata = None, then the current writer may have changed.
        // * current writer view += appdata.value (or not) += oad.value (or not)
        st1 = (Closed,Closed) /\
        (match oad with
        | Some ad -> True //TBC: writer view += at most appdata.value + ad
        | None    -> True //TBC: writer view += at most appdata.value
        )
        // TBC, describing what may have been added to the projection
    | WrittenHS newWriter complete -> True
        // we sent higher-priority traffic; no visible effects,
        // we may be in a new epoch and/or have completed a handshake
        // several cases to be detailed (see below), none of them changing writer views.
(* replacing:
    | WriteAgain -> // we sent higher-priority traffic; no visible effects.
        st0 = st1
        // only HS, Alert, and region wr were modified
        // the writer projection is unchanged
        // the iT indexes are unchanged

    | WriteDone -> // there was nothing to send [before reading]
        None? appdata
        // only internal changes in HS.

    | WriteAgainFinishing ->
        st0 = st1
        // we now have a new writer with an empty view; no other visible effects.
        // appdata was not sent, and we can't send AD until completion.

    | WriteHSComplete -> // rejoice! the handshake completed
        st1 = AD /\
        iT c.hs Writer h1 = iT c.hs Reader h1
        // should also state that the old epoch's log is unchanged, and the new epoch's log is empty.

    | WriteAgainClosing -> False
*)
  end

(*16-05-29 BEGIN OLDER VARIANT

val writeOne: c:connection -> i:id -> appdata: option (rg:frange i & DataStream.fragment i rg) -> ST ioresult_w
  (requires (fun h ->
    send_requires c i h
    /\ (let st = sel h c.state in
       let j = iT c.hs Writer h in
       j >= 0 ==> st=AD))) // CF 16-05-27 too strong
  (ensures (fun h0 r h1 -> True))
(*     let st = sel h0 c.state in *)
(*     let es = sel h0 c.hs.log in *)
(*     let j = iT c.hs Writer h0  in *)
(*     st_inv c h0 /\ *)
(*     st_inv c h1 /\ *)
(*     j == iT c.hs Writer h1 /\ //16-05-16 used to be =; see other instance above *)
(*     (if j < 0 then PlaintextID? i /\ h0 = h1 else *)
(*        let e = Seq.index es j in *)
(*        i == epoch_id e /\ ( *)
(*        let wr:writer i = writer_epoch e in *)
(*        modifies (Set.singleton (C?.region c)) h0 h1 *)
(* )))) *)


let writeOne c i appdata =
  allow_inversion (Handshake.outgoing i);
  let h0 = ST.get() in
  let wopt = current_writer c i in
  // alerts are now sent immediately, so we now start with Handshake
   match next_fragment i c.hs with
    | Handshake.OutError (x,y) -> unrecoverable c y // a bit blunt
    | Handshake.Outgoing om send_ccs next_keys complete ->
	    
      // we send handshake & CCS messages, and process key changes (TODO:restore precise checks and error handling)
      match sendHandshake wopt om send_ccs with
      | Error (_,y) -> unrecoverable c y
      | _   ->
        if next_keys           then c.state := BC; // much happening ghostly
        let st = !c.state in
        if complete && st = BC then c.state := AD; // much happening ghostly too
        if complete
	then WriteHSComplete
        else if Some? om && send_ccs
	then WriteAgain
        else
             // we finally attempt to send some application data; we may statically know that st = AD
             match st, appdata with
	     | AD, Some (rg,f) -> begin
	       match sendFragment c wopt (Content.CT_Data rg f) with
	       | Error (_,y) -> unrecoverable c y
	       | _   -> Written (* Fairly, tell we're done, and we won't write more data *)
	       end
             | _ -> WriteDone // We are finishing a handshake. Tell we're done; the next read will complete it.



let is_current_writer (#c:connection) (#i:id) (wopt:option (cwriter i c)) (h:HH.t) =
  match wopt with
  | None -> True
  | Some w ->
    iT c.hs Writer h >= 0
    /\ (let epoch_i = eT c.hs Writer h in
       w == Epoch?.w epoch_i)


////////////////////////////////////////////////////////////////////////////////
//NS reached up to here
////////////////////////////////////////////////////////////////////////////////


// in TLS 1.2 we send the Finished messages immediately after CCS
// in TLS 1.3 we send e.g. ServerHello in plaintext then encrypted HS

val writeAllFinishing: c:connection -> i:id -> ST ioresult_w
  (requires (fun h ->
    send_requires c i h)) //16-05-28 too strong: already includes incrementable.
  (ensures (fun h0 r h1 ->
    st_inv c h1 /\ modifies (Set.singleton c.region) h0 h1 /\
    (WriteError? r \/ WriteClose? r \/ Written? r)
  ))

let rec writeAllFinishing c i =
    assume false; //16-05-28
    if no_seqn_overflow c Writer then
    match writeOne c i None with
    // we disable writing temporarily
    | WriteAgain          -> writeAllFinishing c i
//   | WriteDone           -> MustRead

    // all other cases disable writing permanently
//  | WriteAgainClosing   -> writeClosing c i
    | WriteError x y      -> WriteError x y
    | WriteClose           -> WriteClose // why would we do that?

//  | MustRead            // excluded since responded only here
//  | Written             // excluded since we are not sending AD
//  | WriteAgainFinishing // excluded by the handshake logic (not easily proved)
    | WriteHSComplete     // excluded since we need an incoming CCS (not easily proved)
                          -> unexpected "[writeAllFinishing] writeOne returned wrong result"
    else                    unexpected "[writeAllFinishing] seqn overflow"


// called both by read (with no appData) and write (with some appData fragment)
// returns to read  { WriteError, WriteClose, WriteDone, WriteHSComplete }
// returns to write { WriteError, Written }
// (TODO: write returns { WriteHSComplete, MustRead } in renegotiation)
val writeAll: c:connection -> i:id -> appdata: option (rg:frange i & DataStream.fragment i rg) -> ST ioresult_w
  (requires (fun h ->
    send_requires c i h /\  //16-05-28 too strong: already includes incrementable.
    (Some? appdata ==> sel h c.state = AD)))
  (ensures (fun h0 r h1 ->
    st_inv c h1 /\ modifies (Set.singleton c.region) h0 h1 /\
    (None? appdata ==> WriteError? r \/ WriteDone? r \/ WriteHSComplete? r )))

let rec writeAll c i appdata =
    if no_seqn_overflow c Writer then
    (assume false; // TODO
    match writeOne c i appdata with
    | WriteAgain          -> writeAll c i appdata
//  | WriteAgainClosing   -> writeClosing c i // TODO, using updated epoch_id (epoch_w c)
    | WriteAgainFinishing -> // next writer epoch!
                            writeAllFinishing c i // TODO, using updated epoch_id (epoch_w c)
    | WriteError x y      -> WriteError x y
    | WriteClose           -> WriteClose
    | WriteDone           -> WriteDone
//  | MustRead            -> MustRead
    | Written             -> Written
    | _                   -> unexpected "[writeAll] writeOne returned wrong result")
    else                    unexpected "[writeAll] seqn overflow"


//Question: NS, BP, JL: Is it possible for write to return WriteAgain or a partially written data?
// no: we always write the whole fragment or we get a fatal error.

let write c i rg data = writeAll c i (Some (| rg, data |))

END OLDER VARIANT *)



// Two API functions to close down the connection
// [review function names]

// Our monotonic invariant on streams already indicates
// whether the last delta is final, so there is no need
// for additional state to keep track of half-closure.

// We notify, and hope to get back the peer's notify.

let writeCloseNotify c =
  trace "writeCloseNotify";
  sendAlert c AD_close_notify "full shutdown"

// We notify and don't wait for confirmation.
// Less reliable. Makes the connection unwritable.
// Returns sentClose  ==> the datastream is extended with AD_close_notify
//      or some unrecoverable error (in which case we don't know)

let writeClose c =
  let r = sendAlert c AD_close_notify "half shutdown" in
  c.state := (Closed, Closed);
  r


(** incoming (implicitly writing) ***)

// By default, all i:id are reader identifiers, i.e. peerId (handshakeId (reader_epoch.h)
// FIXME: Put the following definitions close to range and delta, and use them

type query = Cert.chain
type msg_i (i:id) = (range * DataStream.delta i)

(* merged with ioresult_i
type readOutcome (e:epoch) =
    | WriteOutcome of writeOutcome    // now? { ReadError, DontWrite, CompletedSecond, Read(Close) }
    | RError of string (* internal *) // now ReadError(None,err)
    | CertQuery of query * bool       // now CertQuery
    | RHSDone                         // now Complete
    // now Read(delta e) with subcases Data, Close, Alert
    | RAppDataDone of msg_i | RClose
    | RFatal of alertDescription (* The alert we received *)
    | RWarning of alertDescription (* The alert we received *)
    // internal states only
    | ReadAgain | ReadAgainFinishing | ReadFinished *)


type ioresult_i (i:id) =
    | Read of DataStream.delta i
        // This delta has been added to the input stream;
        // We may have read
        // - an application-data fragment or a warning (leaving the connection live)
        // - a closure or a fatal alert (tearing down the connection)
        // If the alert is a warning, the connection remains live.
        // If the alert is final, the connection has been closed by our peer;
        // the application may reuse the underlying TCP stream
        // only after normal closure (a = AD_close_notify)
        // We have not sent anything notable (no AD, no alerts).

    | ReadError: o:option alertDescription -> txt:string -> ioresult_i i
        // We encountered an error while reading, so the connection dies.
        // we return the fatal alert we may have sent, if any,
        // or None in case of an internal error.
        // The connection is gone; its state is undefined.

    | CertQuery: query -> bool -> ioresult_i i
        // UNUSED
        // We received the peer certificates for the next epoch, to be authorized before proceeding.
        // the bool is what the Windows certificate store said about this certificate.

    | Update: writeable:bool -> ioresult_i i
      // We made some progress, may have installed new keys
      // and/or change their usability for application data.
      // (The application will need to fetch both resulting indexes.)

      // `Update false` typically requires reading again; it covers e.g.
      // - server accepted 0RTT, can receive data at the new index.
      // - client sent EOED, cannot write until handshake completing.

      // `Update true` covers e.g.
      // - client started 0RTT, can send data at the new index.
      // - server started 0.5RTT, can send data at the new index.
      // - rekeying (TBC)

      // These flags are cumulative---we can accumulate them until idle.
      // Consider returning the new indexes too?

    | Complete
      // the client SHOULD check whether 0RTT was acepted or not!
      // We successfully completed the handshake. We may now
      // read/write data in both directions (at the resulting indexes)
      // (e.g. in TLS 1.2 we have already sent our finished message, so only the read epoch changes)

    // internal states only
    | ReadAgain
    | ReadAgainFinishing

//  | ReadFinished
//  | DontWrite
//      // Nothing read yet, but we can't write anymore.

let string_of_ioresult_i (#i:id) = function
  | Read (DataStream.Data d) -> "Read "^string_of_int (length (DataStream.appBytes #i #Range.fragment_range d)) ^ " bytes of data"
  | Read (DataStream.Alert a) -> "Read Alert "^string_of_ad a
  | Read (DataStream.Close) -> "Read Close"
  | ReadError (Some o) txt -> "ReadError "^string_of_error(o,txt) 
  | ReadError None txt -> "ReadError "^txt
  | CertQuery _ _ -> "CertQuery"
  | Update b -> "Update "^(if b then "writable" else "read-only")
  | Complete -> "Complete"
  | ReadAgain -> "ReadAgain" 
  | ReadAgainFinishing -> "ReadAgainFinishing"

let live_i e r = // is the connection still live?
  match r with
  | Read d        -> not(DataStream.final e d)
  | ReadError _ _ -> false
  | _             -> true

// let's specify reading d off the input DataStream (incrementing the reader pos)

val sel_reader: h:HST.mem -> connection -> GTot (option ( i:id & StAE.reader i )) // self-specified
let sel_reader h c =
  let es = epochs c h in
  let j = Handshake.iT c.hs Reader h in
  (if j < 0 then None else
  let e = Seq.index es j in
  let i = peerId (epoch_id e) in
  assume(StAE.is_stream i);
  Some (| i, reader_epoch e |))
  // todo: add other cases depending on dispatch state

type delta h c =
  (match sel_reader h c with
  | Some (| i , _ |) -> DataStream.delta i
  | None             -> DataStream.delta (PlaintextID (c_nonce c)))


// frequent error handler; note that i is the (unused) reader index
//val alertFlush: TODO: WE REALLY NEED A VAL!
let alertFlush c ri (ad:alertDescription { isFatal ad }) (reason:string) =
  let written = sendAlert c ad reason in
  let r : ioresult_i ri = 
    match written with
    | WriteClose      -> Read DataStream.Close // do we need this case?
    | WriteError x y -> ReadError x y in         // how to compose ad reason x y ?
  r

val readFragment: c:connection -> i:id -> ST (result (Content.fragment i))
  (requires (fun h0 ->
    let es = epochs c h0 in
    let j = Handshake.iT c.hs Reader h0 in
    st_inv c h0 /\
    (if j < 0 then PlaintextID? i else
      let e = Seq.index es j in
      i == peerId (epoch_id e) /\
      StAE.incrementable (reader_epoch e) h0)))
  (ensures (fun h0 r h1 ->
    let es = epochs c h0 in
    let j = Handshake.iT c.hs Reader h0 in
    st_inv c h0 /\
    st_inv c h1 /\
    j == Handshake.iT c.hs Reader h1 /\
    (if j < 0 then PlaintextID? i /\ h0 == h1 else
      let e = Seq.index es j in
      i == peerId (epoch_id e) /\
      (let rd: StAE.reader i = reader_epoch e in
      modifies (Set.singleton (StAE.region rd)) h0 h1 /\
      (match r with
      | Error e -> True // don't know what seqnT is, don't care.
      | Correct f ->
          StAE.seqnT rd h1 = StAE.seqnT rd h0 + 1 /\
          (authId i ==>
            (let frs = StAE.fragments #i rd h0 in
            let n = StAE.seqnT rd h0 in
            n < Seq.length frs /\
            f == Seq.index frs n)
  ))))))

let readFragment c i =
  assume false; // 16-05-19 can't prove POST.
  match Record.read c.tcp with
  | Error e -> Error e
  | Correct(ct,pv,payload) ->
    let es = MR.m_read (Handshake.es_of c.hs) in
    let j : Handshake.logIndex es = Handshake.i c.hs Reader in
    //trace ("Epoch index: "^string_of_int j);
    if j < 0 then // payload is in plaintext
      let rg = Range.point (length payload) in
      Correct(Content.mk_fragment i ct rg payload)
    else
      // payload decryption
      let e = Seq.index es j in
      let Epoch #r #n #i hs rd wr = e in
      if not (valid_clen i (length payload))  // cache? check at a lower level?
      then ( 
        // we might make an effort to parse plaintext alerts
        trace ("bad payload: "^print_bytes payload);
        Error(AD_decryption_failed, "Invalid ciphertext length"))
      else 
      match StAE.decrypt (reader_epoch e) (ct,payload) with
      | None -> Error(AD_internal_error,"Decryption failure")
      | Some f -> 
          trace "StAE decrypt correct."; 
          Correct f

// We receive, decrypt, parse a record (ct,f); what to do with it?
// i is the presumed reader, threaded from the application.

private val readOne: c:connection -> i:id -> St (ioresult_i i)
//  (ensures ioresult is not Complete | CompletedSecond | DontWrite)

let readOne c i =
  assume false; //16-05-19
  match readFragment c i with
  | Error (x,y) -> alertFlush c i x y
  | Correct (Content.CT_Alert rg ad) ->
      begin
        trace ("read Alert fragment "^TLSError.string_of_ad ad);
        if ad = AD_close_notify then
          if Closed? (snd !c.state)
          then ( // received a notify response; cleanly close the connection.
            c.state := (Closed,Closed);
            Read (DataStream.Alert ad))
          else ( // received first notification; immediately enqueue notify response [RFC 7.2.1]
            c.state := (Closed, snd !c.state);
            alertFlush c i AD_close_notify "notify response")  // switching to (Closed,Closed)
            // NB we could ignore write errors here.
        else (   //
          if isFatal ad then disconnect c;
          Read (DataStream.Alert ad))
          // else we carry on; the user will know what to do
      end
      // recheck we tolerate alerts in all states; used to be just Init|Open, otherwise:
      // alertFlush c AD_unexpected_message (perror __SOURCE_FILE__ __LINE__ "Message type received in wrong state")

  | Correct(Content.CT_Handshake rg f) ->
      begin
        trace "read Handshake fragment";
        match Handshake.recv_fragment c.hs rg f with
        | Handshake.InError (x,y) -> alertFlush c i x y
        | Handshake.InQuery q a   -> CertQuery q a
        | Handshake.InAck next_keys complete ->
            if complete
            then (c.state := (Open, Open); Complete)
            else ReadAgain
            (* // TODO: additional sanity checks.
            ( match !c.state with
            | BC ->
                   // if epoch_r c = epoch_w c then
                   (c.state := AD; Complete)
                   // else (disconnect c; ReadError None "Invalid connection state")
                   )
            else ReadAgain *)
      //| InFinished    -> ReadAgain // should we care? probably before e.g. accepting falseStart traffic
      // recheck correctness for all states; used to be just Init|Finishing|Open
      end
  | Correct(Content.CT_CCS rg) ->
      begin
        trace "read CCS fragment";
        match Handshake.recv_ccs c.hs with
        | Handshake.InError (x,y) -> alertFlush c i x y
        | Handshake.InAck true false -> ReadAgainFinishing // specialized for HS 1.2
      end
  | Correct(Content.CT_Data rg f) ->
      begin
        trace "read Data fragment"; 
        match fst !c.state with
        | Open -> let f : DataStream.fragment i fragment_range = f in Read #i (DataStream.Data f)
        | _ -> alertFlush c i AD_unexpected_message "Application Data received in wrong state"
      end

 
// scheduling: we always write up before reading, to advance the Handshake.
// those writes are never AppData; they may be for other/changing epochs;
// the write outcomes that matter are: Error, Complete, and Done.
val read: connection -> i:id -> St (ioresult_i i)
let rec read c i =
    assume false;//16-05-19
    let h0 = ST.get() in
    let st0 = !c.state in
    let r = writeHandshake h0 c None in
    match r with
    | WriteError x y -> ReadError x y           // TODO review errors; check this is not ambiguous
    | WriteClose -> unexpected "Sent Close" // can't happen while sending?
    | WrittenHS newWriter complete ->
        let st1 = !c.state in
        trace ("read: WrittenHS, "^string_of_state st1^(
          match newWriter, complete with
          | Some b, true -> "new writer: complete"
          | Some true, _ -> "new writer: writable"
          | Some false, _ -> "new writer: handshake-only"
          | None, true -> "same writer; complete"
          | None, false -> "nothing"));
        // NB writeHandshake already updated the state

        // return at once, so that the app can authorize and use new indexes.
        if complete then Complete
        else if newWriter = Some true then Update true

        else if newWriter = Some false && snd st0 = Ctrl then (
          trace "ignore handshake-specifc key change; calling read again";
          read c i ) // i is off?!
          // We can drop `Update false` when in (ctrl,ctrl)
          // To read again, we need to compose the update signals -- or just let the app loop?
          // We must report *some* update, but then what to do with the data??

        else
    
    // nothing written; now we can read
    // note that the reader index is unchanged
    let result = readOne c i in (
    trace ("readOne "^string_of_ioresult_i result); 
    match result with
    // TODO: specify which results imply that c.state & epochs are unchanged
    | ReadAgain             -> read c i
    | ReadAgainFinishing    -> read c i //was: readAllFinishing c
    | ReadError x y         -> ReadError x y
    | CertQuery q adv       -> CertQuery q adv
    | Read delta            -> Read delta
    | Complete              -> Complete // In TLS 1.2 client and TLS 1.3 server it makes sense to complete upon reading (e.g. reading ServerFinished in 1.2) instead of going through another roundtrip with the handshake with an extra state to Complete in writeHandshake
    )


(* 16-05-28 WIP

let read_ensures (c:connection) (i:id) (r:ioresult_i i) h0 h1 =
  let st0 = sel h0 c.state in
  let st1 = sel h1 c.state in
  let es0 = epochs c h0 in
  let es1 = epochs c h1 in
  let j = iT c.hs Reader h0 in
  st_inv c h0 /\
  st_inv c h1 /\
  begin
    // When authId i, the reader's view is the projected fragment of the peer's writer log up to the reader's seqn
    // (something worth defining, and monotonic).
    // Unless mentioned otherwise, the epoch indexes, the reader view, and the writer view are unchanged.
    match r with
    | ReadError x y ->
        // Local error; x indicates whether the writer view is extended by a fatal alert or not.
    
    | Read delta -> True
        // If authId i, then the reader view is extended by delta.
        // If delta is terminal, then the connection is now closed.
        // In particular, if delta is a (first) closeNotify and the writer view was open, it has been extended with a (second) closeNotify.
        // [for now the second notify is deferred]
        // [DataStream.Close vs closeNotify?]
        // [We get non-alerts only in some states]

    | CompletedFist ->
        // We have new indexes, with empty reader and writer views.
        // If the prior epoch was honest, their views are synchronized with the peer.
(*
    // We will need more signals for new keys:
    | NextWriter ->
        // The writer has changed; the new writer view is empty.
        // The connection is not writable, except perhaps with FalseStart/0.5RTT, or for alerts.
*)

    | ReadAgain -> True            // nothing changed in views and epochs                      [local to read loop]
    | ReadAgainFinishing -> True   // nothing changed in views, but we have a new reader epoch [local to read loop]

    | CertQuery _ _ ->          // nothing changed, and we need to authorize the peer's certificate chain.



...
            let st = !c.state in
            match st with
            | Half Reader  ->

            | Closed -> Read DataStream.Close // we already sent a close_notify, tell the user it's over
            | _ ->
                let written = writeClosing c (rd_i c) (*FIXME*) in
                match written with
                | WriteClose      -> Read DataStream.Close // clean shutdown
                | WriteError x y -> ReadError x y
                | _              -> ReadError None (perror __SOURCE_FILE__ __LINE__ "") // internal error
                )
*)

//* we used to specify the resulting connection in ioresult_i,
//* now we do that in the read postcondition


(*
// -----------------------------------------------------------------------------

// responding to a certificate-validation query,
// so that we have an explicit user decision to blame,
// but in fact a follow-up read would do as well.
// to be adapted once we have a proper PKI model
//val authorize : c:Connection -> q:query -> ST ioresult_i
//  (requires (fun h0 -> True))
//  (ensures (fun h0 result h1))

let authorize c q =
    let res = Handshake.authorize (C?.hs c) q in
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
    writeClosing c
*)
