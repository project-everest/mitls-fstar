module TLSOutline

//16-05-30 this file is now out of date vs TLS.fst (not sure what views to use)
//16-05-30 but still provides exemplary clients and servers.

// Draft TLS API using hyperheaps in F*
// incorporating definitions and comments from TLS.fs7 and TLS.fsi
// - each connection runs through a sequence of epochs
// - each epoch has two streams of application data
// - each secure stream maintains a log of data (and warnings) written so far
//   and the reader position in that log.

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found
open FStar.Monotonic.RRef
open FStar.Ghost

open Platform.Bytes
open Platform.Error
open Platform.Tcp

open TLSError
open TLSInfo


// using DataStream 

type hh = HyperHeap.t


type rid = r:rid{r<>root}

assume val tls_region    : r:rid{parent r = root}
assume val epochs_region : r:rid{parent r = root /\ r <> tls_region}

// an API abstraction over epochs
// epochs are partnered statically (ie, their partner is known at the time of creation)
assume type epoch
assume val epoch_region:      epoch -> Tot rid
assume val epoch_peer_region: epoch -> Tot rid
assume val epochId:           epoch -> Tot id  // globally unique; internally it is (hs_id h) for the handshake h
assume val writtenT:          epoch -> hh -> Tot (Seq.seq (DataStream.delta (epochId e))) //TODO: it is well-formed (note reconcile list vs seq)
assume val readseqT:          epoch -> hh -> Tot nat
assume type is_initial_epoch: epoch -> Type //TODO: maybe this can be removed or defined as the epoch in its initial state
//TODO: an API for the duality on ids

//Do we need such a function? Perhaps a stateful one to record paired epochs
// assume val partner: epoch -> HyperHeap.t -> Tot epoch

// connections may be partnered dynamically (ie, they are partnered by the assignment of partnered epochs to connections)
assume type connection
//field accessors of connections
assume val c_id:      connection -> Tot random         //a unique identifier for the connection, i.e., its local nonce
assume val c_role:    connection -> Tot role                  //Server or Client
assume val c_tcp:     connection -> Tot networkStream
assume val c_resume:  connection -> Tot (option sessionID)
assume val c_config:  connection -> Tot config
//properties of connections for specification purposes only
assume val c_region:  connection -> Tot rid            //the region in which the connection is allocated
assume val c_regionsT:connection -> hh -> Tot (Set.set HyperHeap.rid) //the dynamic set of regions of connection and the connection's current epochs
//TODO: define c_regionsT c h as the c_region c and all the regions of the (epochsT c) (not including the peer regions)

assume type c_inv  :  connection -> hh -> Type          //the private connection invariant
assume val readableT: connection -> hh -> Tot bool // indicates whether read is callable (for any purpose)
assume val writableT: connection -> hh -> Tot bool // indicates whether write is callable (for sending appdata/closing)
assume val epochsT:   connection -> hh -> Tot (Seq.seq epoch)  //the current sequence of epochs associated to a connection

//TODO: move this to FStar.Seq
type seq_prefix (#a:Type) (s1:Seq.seq a) (s2:Seq.seq a) =  
  exists sfx. Seq.append s1 sfx = s2

//an abstract update condition on the connection log
type c_log_extension (#a:Type) (s0:erased (Seq.seq a)) (s1:erased (Seq.seq a)) : Type
(* Internally, we want this to include, at least:
   1. seq_prefix (reveal s0) (reveal s1)
   2. stable assignment of epochs to connections (although this could be pushed inside mrefs of each connection)
   3. ... ?
*)

//a log of all (erased) connections created so far, monotonically growing
//NB: the erasure may not be sustainable for use in ideal mode
//    e.g., when generating new connections we will want to inspect the connection_log 
assume val connection_log : m_rref tls_region (erased (Seq.seq connection)) c_log_extension
assume type c_log_inv : hh -> Type
type is_conn (c:connection) (h:hh) = b2t (SeqProperties.mem c (reveal (sel h connection_log)))
//A conn is a connection known to be in the connection log
type conn = c:connection{witnessed (is_conn c)}


(* init requires an assume to handle top-level effects *)
assume val init : unit -> ST unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> c_log_inv h1
                        /\ fresh_region tls_region h0 h1
			/\ fresh_region epochs_region h0 h1))

(*** SEPARATION INVARIANTS ***)
assume val epoch_region_peer: e:epoch -> Lemma
  (ensures (parent (epoch_region e) = epochs_region
	    /\ parent (epoch_peer_region e) = epochs_region
	    /\ disjoint (epoch_region e) (epoch_peer_region e)))

assume val c_log_inv_separation: c1:connection -> c2:connection{c_id c1 <> c_id c2} -> h:hh -> Lemma
  (requires (c_log_inv h /\ is_conn c1 h /\ is_conn c2 h))
  (ensures (disjoint_regions (c_regionsT c1 h) (c_regionsT c2 h))) //NB: this only works because c_regionsT does not collect the peer_regions

(*** PARTNERING INVARIANTS ***)
(* epoch partnering is a static property *)
assume type partnered_epochs: epoch -> epoch -> Type
assume val epoch_ofT: connection -> hh -> Tot (option epoch)         //the current epoch of a connection
let epoch_ofT' (c:connection) (h:hh{is_Some (epoch_ofT c h)}) = Some.v (epoch_ofT c h)
assume val epoch_assigned_to: epoch -> hh -> Tot (option connection) //the stable assignment of an epoch to a connection
type was_assigned_to (e:epoch) (c:connection) (h:hh) = (epoch_assigned_to e h == Some c)
assume val epoch_of: c:conn -> ST (option epoch)
  (requires c_log_inv)
  (ensures (fun h0 e h1 -> 
    h0=h1 /\
    epoch_ofT c h1 = e /\
    (is_Some e ==> witnessed (was_assigned_to (Some.v e) c))))

(* connection partnering is state dependent ... it is not necessarily stable
     But, we should be able to prove that it is symmetric *)
type partnered_conn (c1:connection) (c2:connection) (h:hh) = 
  is_Some (epoch_ofT c1 h) /\
  is_Some (epoch_ofT c2 h) /\
  partnered_epochs (epoch_ofT' c1 h) (epoch_ofT' c2 h)

(* relating index of the peer to the epoch's peer *)

(*** FRAMING INVARIANTS ***)
assume val frame_c_inv: c:connection -> h0:hh -> h1:hh -> Lemma 
  (requires (HyperHeap.equal_on (c_regionsT c h0) h0 h1
	     /\ c_log_inv h0
	     /\ c_inv c h0))
  (ensures (c_log_inv h0
	    /\ c_inv c h1
 	    /\ readableT c h0 = readableT c h1
	    /\ writableT c h0 = writableT c h1 
	    /\ epochsT c h0   = epochsT c h1 
	    /\ Connection.Seq_forall 
			 (fun e -> writtenT e h0 = writtenT e h1 /\
			        readseqT e h0 = readseqT e h1)
		         (epochsT c h0)))

(*** SECURITY INVARIANT ***)
//Question: is is possible for c1 and c2 to be partnered now but for c1 to have been partnered with some other c2' previously? *)
assume val partnered_conn_inv: c1:connection -> c2:connection -> h:hh -> Lemma
  (requires (partnered_conn c1 c2 h))
  (ensures (partnered_conn c1 c2 h
	   /\ readseqT (epoch_ofT' c1 h) h <= Seq.length (writtenT (epoch_ofT' c2 h) h)    //the current reader is behind the writer
	   /\ readseqT (epoch_ofT' c2 h) h <= Seq.length (writtenT (epoch_ofT' c1 h) h)   //on both sides
	   /\ (forall e1 e2. e1 <> epoch_ofT' c1 h                         //and for any old partnered epochs (can we get this?)
		       /\ was_assigned_to e1 c1 h
		       /\ e2 <> epoch_ofT' c2 h 
		       /\ was_assigned_to e2 c2 h
		       /\ partnered_epochs e1 e2
		       ==> (readseqT e1 h = Seq.length (writtenT e2 h)           //everything that was sent was read
  		         /\ readseqT e2 h = Seq.length (writtenT e1 h)))))       //on both sides


(*** CONTROL API ***)
type initial (r:role) (ns:_) (cfg:_) (resume:_) (cn: connection) (h:hh) = 
    extends (c_region cn) tls_region /\ // we allocate a fresh, opaque region for the connection
    c_role cn   = r /\
    c_tcp cn    = ns /\
    c_resume cn = resume /\
    c_config cn = cfg /\
    witnessed (is_conn cn) /\
    is_Some (epoch_ofT cn h) /\
    is_initial_epoch (epoch_ofT' cn h)

(* lemma about the initial epoch *)
val initial_epoch_empty : h:hh -> e:epoch{is_initial_epoch e} -> Lemma 
  (requires (c_log_inv h))
  (ensures (Seq.length (writtenT e h) = 0
	   /\ readseqT e h = 0))

//* should we still return connectionInfo ?
//* merging connect and resume with an optional sessionID
val connect: ns:networkStream -> c:config -> resume: option sessionID -> ST conn
  (requires c_log_inv)
  (ensures (fun h0 cn h1 ->
    c_log_inv h1 /\
    modifies Set.empty h0 h1 /\
    initial Client ns c resume cn h1))
  //TODO: even if the server declines, we authenticate the client's intent to resume from this sid.

//* do we need both?
val accept: tcpListener -> c:config -> ST conn
  (requires c_log_inv)
  (ensures (fun h0 cn h1 ->
    c_log_inv h1 /\
    modifies Set.empty h0 h1 /\
    (exists ns. initial Server ns c None cn h1)))

val accept_connected: ns:networkStream -> c:config -> ST conn
  (requires c_log_inv)
  (ensures (fun h0 cn h1 ->
    c_log_inv h1 /\
    modifies Set.empty h0 h1 /\
    initial Server ns c None cn h1))

// the client can ask for rekeying --- no immediate effect
val rekey: cn:conn { c_role cn = Client } -> ST unit
  (requires c_log_inv)
  (ensures (fun h0 b h1 -> 
     c_log_inv h1 /\
     modifies Set.empty h0 h1)) // no visible change in cn

val rehandshake: cn:conn { c_role cn = Client } -> c:config -> ST unit
  (requires c_log_inv)
  (ensures (fun h0 b h1 -> 
    c_log_inv h1 /\
    modifies Set.empty h0 h1)) // no visible change in cn

val request: cn:conn { c_role cn = Server } -> c:config -> ST unit
  (requires c_log_inv)
  (ensures (fun h0 b h1 -> 
    c_log_inv h1 /\
    modifies Set.empty h0 h1)) // no visible change in cn


(*** WRITING ***)
(* // assuming writer_log is the high-level projection of the log  *)

 
type ioresult_w =
    // public results
    | Written             // Application data was written, and the connection remains writable
    | WriteError: al:option alertDescription -> txt: string -> ioresult_w // The connection is down, optionally after sending a fatal alert (on the current writer)
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


type modifies_c c h0 h1 =
  modifies (c_regionsT c h1) h0 h1 /\   //may modify all the (non-peer) regions of the connections
  (let epochs0 = epochsT c h0 in 
   let epochs1 = epochsT c h1 in
   seq_prefix epochs0 epochs1 /\        //but the epochs only grew
   (forall (i: nat { i < Seq.length epochs0 - 1 }). //and for all but the last epoch, nothing changed
    writtenT (Seq.index epochs0 i) h0 = writtenT (Seq.index epochs1 i) h1 /\
    readseqT (Seq.index epochs0 i) h0 = readseqT (Seq.index epochs1 i) h1))

assume val transitive_modifies_c : c:connection -> h0:hh -> h1:hh -> h2:hh -> Lemma
  (requires (modifies_c c h0 h1 /\
	     modifies_c c h1 h2))
  (ensures (modifies_c c h0 h2))

assume val write: c:conn -> i:id -> rg:Range.frange i -> data: DataStream.fragment i rg -> ST ioresult_o
  (requires (fun h0 ->
    c_log_inv h0 /\
    writableT c h0 /\            //TODO: make it so that writableT ==> implying epochsT c h0 is not empty
    is_Some (epoch_ofT c h0) /\  
    i = epochId (epoch_ofT' c h0)))
  (ensures (fun h0 r h1 ->
    c_log_inv h1 /\
    modifies_c c h0 h1 /\            //modified at most the last epoch
    epochsT c h1 = epochsT c h0 /\ //we didn't move to a new epoch
    is_Some (epoch_ofT c h0) /\ 
    i = epochId (epoch_ofT' c h0) /\
   ((fun (current:epoch{current=epoch_ofT' c h0}) -> (* TODO: fix ugly encoded let *)
     (fun (log0:Seq.seq (DataStream.delta i))
        (log1:Seq.seq (DataStream.delta i)) -> 
	(r = Written ==> (
	  log1 = SeqProperties.snoc log0 (DataStream.Data data) /\   // should it be conditioned on authId?
	  readableT c h1 = readableT c h0 /\ 
	  readseqT current h1 = readseqT current h0   /\
	  writableT c h1 = writableT c h0  ))
        /\
	(is_WriteError r ==> (
  	  (log1 = (match WriteError.al r with 
		       | None -> log0
	               | Some v -> SeqProperties.snoc log0 (DataStream.Alert v))) /\
	  ~(readableT c h1) 
	  /\ readseqT current h1 = readseqT current h0 /\
	  ~(writableT c h1)
	  )))
     (writtenT current h0)
     (writtenT current h1))
     (epoch_ofT' c h0))))

(*** READING ***)
type ioresult_r (i:id) =
    | Read of DataStream.delta i
        // this delta has been added to the input stream; we may have read
        // - an application-data fragment or a warning (leaving the connection live)
        // - a closure or a fatal alert (tearing down the connection)
        // If the alert is a warning, the connection remains live.
        // If the alert is final, the connection has been closed by our peer;
        // the application may reuse the underlying TCP stream
        // only after normal closure (a = AD_close_notify)

    | ReadError: o:option alertDescription -> txt:string -> ioresult_r i
        // We encountered an error while reading, so the connection dies.
        // we return the fatal alert we may have sent, if any,
        // or None in case of an internal error.
        // The connection is gone; its state is undefined.

    | CertQuery : q:Cert.chain -> b:bool -> ioresult_r i
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

type ioresult_i (i:id) = i:ioresult_r i{is_Read i \/ is_ReadError i \/ is_CertQuery i \/ is_CompletedFirst i \/ is_CompletedSecond i \/ is_DontWrite i}
assume val dual : id -> Tot id //TODO: move this to TLSInfo?

assume val read: c:conn -> i:id -> ST (ioresult_i i)              // unclear whether we should pass i in.
  (requires (fun h0 -> 
    c_log_inv h0 /\
    readableT c h0 /\                   //TODO: this should imply the next line
    is_Some (epoch_ofT c h0) /\  
    i = dual (epochId (epoch_ofT' c h0))))
  (ensures (fun h0 r h1 ->
    c_log_inv h1 /\
    modifies_c c h0 h1 
    // (r = Read d ==> ... /\ ) /\ TODO: complete this
     ))


(* // hopefully mustRead is gone.  *)
(* //  | MustRead  // Nothing written, as the connection is busy completing a handshake *)

(* // all the calls below are ghost & read-only; they depend only on c's region,  *)
(* // and their result are determined by the sequence of calls (arguments, results, and postconditions) *)
(* // consider using a log of epoch views instead of epochs *)
(* // fix r/w dual indexing! *)

(* // by design, the current values of writerId c and readerId c *)
(* // are determined by the call sequence --- no need to call them. *)

(* // *all* stateful connection calls are specializations of: *)


(* // NB the log can silently extend to new epochs (with empty log projections) *)
(* // NB we never expose reader/writer at different epochs.  *)

(* val sample: c:conn -> ... -> ST r *)
(*   (requires (fun h0 -> connection_log_inv h0)) *)
(*   (ensures (fun h0 r h1 ->  *)
(*     connection_log_inv h1 *)
(*     /\ regions_of c h0 <= regions_of c h1 *)
(*     /\ modifies (regions_of c h1) h0 h1  *)
(*     /\ "current epoch, readable, writeable, and the log after projection are all determined by the results & posts of prior calls"  *)
(*     /\ "current and the log contents after projection are monotonic" /\ *)
(*     "epochId is the id of an epoch in the log" /\  *)
(*     "the DataStream projection of all fragment logs for all epochs after epochId are empty" /\  *)
(*     "the DataStream projection of all fragment logs for all epochs are monotonic" /\  *)

(* //TODO: unclear how to fold in 0RTT *)






(* // ------------------- typical call sequence ------------------------- *)

(* // for simplicity, we assume all requests and responses fit in a single fragment. *)


let client (here:rid) tcp config_1 request =
  let c = connect here tcp config_0RTT None in
  // nothing sent yet, except possibly for TCP
  // we write in cleartext until we have the 0RTT index.
  match read c noId with
  //    ClientHello
  //      + KeyShare             -------->
  //                                                  ServerHello
  //                                                   + KeyShare
  //                                         {EncryptedExtensions}
  //                                         {CertificateRequest*}
  //                                        {ServerConfiguration*}
  //                                                {Certificate*}
  //                                          {CertificateVerify*}
  //                             <--------              {Finished}
  //   {Certificate*}
  //   {CertificateVerify*}
  //   {Finished}                -------->
  | Complete i -> 
  let f0 = DataStream.plain i rg0 request in
  match write c f0 with 
  //   [Request]                 -------->
  | Written ->
  match read c i with 
  //                             <--------      [Application Data]
  | Read (Data g0) -> 
  closeNotify c; 
  //   [CloseNotify]             -------->
  match read c i with 
  //                             <--------           [CloseNotify] 
  | Read Close -> g0 
  // At this point, if authId i, I know that 
  // (1) my peer's writer view is exactly ( Data g0 ; Close ), 
  // (2) my peer's reader view is exactly ( Data f0 ; Close ).

  // it seems convenient to have complete return i.
  // the client need not be aware of the handshake epoch.
  // should connect read to completion?

  // we have exactly the same code for 1.2 and 1.3 1RTT 
  // (even with falseStart)

let client_05 (here:rid) tcp config_05 request =
  let c = connect here tcp config_0RTT None in
  // nothing sent yet, except possibly for TCP
  // we write in cleartext until we have the 0RTT index.
  match read c noId with
  | FalseStart i -> 
  // let's hope we are Ok...
  let f0 = DataStream.plain i rg0 request in
  match write c f0 with 
  | Written ->
  match read c i with 
  | Complete i -> 
  // we were Ok!
  match read c i with 
  | Read (Data g0) -> g0 
  //...


// could write e.g. 
let complete c = 
  match read c noId with
  | Complete i -> i 
  | _          -> failwith "no secure connection"

let plain i f = DataStream.plain i (Range.point (length f)) f


let client0RTT_13 tcp config_0RTT request =
  let c = connect tcp config_0RTT None in
  // nothing sent yet, except possibly for TCP
  // we write in cleartext until we have the 0RTT index.
  match write0 c
  //    ClientHello
  //      + KeyShare
  //      + EarlyDataIndication  -------->
  with
  | SendError   -> failwith "dunno"
  | ZeroRTT id0 -> 
  let f0 = DataStream.plain id0 rg0 request in
  match write c f0
  //   (Certificate*)
  //   (CertificateVerify*)
  //   (Finished)
  //   (Application Data*)       -------->
  with
  | SendError -> failwith "dunno"
  | Sent ->
  match read c
  //   (end_of_early_data)       -------->
  //                                                  ServerHello
  //                                        + EarlyDataIndication*
  //                                                   + KeyShare
  //                                         {EncryptedExtensions}
  //                                         {CertificateRequest*}
  //                                        {ServerConfiguration*}
  //                                                {Certificate*}
  //                                          {CertificateVerify*}
  //                             <--------              {Finished}
  with
  | ReadError | Read (Alert _) -> failwith "give up"
  | ZeroRTTmiss -> failwith "give up (lazy)"
  | CertQuery _ -> // what checks should I do?
  match read c
  //   {Certificate*}
  //   {CertificateVerify*}
  //   {Finished}                -------->
  with
  | ReadError | Read (Alert _) -> failwith "give up"
  | Complete id1 -> // what checks should I do?
  match read c
  //                             <--------      [Application Data]
  with
  | Read (Data response) -> response  // by typing, response is indexed by id1
  | _ -> failwith "dunno"
  //  ...

  
(* let server_0RTT tcp config_0RTT =  *)
(*   let c = accept tcp cfg0 in  *)
(*   let query, id1 = // two branches, depending on 0RTT succeeding or not *)
(*     match read c with  *)
(*     | ZeroData (| _, request |) -> parse request, id1 *)
(*       match read c with *)
(*       | Complete id1 -> request, id1 *)
(*       | _ -> failwith "dunno" *)
(*     | Complete id1 ->  *)
(*       // for the time being, we do not signal 0RTT loss; *)
(*       // this information is available somewhere in id1 *)
(*       match read c with  *)
(*       | ZeroData (| _, request |) -> parse request, id1 *)
(*       | _ -> failwith "dunno"  *)
(*     | _ -> failwith "dunno" in *)

(*   // assert("this is a genuine query from id0 and id1's signer") *)
(*   let response = ...(query) in  *)
(*   match write c response with  *)
(*   | Written -> close c *)
(*   | _ -> failwith "dunno"  *)


    
