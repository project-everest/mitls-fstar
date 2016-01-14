module TLSOutline

// Draft TLS API using hyperheaps in F*
// incorporating definitions and comments from TLS.fs7 and TLS.fsi
// - each connection runs through a sequence of epochs
// - each epoch has two streams of application data
// - each secure stream maintains a log of data (and warnings) written so far
//   and the reader position in that log.

open Heap
open FStar.HyperHeap
open Seq
open SeqProperties // for e.g. found

open Platform.Bytes
open Platform.Error
open Platform.Tcp

open TLSError
open TLSInfo

type hh = HyperHeap.t

// using DataStream 
assume val tls_region    : r:rid{r<>root /\ parent r = root}
assume val epochs_region : r:rid{r<>root /\ parent r = root /\ r <> tls_region}
type e_rid = r:rid{r<>root /\ parent r = epochs_region}

// epochs are partnered statically (ie, their partner is known at the time of creation)
assume type epoch
assume val epoch_region:      epoch -> Tot rid
assume val epoch_peer_region: epoch -> Tot rid
assume val epochId:  e:epoch -> Tot id  // globally unique; should reveal some handshake info too
assume val writtenT: e:epoch -> hh -> Tot (Seq.seq (DataStream.delta (epochId e))) //TODO: it is well-formed (note reconcile list vs seq)
assume val readseqT: epoch -> hh -> Tot nat

//Do we need such a function? Perhaps a stateful one to record paired epochs
// assume val partner: epoch -> HyperHeap.t -> Tot epoch

// connections may be partnered dynamically (ie, they are partnered by the assignment of partnered epochs to connections)
assume type connection
assume type cid
assume type c_inv  :  connection -> hh -> Type          //the private connection invariant
assume val c_id:      connection -> Tot cid            //a unique identifier for the connection, typically derived from a nonce
assume val c_region:  connection -> Tot rid            //the region in which the connection is allocated
assume val c_role:    connection -> Tot role                  //Server or Client
assume val c_regionsT:connection -> hh -> Tot (Set.set rid)    //the dynamic set of regions of connection and the connection's current epochs
assume val readableT: connection -> hh -> Tot bool // indicates whether read is callable (for any purpose)
assume val writableT: connection -> hh -> Tot bool // indicates whether write is callable (for sending appdata/closing)
assume val epochsT:   connection -> hh -> Tot (Seq.seq epoch)  //the current sequence of epochs associated to a connection

open FStar.Monotonic.RRef
open FStar.Ghost

//an abstract update condition on the connection log
type c_log_extension (#a:Type) (s0:erased (Seq.seq a)) (s1:erased (Seq.seq a)) : Type
(* Internally, we want this to include, at least:
   1. seq extension: exists sfx. Seq.append (reveal s0) sfx = reveal s1
   2. stable assignment of epochs to connections
   3. ... ?
*)

//a log of all (erased) connections created so far, monotonically growing
assume val connection_log : m_rref tls_region (erased (Seq.seq connection)) c_log_extension
assume type c_log_inv : hh -> Type
let is_conn (c:connection) (h:hh) = SeqProperties.mem c (reveal (sel h connection_log))
//A conn is a connection known to be in the connection log
type conn = c:connection{witnessed (fun h -> b2t (is_conn c h))}

(*** SEPARATION INVARIANTS ***)
assume val epoch_region_peer: e:epoch -> Lemma
  (ensures (epoch_region e <> root
	    /\ epoch_peer_region e <> root
	    /\ parent (epoch_region e) = epochs_region
	    /\ parent (epoch_peer_region e) = epochs_region
	    /\ disjoint (epoch_region e) (epoch_peer_region e)))

assume val c_regions_includes_c_region: c:connection -> h:hh -> Lemma
  (Set.mem (c_region c) (c_regionsT c h))

assume val c_log_inv_separation: c1:connection -> c2:connection{c_id c1 <> c_id c2} -> h:hh -> Lemma
  (requires (c_log_inv h /\ is_conn c1 h /\ is_conn c2 h))
  (ensures (disjoint_regions (c_regionsT c1 h) (c_regionsT c2 h)))

(*** PARTNERING INVARIANTS ***)
(* epoch partnering is a static property *)
assume type partnered_epochs: epoch -> epoch -> Type
assume val epoch_of: connection -> hh -> Tot epoch                   //the current epoch of a connection
assume val epoch_assigned_to: epoch -> hh -> Tot (option connection) //the stable assignment of an epoch to a connection
assume val current_epoch: c:conn -> ST (option epoch)
  (requires c_log_inv)
  (ensures (fun h0 e h1 -> 
    h0=h1 /\
    (is_Some e ==> (let epoch = Some.v e in
		   epoch = epoch_of c h0
		   /\ witnessed (fun h -> epoch_assigned_to epoch h == Some c)))))

(* connection partnering is state dependent ... *)
assume type partnered_conn : connection -> connection -> hh -> Type
(* ... and is defined by the current assignment of epochs to connections *)
assume val lemma_conn_partnering: c1:connection -> c2:connection -> h:hh -> Lemma 
  (requires (c_log_inv h /\ is_conn c1 h /\ is_conn c2 h))
  (ensures (partnered_conn c1 c2 h <==> partnered_epochs (epoch_of c1 h) (epoch_of c2 h)))
  
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
assume val partnered_conn_inv: c1:connection -> c2:connection -> h:hh -> Lemma
  (requires (partnered_conn c1 c2 h))
  (ensures (readseqT (epoch_of c1 h) h <= Seq.length (writtenT (epoch_of c2 h) h)    //the current reader is behind the writer
	   /\ readseqT (epoch_of c2 h) h <= Seq.length (writtenT (epoch_of c1 h) h)   //on both sides
	   /\ (forall e1 e2. e1 <> epoch_of c1 h                         //and for any old partnered epochs (can we get this?)
		       /\ epoch_assigned_to e1 h = Some c1
		       /\ e2 <> epoch_of c2 h 
		       /\ epoch_assigned_to e2 h = Some c2
		       /\ partnered_epochs e1 e2
		       ==> (readseqT e1 h = Seq.length (writtenT e2 h)           //everything that was sent was read
  		         /\ readseqT e2 h = Seq.length (writtenT e1 h)))))       //on both sides


(* // all the calls below are ghost & read-only; they depend only on c's region,  *)
(* // and their result are determined by the sequence of calls (arguments, results, and postconditions) *)
(* // consider using a log of epoch views instead of epochs *)
(* // fix r/w dual indexing! *)

(* // by design, the current values of writerId c and readerId c *)
(* // are determined by the call sequence --- no need to call them. *)

(* // *all* stateful connection calls are specializations of: *)

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


(* //------------------------- control API ---------------------------- *)

(* let initial:  -> cn: connection -> h:heap -> Tot bool = *)
(*     extends (c_region cn) root /\ // we allocate a fresh, opaque region for the connection *)
(*     c_role cn   = role /\ *)
(*     c_tcp cn    = ns /\ *)
(*     c_resume cn = resume /\ *)
(*     c_config cn = c /\ *)
(*     sel h (c_epoch cn) = Init // assuming Init epoch implicitly have no data sent/received *)

(* //* should we still return ConnectionInfo ? *)
(* //* merging connect and resume with an optional sessionID *)
(* val connect: ns:Tcp.networkStream -> c:config -> resume: option sessionID -> ST connection *)
(*   (requires (fun h0 -> True)) *)
(*   (ensures (fun h0 cn h1 -> *)
(*     modifies Set.empty h0 h1 /\ *)
(*     initial Client ns c resume cn h1 *)
(*     //TODO: even if the server declines, we authenticate the client's intent to resume from this sid. *)
(*   )) *)

(* //* do we need both? *)
(* val accept: Tcp.TcpListener -> c:config -> ST connection *)
(*   (requires (fun h0 -> True)) *)
(*   (ensures (fun h0 cn h1 -> *)
(*     modifies Set.empty h0 h1 /\ *)
(*     exists ns. initial Server ns c None cn h1 *)
(*   )) *)
(* val accept_connected: ns:Tcp.NetworkStream -> c:config -> ST connection *)
(*   (requires (fun h0 -> True)) *)
(*   (ensures (fun h0 cn h1 -> *)
(*     modifies Set.empty h0 h1 /\ *)
(*     initial Server ns c None cn h1 *)
(*   )) *)

(* // the client can ask for rekeying --- no immediate effect *)
(* val rekey: cn:connection { c_role cn = Client } -> ST unit *)
(*   (requires (fun h0 -> True)) *)
(*   (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 // no visible change in cn *)
(*   )) *)

(* val rehandshake: cn:connection { c_role cn = Client } -> c:config -> ST unit *)
(*   (requires (fun h0 -> True)) *)
(*   (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 // no visible change in cn *)
(*   )) *)

(* val request: cn:connection { c_role cn = Server } -> c:config -> ST unit *)
(*   (requires (fun h0 -> True)) *)
(*   (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 // no visible change in cn *)
(*   )) *)

(* //--------------------------writing----------------------------- *)

(* // assuming writer_log is the high-level projection of the log  *)

(* type ioresult_w =  *)
(*     | Written   // Application data was written, and the connection remains writable in the same epoch *)
(*     | WriteError of al:alertDescription -> s:string -> ioresult_w // The connection is down, possibly after sending an alert *)

(* type modifies_c c h0 h1 =  *)
(*   modifies (regions_of c h1) h0 h1 /\ *)
(*   let epochs0 = epochsT c h0 in  *)
(*   let epochs1 = epochsT c h1 in  *)
(*   Seq.prefix epochs0 epochs1 /\ *)
(*   forall e: nat { e < Seq.length epochs - 1 }.  *)
(*     writtenT (Seq.index epochs0 i) = writtenT (Seq.index epochs1 i) /\ *)
(*     readseqT (Seq.index epochs0 i) = readseqT (Seq.index epochs1 i)  *)
(* // this predicate is meant to be transitive *)

(* let currentId epochs = epochId (Seq.last epochs) *)

(* (\* we could use a record to avoid multiple sels  *)
(* type sT = State: *)
(*     epochs: Seq epoch ->  *)
(*     readable: bool ->  *)
(*     writable: bool -> *)
(*     readseq: nat  *)
(*     written: Seq DataStream.fragment (currentId epochs) -> sT *)
(* *\) *)

(* val write: c:conn -> i:id -> rg:frange i -> data: DataStream.fragment i rg -> ST ioresult_w *)
(*   (requires (fun h0 ->  *)
(*     connection_log_inv h0 /\ *)
(*     writableT c h0 /\  // implying epochsT c h0 is not empty *)
(*     i = currentId (epochsT c h0))) *)
(*   (ensures (fun h0 r h1 ->  *)
(*     connection_log_inv h1 /\ *)
(*     modifies_c c h0 h1 /\ // should also guarantee that we modify at most the current epoch and append to the log *)
(*     epochsT c h1   = epochsT c h0 /\  *)
(*     let current = Seq.last (epochsT c h0) in  *)
(*     let log0 = writtenT current h0 in  *)
(*     let log1 = writtenT current h1 in  *)
(*     (r = Written ==> ( *)
(*       log1 = snoc log0 (DataStream.Data data) /\   // should it be conditioned on authId? *)
(*       readableT c h1 = readableT c h0 /\ readseqT c h1 = readseqT c h0 /\ *)
(*       writableT c h1 = writableT c h0  )) *)
(*     /\  *)
(*     (is_WriteError r ==> ( *)
(*       log1 = match r.al with | None -> log0 *)
(*                              | Some -> snoc log0 (DataStream.Alert (WriteError.al.value r)) /\ *)
(*       ~(readableT c h1) /\ readseqT c h1 = readseqT c h0 /\  *)
(*       writableT c h1 = None *)
(*     )) *)
(*   )) *)

(* // hopefully mustRead is gone.  *)
(* //  | MustRead  // Nothing written, as the connection is busy completing a handshake *)

(* //------------------------- reading ---------------------------- *)


(* type ioresult_r (i:id) = // the caller's read id *)
(*     | Read of DataStream.delta e *)
(*         // this delta has been added to the input stream; we may have read *)
(*         // - an application-data fragment or a warning (leaving the connection live) *)
(*         // - a closure or a fatal alert (tearing down the connection) *)
(*         // If the alert is a warning, the connection remains live. *)
(*         // If the alert is final, the connection has been closed by our peer; *)
(*         // the application may reuse the underlying TCP stream *)
(*         // only after normal closure (a = AD_close_notify) *)

(*     | ReadError of option alertDescription * string *)
(*         // We encountered an error while reading, so the connection dies. *)
(*         // we return the fatal alert we may have sent, if any, *)
(*         // or None in case of an internal error. *)
(*         // The connection is gone; its state is undefined. *)

(*     | CertQuery of query * bool *)
(*         // We received the peer certificates for the next epoch, to be authorized before proceeding. *)
(*         // the bool is what the Windows certificate store said about this certificate. *)

(*     | Complete  *)
(*         // Now readable and writable in a fresh epoch at the end of the log *)

(*     | DontWrite *)
(*         // Nothing read yet, and now unwriteable until completion of ongoing handshake *)

(* // NB the log can silently extend to new epochs (with empty log projections) *)
(* // NB we never expose reader/writer at different epochs.  *)


(* val read: c:connection -> i:id -> ST(ioresult_r)              // unclear whether we should pass i in. *)
(*   (requires (fun h0 -> inv c h0 /\ readerIdT c h0 = Some i /\  *)
(*   (ensures (fun h0 r h1 ->  *)
(*     inv c h1 /\  *)
(*     modifies (c_region c) h0 h1 /\    *)
(*     (r = Read d ==> ... /\ ) /\ *)
(*      )) *)


(* // ------------------- typical call sequence ------------------------- *)

(* // for simplicity, we assume both requests and responses fit in a single fragment. *)

(* let client_0RTT tcp config_0RTT request =  *)
(*   let c = connect tcp config_0RTT None in  *)
(*   // nothing sent yet, except possibly for TCP *)
(*   // we write in cleartext until we have the 0RTT index. *)
(*   match write0 c  *)
(*   //    ClientHello *)
(*   //      + KeyShare *)
(*   //      + EarlyDataIndication  --------> *)
(*   with  *)
(*   | SendError   -> failwith "dunno"  *)
(*   | ZeroRTT id0 -> id0  *)
(*   let f0 = DataStream.plain id0 rg0 request in  *)
(*   match write c f0  *)
(*   //   (Certificate*\) *)
(*   //   (CertificateVerify*\) *)
(*   //   (Finished) *)
(*   //   (Application Data*\)       --------> *)
(*   with  *)
(*   | SendError -> failwith "dunno"  *)
(*   | Sent ->  *)
(*   match read c *)
(*   //   (end_of_early_data)       --------> *)
(*   //                                                  ServerHello *)
(*   //                                        + EarlyDataIndication*    *)
(*   //                                                   + KeyShare *)
(*   //                                         {EncryptedExtensions} *)
(*   //                                         {CertificateRequest*} *)
(*   //                                        {ServerConfiguration*} *)
(*   //                                                {Certificate*} *)
(*   //                                          {CertificateVerify*} *)
(*   //                             <--------              {Finished} *)
(*   with  *)
(*   | ReadError | Read (Alert _) -> failwith "give up"  *)
(*   | ZeroRTTmiss -> failwith "give up (lazy)" *)
(*   | CertQuery _ -> // what checks should I do?  *)
(*   match read c  *)
(*   //   {Certificate*} *)
(*   //   {CertificateVerify*} *)
(*   //   {Finished}                --------> *)
(*   with  *)
(*   | ReadError | Read (Alert _) -> failwith "give up" *)
(*   | Complete id1 -> // what checks should I do? *)
(*   match read c   *)
(*   //                             <--------      [Application Data] *)
(*   with  *)
(*   | Read (Data response) -> response  // by typing, response is indexed by id1 *)
(*   | _ -> failwith "dunno" *)
(*   ... *)

  
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






(* init requires an assume to handle top-level effects *)
assume val init : unit -> ST unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> c_log_inv h1
                        /\ fresh_region tls_region h0 h1
			/\ fresh_region epochs_region h0 h1))
    
