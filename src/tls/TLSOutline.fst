module TLS

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

// using DataStream
val tls_region    : r:rid{parent r = root}
val epochs_region : r:rid{parent r = root /\ r <> tls_region}

//epochs are partnered statically (ie, their partner is known at the time of creation)
abstract type epoch  = ... // abstract; how to express sharing? using a global table of epochs?

abstract val epochId: epoch -> Tot id  // globally unique; should reveal some handshake info too
let epochId e = e.id

//both of these next two are monotonic
val writtenT: e:epoch -> HyperHeap.t -> Tot (seq (DataStream.delta (epochId e))) //TODO: it is well-formed (note reconcile list vs seq)
val readseqT: e:epoch -> HyperHeap.t -> Tot nat 

//connections may be partnered dynamically (ie, they are partnered by the assignment of partnered epochs to connections)
abstract type connection = ...
type inv: connection -> HyperHeap.t ->  Type // the private connection invariant

val c_region: connection -> regionId // the only region modified by the connection.
val c_role: connection -> role


val connection_log : m_rref (seq connection) (fun s0 s1 -> s1 >= s0)

type conn = c:connection{Witnessed (fun h -> c \in (sel h connection_log)}

//connection_log_inv h = 
//    let cs = sel h connection_log in
//    partnering_inv cs /\ (TBD)
//    forall c1<>c2 \in cs. disjoint (c_region c1) (c_region c2)
//                      /\  disjoint_regions (epoch_regions c1 h) (epoch_regions c2 h)
val connection_log_inv : HyperHeap.t -> Type


//init requires an assume to handle top-level effects
assume val init : unit -> ST unit
    (ensures (fun h0 _ h1 -> connection_log_inv h1
                         /\ fresh_region tls_region h0 h1))
    
  

// all the calls below are ghost & read-only; they depend only on c's region, 
// and their result are determined by the sequence of calls (arguments, results, and postconditions)
// consider using a log of epoch views instead of epochs
// fix r/w dual indexing!

val readableT: connection -> HyperHeap.t -> Tot bool // indicates whether read is callable (for any purpose)
val writableT: connection -> HyperHeap.t -> Tot bool // indicates whether write is callable (for sending appdata/closing)
val epochsT:   connection -> HyperHeap.t -> Tot (seq epoch) // *projected* and *truncated* so that the last entry is always the current epoch.


(* lemma state_inv: forall c h0 h1,  *)
(*   HyperHeap.restrict c.region h0 = HyperHeap.restrict c.region h1 ==> *)
(*   readableT c h0 = readableT c h1 /\ *)
(*   writableT c h0 = writableT c h1 /\ *)
(*   epochsT c h0   = epochsT c h1 /\  *)
(*   Seq.Forall (epochsT c h0) *)
(*     (fun e -> writtenT e h0 = writtenT e h1 /\  *)
(*             readseqT e h0 = readseqT e h1) *)

// by design, the current values of writerId c and readerId c
// are determined by the call sequence --- no need to call them.

// *all* stateful connection calls are specializations of:

val sample: c:conn -> ... -> ST r
  (requires (fun h0 -> connection_log_inv h0))
  (ensures (fun h0 r h1 -> 
    connection_log_inv h1
    /\ regions_of c h0 <= regions_of c h1
    /\ modifies (regions_of c h1) h0 h1 
    /\ "current epoch, readable, writeable, and the log after projection are all determined by the results & posts of prior calls" 
    /\ "current and the log contents after projection are monotonic" /\
    "epochId is the id of an epoch in the log" /\ 
    "the DataStream projection of all fragment logs for all epochs after epochId are empty" /\ 
    "the DataStream projection of all fragment logs for all epochs are monotonic" /\ 

//TODO: unclear how to fold in 0RTT


//------------------------- control API ----------------------------

let initial:  -> cn: connection -> h:heap -> Tot bool =
    extends (c_region cn) root /\ // we allocate a fresh, opaque region for the connection
    c_role cn   = role /\
    c_tcp cn    = ns /\
    c_resume cn = resume /\
    c_config cn = c /\
    sel h (c_epoch cn) = Init // assuming Init epoch implicitly have no data sent/received

//* should we still return ConnectionInfo ?
//* merging connect and resume with an optional sessionID
val connect: ns:Tcp.networkStream -> c:config -> resume: option sessionID -> ST connection
  (requires (fun h0 -> True))
  (ensures (fun h0 cn h1 ->
    modifies Set.empty h0 h1 /\
    initial Client ns c resume cn h1
    //TODO: even if the server declines, we authenticate the client's intent to resume from this sid.
  ))

//* do we need both?
val accept: Tcp.TcpListener -> c:config -> ST connection
  (requires (fun h0 -> True))
  (ensures (fun h0 cn h1 ->
    modifies Set.empty h0 h1 /\
    exists ns. initial Server ns c None cn h1
  ))
val accept_connected: ns:Tcp.NetworkStream -> c:config -> ST connection
  (requires (fun h0 -> True))
  (ensures (fun h0 cn h1 ->
    modifies Set.empty h0 h1 /\
    initial Server ns c None cn h1
  ))

// the client can ask for rekeying --- no immediate effect
val rekey: cn:connection { c_role cn = Client } -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 // no visible change in cn
  ))

val rehandshake: cn:connection { c_role cn = Client } -> c:config -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 // no visible change in cn
  ))

val request: cn:connection { c_role cn = Server } -> c:config -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 // no visible change in cn
  ))

//--------------------------writing-----------------------------

// assuming writer_log is the high-level projection of the log 

type ioresult_w = 
    | Written   // Application data was written, and the connection remains writable in the same epoch
    | WriteError of al:alertDescription -> s:string -> ioresult_w // The connection is down, possibly after sending an alert

type modifies_c c h0 h1 = 
  modifies (regions_of c h1) h0 h1 /\
  let epochs0 = epochsT c h0 in 
  let epochs1 = epochsT c h1 in 
  Seq.prefix epochs0 epochs1 /\
  forall e: nat { e < Seq.length epochs - 1 }. 
    writtenT (Seq.index epochs0 i) = writtenT (Seq.index epochs1 i) /\
    readseqT (Seq.index epochs0 i) = readseqT (Seq.index epochs1 i) 
// this predicate is meant to be transitive

let currentId epochs = epochId (Seq.last epochs)

(* we could use a record to avoid multiple sels 
type sT = State:
    epochs: Seq epoch -> 
    readable: bool -> 
    writable: bool ->
    readseq: nat 
    written: Seq DataStream.fragment (currentId epochs) -> sT
*)

val write: c:conn -> i:id -> rg:frange i -> data: DataStream.fragment i rg -> ST ioresult_w
  (requires (fun h0 -> 
    connection_log_inv h0 /\
    writableT c h0 /\  // implying epochsT c h0 is not empty
    i = currentId (epochsT c h0)))
  (ensures (fun h0 r h1 -> 
    connection_log_inv h1 /\
    modifies_c c h0 h1 /\ // should also guarantee that we modify at most the current epoch and append to the log
    epochsT c h1   = epochsT c h0 /\ 
    let current = Seq.last (epochsT c h0) in 
    let log0 = writtenT current h0 in 
    let log1 = writtenT current h1 in 
    (r = Written ==> (
      log1 = snoc log0 (DataStream.Data data) /\   // should it be conditioned on authId?
      readableT c h1 = readableT c h0 /\ readseqT c h1 = readseqT c h0 /\
      writableT c h1 = writableT c h0  ))
    /\ 
    (is_WriteError r ==> (
      log1 = match r.al with | None -> log0
                             | Some -> snoc log0 (DataStream.Alert (WriteError.al.value r)) /\
      ~(readableT c h1) /\ readseqT c h1 = readseqT c h0 /\ 
      writableT c h1 = None
    ))
  ))

// hopefully mustRead is gone. 
//  | MustRead  // Nothing written, as the connection is busy completing a handshake

//------------------------- reading ----------------------------


type ioresult_r (i:id) = // the caller's read id
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

    | Complete 
        // Now readable and writable in a fresh epoch at the end of the log

    | DontWrite
        // Nothing read yet, and now unwriteable until completion of ongoing handshake

// NB the log can silently extend to new epochs (with empty log projections)
// NB we never expose reader/writer at different epochs. 


val read: c:connection -> i:id -> ST(ioresult_r)              // unclear whether we should pass i in.
  (requires (fun h0 -> inv c h0 /\ readerIdT c h0 = Some i /\ 
  (ensures (fun h0 r h1 -> 
    inv c h1 /\ 
    modifies (c_region c) h0 h1 /\   
    (r = Read d ==> ... /\ ) /\
     ))


// ------------------- typical call sequence -------------------------

// for simplicity, we assume both requests and responses fit in a single fragment.

let client_0RTT tcp config_0RTT request = 
  let c = connect tcp config_0RTT None in 
  // nothing sent yet, except possibly for TCP
  // we write in cleartext until we have the 0RTT index.
  match write0 c 
  //    ClientHello
  //      + KeyShare
  //      + EarlyDataIndication  -------->
  with 
  | SendError   -> failwith "dunno" 
  | ZeroRTT id0 -> id0 
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
  ...

  
let server_0RTT tcp config_0RTT = 
  let c = accept tcp cfg0 in 
  let query, id1 = // two branches, depending on 0RTT succeeding or not
    match read c with 
    | ZeroData (| _, request |) -> parse request, id1
      match read c with
      | Complete id1 -> request, id1
      | _ -> failwith "dunno"
    | Complete id1 -> 
      // for the time being, we do not signal 0RTT loss;
      // this information is available somewhere in id1
      match read c with 
      | ZeroData (| _, request |) -> parse request, id1
      | _ -> failwith "dunno" 
    | _ -> failwith "dunno" in

  // assert("this is a genuine query from id0 and id1's signer")
  let response = ...(query) in 
  match write c response with 
  | Written -> close c
  | _ -> failwith "dunno" 




