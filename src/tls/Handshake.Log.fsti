module Handshake.Log

// NB still missing regions and modifies clauses.

open Platform.Bytes
open FStar.Ghost // after HH so as not to shadow reveal :( 

open Hashing
open Hashing.CRF // now using incremental, collision-resistant, agile Hashing.

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

type msg = HandshakeMessages.hs_msg 

val format: msg -> Tot bytes 
val parse_msg: b:bytes -> Tot (option (m:msg {b = format m}))

// No support for binders yet

// Do we compute a hash of the transcript ending with this message?
// in doubt, we hash! 
// val tagged: msg -> Tot bool 
let tagged = 
  let open HandshakeMessages in function 
  | Certificate _ -> true // for CertVerify payload in TLS 1.3
  | CertificateVerify _ -> // for ServerFinish payload in TLS 1.3
  | Finished _ -> // for 2nd Finished 
  | ClientHello _ 
  | ServerHello _ 
  | EncryptedExtensions _  
  | ClientKeyExchange _ 
  | ServerKeyExchange _
  | ServerHelloDone 
  | CertificateRequest _
  | NextProtocol _
  | HelloRequest  
  | HelloRetryRequest _ 
  | SessionTicket _ -> false 

// Does this message complete the flight? 
// val eoflight: msg -> Tot bool 
let eoflight = 
  let open HandshakeMessages in function
  | ClientKeyExchange _ 
  | ClientHello _ 
  | ServerHello _ 
  | EncryptedExtensions _  
  | ClientKeyExchange _ 
  | ServerKeyExchange _
  | ServerHelloDone 
  | CertificateRequest _
  | Certificate _
  | CertificateVerify _
  | Finished _
  | NextProtocol _
  | HelloRequest  
  | HelloRetryRequest _ 
  | SessionTicket _ -> false 

// NB CCS is not explicitly handled here, but can trigger tagging and end-of-flights. 

(* TODO
- add subregion discipline and the corresponding framing conditions
- make prior ghost
- add record-layer calls, keeping track of bytes buffers and their effective lengths
- support abstract plaintexts and multiple epochs 
*)

let transcript_bytes ms = List.Tot.fold_left (fun a m -> a @| format m) empty_bytes ms
// we will need to prove it is injective, we will rely in turn on concrete msg formats
// should use a named lambda

// formatting of the whole transcript is injective (what about binders?)
val transcript_format_injective: ms0:list msg -> ms1:list msg -> 
  Lemma(Seq.equal (transcript_bytes ms0) (transcript_bytes ms1) ==> ms0 == ms1)

val transcript_bytes_append: ms0: list msg -> ms1: list msg -> 
  Lemma (transcript_bytes (ms0 @ ms1) = transcript_bytes ms0 @| transcript_bytes ms1)

// full specification of the hashed-prefix tags required for a given flight 
// (in relational style to capture computational-hashed)
//val tags: a:alg -> prior: list msg -> ms: list msg -> hs: list (tag a) -> Tot Type0 (decreases ms)
let rec tags (a:alg) (prior: list msg) (ms: list msg) (hs:list (tag a)) : Tot Type0 (decreases ms) = 
  match ms with 
  | [] -> hs == [] 
  | m :: ms -> 
      let prior = prior @ [m] in
      match tagged m, hs with 
      | true, h::hs -> let t = transcript_bytes prior in (hashed a t /\ h == hash a t /\ tags a prior ms hs)
      | false, hs -> tags a prior ms hs
      | _ -> False 

val tags_append: a:alg -> prior: list msg -> ms0: list msg -> ms1: list msg -> hs0: list (tag a) -> hs1: list (tag a) ->
  Lemma (tags a prior ms0 hs0 /\ tags a (prior @ ms0) ms1 hs1 ==> tags a prior (ms0 @ ms1) (hs0 @ hs1))


(* STATE *)

type t (r:HH.rid) (a:alg) 
//17-03-25 assume new warning?

//  specification-level transcript of all handshake messages logged so far
val transcriptT: h:HS.mem -> #region:HH.rid -> #a:alg -> t region a -> GTot (list msg) 

// specification-level guard for sending: we have not started receiving the next flight
val writing: h:HS.mem -> #region:HH.rid -> #a:alg -> t region a -> GTot bool 

val create: region:HH.rid -> a:alg -> ST (t region a) 
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> // "allocated in r" /\ writing h1 r /\ 
    writing h1 r /\  
    transcriptT h1 r == []))
  
// We send one message at a time (or in two steps for CH); 
// for call-site simplicity we distinguish between tagged and untagged messages
// We require ms_0 be empty; otherwise the hash computation is messed up

// We do not enforce "tagged m", a local decision 

val send: #region:HH.rid -> #a:alg -> r:t region a -> m:msg (*{~(tagged m)}*) -> ST unit 
  (requires (fun h0 -> writing h0 r )) 
  (ensures (fun h0 _ h1 -> 
    writing h1 r /\
    transcriptT h1 r == transcriptT h0 r @ [m]  ))

val send_tag: #region:HH.rid -> #a:alg -> r:t region a -> m:msg (*{tagged m}*) -> ST (tag a)
  (requires (fun h0 -> writing h0 r )) 
  (ensures (fun h0 h h1 -> 
    let t_0 = transcriptT h0 r in 
    let t_1 = transcriptT h1 r in 
    let bs = transcript_bytes t_1 in
    writing h1 r /\
    t_1 == t_0 @ [m] /\
    hashed a bs /\ h == hash a bs ))

// We receive messages in whole flights; 
// note that, untill a full flight is received, we lose "writing h1 r"
val receive: #region:HH.rid -> #a:alg -> r:t region a -> bytes -> ST (option (list msg * list (tag a)))
  (requires (fun h0 -> True))
  (ensures (fun h0 o h1 -> 
    let t0 = transcriptT h0 r in
    let t1 = transcriptT h1 r in
    match o with 
    | Some (ms, hs) -> t1 == t0 @ ms /\ tags a t0 ms hs /\ writing h1 r
    | None -> t1 == t0 ))

// We receive CCS as external end-of-flight signals;
// we return the messages processed so far, and their final tag; 
// we still can't write.
// This should *fail* if there are pending input bytes. 
val receiveCCS: #region:HH.rid -> #a:alg -> r:t region a -> ST (list msg * list (tag a) * tag a)
  (requires (fun h0 -> True))
  (ensures (fun h0 (ms,hs,h) h1 -> 
    let t0 = transcriptT h0 r in
    let t1 = transcriptT h1 r in
    let tr = transcript_bytes t1 in 
    t1 == t0 @ ms /\ tags a t0 ms hs /\ hashed a tr /\ h = hash a tr ))
