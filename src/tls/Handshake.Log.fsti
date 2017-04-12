module Handshake.Log

// NB still missing regions and modifies clauses.

open Platform.Bytes
open FStar.Ghost // after HH so as not to shadow reveal :( 

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open Hashing
open Hashing.CRF // now using incremental, collision-resistant, agile Hashing.
open TLSConstants
open HandshakeMessages
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

type msg = HandshakeMessages.hs_msg 

// Does this message complete the flight? 
let eoflight = 
  let open HandshakeMessages in function
  | ClientHello _
  | HelloRetryRequest _
  | ServerHello _
  | ServerHelloDone 
  | Finished _ -> true
  | _ -> false

// No support for binders yet

// Do we compute a hash of the transcript ending with this message?
// in doubt, we hash! 
//val tagged: msg -> Tot bool
let tagged m =
  match m with
  | ClientHello _ -> true
  | ServerHello _ -> true
  | Certificate _ -> true // for CertVerify payload in TLS 1.3
  | CertificateVerify _ -> true // for ServerFinish payload in TLS 1.3
  | ClientKeyExchange _ -> true
  | Finished _ -> true // for 2nd Finished
  | _ -> false
// NB CCS is not explicitly handled here, but can trigger tagging and end-of-flights. 

(* TODO
- add subregion discipline and the corresponding framing conditions
- make prior ghost
- add record-layer calls, keeping track of bytes buffers and their effective lengths
- support abstract plaintexts and multiple epochs 
*)

val valid_transcript: list msg -> Tot bool
let hs_transcript: Type0 = l:list msg{valid_transcript l}
let empty_transcript: hs_transcript = []
let extend_transcript (l:hs_transcript) (m:msg): Tot hs_transcript = l @ [m]
let append_transcript (l:hs_transcript) (m:list msg): Tot hs_transcript = l @ m
val transcript_bytes: hs_transcript -> GTot bytes


// formatting of the whole transcript is injective (what about binders?)
val transcript_format_injective: ms0:hs_transcript -> ms1:hs_transcript -> 
  Lemma(Seq.equal (transcript_bytes ms0) (transcript_bytes ms1) ==> ms0 == ms1)

//val transcript_bytes_append: ms0: hs_transcript -> ms1: list msg -> 
//  Lemma (transcript_bytes (ms0 @ ms1) = transcript_bytes ms0 @| transcript_bytes ms1)

let narrowTag a (b:anyTag { length b = tagLen a}) : tag a = b
let tagLength (b:anyTag) = length b

// full specification of the hashed-prefix tags required for a given flight
// (in relational style to capture computational-hashed)
//val tags: a:alg -> prior: list msg -> ms: list msg -> hs: list anyTag(tag a) -> Tot Type0 (decreases ms)
let rec tags (a:alg) (prior: hs_transcript) (ms: list msg) (hs:list anyTag) : Tot Type0 (decreases ms) =
  match ms with
  | [] -> hs == []
  | m :: ms ->
      let prior = extend_transcript prior m in
      match tagged m, hs with 
      | true, h::hs -> 
          let t = transcript_bytes prior in 
          (  tagLength h = tagLen a /\ 
             (  let h = narrowTag a h in 
                hashed a t /\ h == hash a t /\
                tags a prior ms hs ))
      | false, hs -> tags a prior ms hs
      | _ -> False

val tags_append: a:alg -> prior: hs_transcript -> ms0: list msg -> ms1: list msg -> hs0: list anyTag -> hs1: list anyTag ->
  Lemma (tags a prior ms0 hs0 /\ tags a (append_transcript prior ms0) ms1 hs1 ==> tags a prior (ms0 @ ms1) (hs0 @ hs1))

(* STATE *)

val log: Type0
type t = log

val get_reference: log -> GTot HS.some_ref
val init: h:HS.mem -> log -> option protocolVersion -> GTot bool
val writing: h:HS.mem -> log -> GTot bool 
val hashAlg: h:HS.mem -> log -> GTot (option Hashing.alg)
val transcript: h:HS.mem -> log -> GTot (list hs_msg)
val create: #reg:HH.rid -> pv:option protocolVersion -> ST log
  (requires (fun h -> True))
  (ensures (fun h0 out h1 ->
    modifies (Set.singleton reg) h0 h1 /\
    List.Tot.length (transcript h1 out) == 0 /\
    writing h1 out /\
    init h1 out pv))
val setParams: s:log -> 
  TLSConstants.protocolVersion -> 
  a: Hashing.alg -> 
  option TLSConstants.kexAlg -> 
  option CommonDH.group -> ST unit
  (requires (fun h0 -> None? (hashAlg h0 s)))
  (ensures (fun h0 _ h1 ->
    HS.(mods [get_reference s] h0 h1) /\
    transcript h1 s == transcript h0 s /\
    writing h1 s == writing h0 s /\
    hashAlg h1 s == Some a ))


(* Outgoing *) 

// We send one message at a time (or in two steps for CH); 
// for call-site simplicity we distinguish between tagged and untagged messages
// We require ms_0 be empty; otherwise the hash computation is messed up

// We do not enforce "tagged m", a local decision 

let write_transcript h0 h1 (s:log) (m:msg) = 
    HS.(mods [get_reference s] h0 h1) /\
    writing h1 s /\
    hashAlg h1 s == hashAlg h0 s /\
    transcript h1 s == transcript h0 s @ [m] 


val send: s:log -> m:msg -> ST unit 
  (requires (fun h0 -> writing h0 s)) 
  (ensures (fun h0 _ h1 -> write_transcript h0 h1 s m))

val send_tag: #a:alg -> s:log -> m:msg -> ST (tag a)
  (requires (fun h0 -> 
    writing h0 s /\
    hashAlg h0 s = Some a )) 
  (ensures (fun h0 h h1 -> 
    let t = transcript h1 s in
    let bs = transcript_bytes t  in
    write_transcript h0 h1 s m /\ 
    hashed a bs /\ h == hash a bs ))

// An ad hoc variant for caching a message to be sent immediately after the CCS
// We always increment the writer, sometimes report handshake completion.
// This variant also sets flags and 'drops' the writing state
val send_CCS_tag: #a:alg -> s:log -> m:msg -> complete:bool -> ST (tag a)
  (requires (fun h0 -> 
    writing h0 s /\
    hashAlg h0 s = Some a )) 
  (ensures (fun h0 h h1 -> 
    let bs = transcript_bytes (transcript h1 s)  in
    hashAlg h0 s = hashAlg h1 s /\    
    write_transcript h0 h1 s m /\ 
    hashed a bs /\ h == hash a bs ))

// Setting signals 'drops' the writing state, to prevent further writings until the signals have been transmitted
val send_signals: s:log -> outgoing_next_keys:bool -> outgoing_complete:bool -> ST unit
  (requires fun h0 -> 
    writing h0 s /\
    outgoing_next_keys \/ outgoing_complete)
  (ensures fun h0 _ h1 -> 
    hashAlg h0 s = hashAlg h1 s /\
    transcript h0 s = transcript h1 s)

// FRAGMENT INTERFACE 
//
// for outgoing messages, Handshake.Log maintains 
// - an output buffer (bytes) for handshake messages
// - the three flags below, to be echoed and cleared once the buffer is empty

type id = TLSInfo.id 
open Range // for now

// payload of a handshake fragment, to be made opaque eventually
type fragment (i:id) = ( rg: frange i & rbytes rg )
//let out_msg i rg b : msg i = (|rg, b|)

// What the HS asks the record layer to do, in that order.
type outgoing (i:id) (* initial index *) =
  | Outgoing:
      send_first: option (fragment i) -> // HS fragment to be sent;  (with current id)
      send_ccs  : bool               -> // CCS fragment to be sent; (with current id)
      next_keys : bool               -> // the writer index increases;
      complete  : bool               -> // the handshake is complete!
      outgoing i


//17-03-26 now return an outgoing result, for uniformity
// | OutError: error -> outgoing i       // usage? send a polite Alert in case something goes wrong when preparing messages

//17-03-29  these cause a mysterious error
//let out_next_keys (#i:id) (r:outgoing i) = Outgoing? r /\ Outgoing?.next_keys r
//let out_complete (#i:id) (r:outgoing i)  = Outgoing? r /\ Outgoing?.complete r

// provides outputs to the record layer, one fragment at a time
// never fails, in contrast with Handshake.next_fragment
val next_fragment: log -> i:id -> St (outgoing i) 
(* Incoming *) 

// We receive messages in whole flights; 
// note that, untill a full flight is received, we lose "writing h1 r"
val receive: s:log -> bytes -> ST (option (list msg * list anyTag))
  (requires (fun h0 -> True))
  (ensures (fun h0 o h1 -> 
    let oa = hashAlg h1 s in 
    let t0 = transcript h0 s in
    let t1 = transcript h1 s in
    oa == hashAlg h0 s /\
    HS.(mods [get_reference s] h0 h1) /\ (
    match o with 
    | Some (ms, hs) -> 
        t1 == t0 @ ms /\ 
        writing h1 s /\
        (match oa with Some a -> tags a t0 ms hs | None -> hs == []) 
    | None -> t1 == t0 )))

// We receive CCS as external end-of-flight signals;
// we return the messages processed so far, and their final tag; 
// we still can't write.
// This should *fail* if there are pending input bytes. 
val receive_CCS: s:log -> ST (option (list msg * list anyTag))
  (requires (fun h0 -> True))
  (ensures (fun h0 res h1 -> 
    match res with 
    | Some (ml,tl) ->  
       let t0 = transcript h0 s in
       let t1 = transcript h1 s in
       let tr = transcript_bytes t1 in 
       let a = hashAlg h1 s in
       Some?a /\ t1 == t0 @ ml /\ tags (Some?.v a) t0 ml tl))

