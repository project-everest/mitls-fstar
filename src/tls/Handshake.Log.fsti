module Handshake.Log
 
// NB still missing regions and modifies clauses.
 
open Platform.Bytes
open FStar.Ghost // after HH so as not to shadow reveal :( 

open FStar.Heap
open Hashing.CRF
open HandshakeMessages // for pattern matching on messages
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

open Platform.Error
open TLSError

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

let valid_transcript hsl =
    match hsl with
    | [] -> true
    | [ClientHello ch] -> true
    | (ClientHello ch) :: (ServerHello sh) :: rest -> true
    | _ -> false

let hs_transcript: Type0 = l:list msg{valid_transcript l}

let append_transcript (l:hs_transcript) (m:list msg {valid_transcript (l @ m)}): Tot hs_transcript = l @ m

val transcript_bytes: list msg -> GTot bytes
 
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
let rec tags (a:alg) (prior: list msg) (ms: list msg) (hs:list anyTag) : Tot Type0 (decreases ms) =
  match ms with
  | [] -> hs == []
  | m :: ms ->
      let prior = prior@[m] in
      match tagged m, hs with 
      | true, h::hs -> 
          let t = transcript_bytes prior in 
          (  tagLength h = tagLen a /\ 
             (  let h = narrowTag a h in 
                hashed a t /\ h == hash a t /\
                tags a prior ms hs ))
      | false, hs -> tags a prior ms hs
      | _ -> False

val tags_append: a:alg -> prior: list msg -> ms0: list msg -> ms1: list msg -> hs0: list anyTag -> hs1: list anyTag -> Lemma (tags a prior ms0 hs0 /\ tags a (prior@ms0) ms1 hs1 ==> tags a prior (ms0 @ ms1) (hs0 @ hs1))

(* STATE *)

val log: Type0
type t = log

val get_reference: log -> GTot HS.some_ref
let region_of s = 
  let open FStar.HyperStack in 
  let Ref r = get_reference s in 
  r.id

// not needed.

// the Handshake can write
val writing: h:HS.mem -> log -> GTot bool 

// the assigned hash algorithm, if any
val hashAlg: h:HS.mem -> log -> GTot (option Hashing.alg)

// the transcript of past messages, in both directions
val transcript: h:HS.mem -> log -> GTot (list hs_msg)

//17-04-12 for now always called with pv = None.
val create: reg:HH.rid -> pv:option TLSConstants.protocolVersion -> ST log
  (requires (fun h -> True))
  (ensures (fun h0 out h1 ->
    HS.modifies (Set.singleton reg) h0 h1 /\ // todo: we just allocate (ref_of out)
    transcript h1 out == [] /\
    writing h1 out /\
    hashAlg h1 out == None ))

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

// shared postcondition
let write_transcript h0 h1 (s:log) (m:msg) = 
    HS.(mods [get_reference s] h0 h1) /\
    writing h1 s /\
    hashAlg h1 s == hashAlg h0 s /\
    transcript h1 s == transcript h0 s @ [m] 

val send: s:log -> m:msg -> ST unit 
  (requires (fun h0 -> 
    writing h0 s /\
    valid_transcript (transcript h0 s @ [m]))) 
  (ensures (fun h0 _ h1 -> write_transcript h0 h1 s m))

val hash_tag: #a:alg -> s:log -> ST (tag a)
  (requires (fun h0 -> 
    hashAlg h0 s = Some a )) 
  (ensures (fun h0 h h1 -> 
    let bs = transcript_bytes (transcript h1 s)  in
    hashed a bs /\ h == hash a bs ))

val send_tag: #a:alg -> s:log -> m:msg -> ST (tag a)
  (requires (fun h0 -> 
    writing h0 s /\
    valid_transcript (transcript h0 s @ [m]) /\
    hashAlg h0 s = Some a )) 
  (ensures (fun h0 h h1 -> 
    let bs = transcript_bytes (transcript h1 s)  in
    write_transcript h0 h1 s m /\ 
    hashed a bs /\ h == hash a bs ))

// An ad hoc variant for caching a message to be sent immediately after the CCS
// We always increment the writer, sometimes report handshake completion.
// This variant also sets flags and 'drops' the writing state
val send_CCS_tag: #a:alg -> s:log -> m:msg -> complete:bool -> ST (tag a)
  (requires (fun h0 -> 
    writing h0 s /\
    valid_transcript (transcript h0 s @ [m]) /\
    hashAlg h0 s = Some a )) 
  (ensures (fun h0 h h1 -> 
    let bs = transcript_bytes (transcript h1 s)  in
    write_transcript h0 h1 s m /\ 
    hashed a bs /\ h == hash a bs ))

// Setting signals 'drops' the writing state, to prevent further writings until the signals have been transmitted
val send_signals: s:log -> outgoing_next_keys:bool -> outgoing_complete:bool -> ST unit
  (requires fun h0 -> 
    writing h0 s /\
    (outgoing_next_keys \/ outgoing_complete))
  (ensures fun h0 _ h1 -> 
    HS.(mods [get_reference s] h0 h1) /\
    hashAlg h0 s == hashAlg h1 s /\
    transcript h0 s == transcript h1 s)


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
// the spec should say the "high-level" view does not change


(* Incoming *) 

// We receive messages & hashes in whole flights; 
// Untill a full flight is received, we lose "writing h1 r"
val receive: s:log -> bytes -> ST (result (option (list msg * list anyTag)))
//TODO return instead ST (result (list msg * list anyTag))
  (requires (fun h0 -> True))
  (ensures (fun h0 o h1 -> 
    let oa = hashAlg h1 s in 
    let t0 = transcript h0 s in
    let t1 = transcript h1 s in
    oa == hashAlg h0 s /\
    HS.(mods [get_reference s] h0 h1) /\ (
    match o with 
    | Error _ -> True // left underspecified
    | Correct None -> 
        t1 == t0 
    | Correct (Some (ms, hs)) -> 
        t1 == t0 @ ms /\ 
        writing h1 s /\
        (match oa with Some a -> tags a t0 ms hs | None -> hs == [])  )))

// We receive CCS as external end-of-flight signals;
// we return the messages & hashes processed so far, and their final tag; 
// we still can't write (we should receive Finished next)
// This should *fail* if there are pending input bytes. 
val receive_CCS: #a:Hashing.alg -> s:log -> ST (result (list msg * list anyTag * anyTag))
  (requires (fun h0 -> hashAlg h0 s == Some a))
  (ensures (fun h0 res h1 -> 
    let oa = hashAlg h1 s in 
    let t0 = transcript h0 s in
    let t1 = transcript h1 s in
    HS.(mods [get_reference s] h0 h1) /\ 
    hashAlg h0 s == hashAlg h1 s /\ (
    match res with 
    | Error _ -> True // left underspecified
    | Correct (ml,tl,h) ->  
       t1 == t0 @ ml /\ tags a t0 ml tl)))

