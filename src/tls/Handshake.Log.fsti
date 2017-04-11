(*--build-config options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
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

// When receiving, do we automatically compute a hash of the transcript ending with this message?
// in doubt, we hash!
// val tagged: msg -> Tot bool
let tagged =
  let open HandshakeMessages in function
  | Certificate _ -> true // for CertVerify payload in TLS 1.3
  | CertificateVerify _ -> true // for ServerFinish payload in TLS 1.3
  | Finished _ -> true // for 2nd Finished
  | _ -> false
(*
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
*)

// Does this message complete the flight?
// val eoflight: msg -> Tot bool
let eoflight =
  let open HandshakeMessages in function
  | ClientHello _
  | HelloRetryRequest _
  | ServerHello _
  | ServerHelloDone
  | Finished _ -> true
  | _ -> false
(*
  | ClientKeyExchange _
  | EncryptedExtensions _
  | ClientKeyExchange _
  | ServerKeyExchange _
  | CertificateRequest _
  | Certificate _
  | CertificateVerify _
  | NextProtocol _
  | HelloRequest
  | SessionTicket _ -> false
*)

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

// making subtyping explicit
let narrowTag a (b:anyTag { length b = tagLen a}) : tag a = b
let tagLength (b:anyTag) = length b

// full specification of the hashed-prefix tags required for a given flight
// (in relational style to capture computational-hashed)
//val tags: a:alg -> prior: list msg -> ms: list msg -> hs: list anyTag(tag a) -> Tot Type0 (decreases ms)
let rec tags (a:alg) (prior: list msg) (ms: list msg) (hs:list anyTag) : Tot Type0 (decreases ms) =
  match ms with
  | [] -> hs == []
  | m :: ms ->
      let prior = prior @ [m] in
      match tagged m, hs with 
      | true, h::hs -> 
          let t = transcript_bytes prior in 
          (  tagLength h = tagLen a /\ 
             (  let h = narrowTag a h in 
                hashed a t /\ h == hash a t /\
                tags a prior ms hs ))
      | false, hs -> tags a prior ms hs
      | _ -> False

val tags_append: a:alg -> prior: list msg -> ms0: list msg -> ms1: list msg -> hs0: list anyTag -> hs1: list anyTag ->
  Lemma (tags a prior ms0 hs0 /\ tags a (prior @ ms0) ms1 hs1 ==> tags a prior (ms0 @ ms1) (hs0 @ hs1))


(* STATE *)

assume new type state
type t = HS.ref state
// instead of allocating a subregion, we reveal that t is a single reference;
// hopefully we get separation by typing.

//TODO we need framing for transcript, writing, ...
let region t: HH.rid = HS.(t.id)

//  specification-level transcript of all handshake messages logged so far
val transcript: h:HS.mem -> t -> GTot (list msg)

// specification-level guard for sending: we have not started receiving the next flight
val writing: h:HS.mem -> t -> GTot bool

val hashAlg: h:HS.mem -> t -> GTot (option Hashing.alg)

val create: parent:HH.rid -> ST t
  (requires (fun h0 -> True))
  (ensures (fun h0 s h1 ->
    //17-04-06 TODO extends (region r) parent /\
    writing h1 s /\
    transcript h1 s == [] /\
    hashAlg h1 s == None  ))

let modifies_0 (s:t) h0 h1 =
  HS.(mods [Ref s] h0 h1) /\
  transcript h1 s == transcript h0 s /\
  writing h1 s == writing h0 s /\
  hashAlg h1 s = hashAlg h0 s

val setParams: s:t ->
  TLSConstants.protocolVersion ->
  a: Hashing.alg ->
  option TLSConstants.kexAlg ->
  option CommonDH.group -> ST unit
  (requires (fun h0 -> None? (hashAlg h0 s)))
  (ensures (fun h0 _ h1 ->
    HS.(mods [Ref s] h0 h1) /\
    transcript h1 s == transcript h0 s /\
    writing h1 s == writing h0 s /\
    hashAlg h1 s == Some a ))

(* Outgoing *)

// We send one message at a time (or in two steps for CH);
// for call-site simplicity we distinguish between tagged and untagged messages
// We require ms_0 be empty; otherwise the hash computation is messed up

// We do not enforce "tagged m", a local decision

let write_transcript h0 h1 (s:t) (m:msg) =
    HS.(mods [Ref s] h0 h1) /\
    writing h1 s /\
    hashAlg h1 s == hashAlg h0 s /\
    transcript h1 s == transcript h0 s @ [m]


val send: s:t -> m:msg -> ST unit
  (requires (fun h0 -> writing h0 s))
  (ensures (fun h0 _ h1 -> write_transcript h0 h1 s m))

val send_tag: #a:alg -> s:t -> m:msg -> ST (tag a)
  (requires (fun h0 ->
    writing h0 s /\
    hashAlg h0 s = Some a ))
  (ensures (fun h0 h h1 ->
    let bs = transcript_bytes (transcript h1 s)  in
    write_transcript h0 h1 s m /\
    hashed a bs /\ h == hash a bs ))

// An ad hoc variant for caching a message to be sent immediately after the CCS
// We always increment the writer, sometimes report handshake completion.

val send_CCS_tag: #a:alg -> s:t -> m:msg -> complete:bool -> ST (tag a)
  (requires (fun h0 ->
    writing h0 s /\
    hashAlg h0 s = Some a ))
  (ensures (fun h0 h h1 ->
    let bs = transcript_bytes (transcript h1 s)  in
    write_transcript h0 h1 s m /\
    hashed a bs /\ h == hash a bs ))


(* Incoming *)


// We receive messages in whole flights;
// note that, untill a full flight is received, we lose "writing h1 r"
val receive: s:t -> bytes -> ST (option (list msg * list anyTag))
  (requires (fun h0 -> True))
  (ensures (fun h0 o h1 ->
    let oa = hashAlg h1 s in
    let t0 = transcript h0 s in
    let t1 = transcript h1 s in
    oa == hashAlg h0 s /\
    HS.(mods [Ref s] h0 h1) /\ (
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
val receive_CCS: s:t -> ST (option (list msg * list anyTag * anyTag))
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 ->
    match r with
    | Some  (ms,hs,h) -> (
        let oa = hashAlg h1 s in
        let t0 = transcript h0 s in
        let t1 = transcript h1 s in
        let tr = transcript_bytes t1 in
        oa == hashAlg h0 s /\
        Some? oa /\ (
        let a = Some?.v oa in
        t1 == t0 @ ms /\ tags a t0 ms hs /\ hashed a tr /\ h = hash a tr ))
     | None -> True))


// FRAGMENT INTERFACE
//
// for outgoing messages, Handshake.Log maintains
// - an output buffer (bytes) for handshake messages
// - the three flags below, to be echoed and cleared once the buffer is empty

type id = TLSInfo.id

// payload of a handshake fragment, to be made opaque eventually
type fragment (i:id) = ( rg: Range.frange i & Range.rbytes rg )
//let out_msg i rg b : msg i = (|rg, b|)

// What the HS asks the record layer to do, in that order.
type outgoing (i:id) (* initial index *) =
  | Outgoing:
      send_first: option (fragment i) -> // HS fragment to be sent;  (with current id)
      send_ccs  : bool               -> // CCS fragment to be sent; (with current id)
      next_keys : bool               -> // the writer index increases;
      complete  : bool               -> // the handshake is complete!
      outgoing i

// provides outputs to the record layer, one fragment at a time
// never fails, in contrast with Handshake.next_fragment
val next_fragment: s:t -> i:id -> ST (outgoing i)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> modifies_0 s h0 h1))

(*
  if length st.outgoing = 0
  return as we can, up to the fragment limit

    //(1) return any pending output in Handshake.Log
    // GOING to Handshake.Log
    //16-06-01 TODO: handle fragmentation; return fragment + flags set in some cases
    let l = length b in
    if (!hsref).hs_buffers.hs_outgoing_ccs then (
       hsref := {!hsref with
         hs_buffers = {(!hsref).hs_buffers with
           hs_outgoing_ccs = false }};
       Epochs.incr_writer lgref;
       Outgoing None true true false
    ) else if (l > 0) then ( // first, send next message fragment, possibly followed by a keychange signal )

       let keychange =
          match (!hsref).hs_buffers.hs_outgoing_epochchange with
          | None -> false
          | Some Reader -> Epochs.incr_reader lgref; true // possibly used by server in 0-RT
          | Some Writer -> Epochs.incr_writer lgref; true in
       IO.hs_debug_print_string (" * WRITE "^print_bytes b^"\n");
       hsref := {!hsref with
         hs_buffers = {(!hsref).hs_buffers with
           hs_outgoing = empty_bytes;
           hs_outgoing_epochchange = None }};
       Outgoing (Some (out_msg i (l,l) b)) false keychange false)

    else // were we waiting to advance our state machine & send the next messages?
 *)


(*
// move to Handshake.Log?
let print_hsl hsl : Tot bool =
    let sl = List.Tot.map (fun (x,_) -> HandshakeMessages.string_of_handshakeMessage x) hsl in
    let s = List.Tot.fold_left (fun x y -> x^", "^y) "" sl in
    debug_print ("Recv_fragment buffer: " ^ s ^ "\n")
*)
