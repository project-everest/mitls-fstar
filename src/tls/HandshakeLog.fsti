module HandshakeLog

// NB still missing regions and modifies clauses.

open FStar.Bytes
open FStar.Ghost // after HH so as not to shadow reveal :(

open FStar.HyperStack
open FStar.HyperStack.All
open Hashing.CRF
open HandshakeMessages // for pattern matching on messages

module HS = FStar.HyperStack

open FStar.Error
open TLSError

type msg = HandshakeMessages.hs_msg

// Does this message complete the flight?
let eoflight =
  let open HandshakeMessages in function
  | ClientHello _
  | HelloRetryRequest _
  | EndOfEarlyData
  | ServerHello _
  | ServerHelloDone
  | NewSessionTicket13 _
  | Finished _ -> true
  | _ -> false
// No support for binders yet

// Do we compute a hash of the transcript ending with this message?
// in doubt, we hash!
//val tagged: msg -> Tot bool
let tagged m =
  match m with
  | ClientHello _
  | ServerHello _
  | EndOfEarlyData        // for Client finished
  | Certificate13 _       // for CertVerify payload in TLS 1.3
  | EncryptedExtensions _ // For PSK handshake: [EE; Finished]
  | CertificateVerify _   // for ServerFinish payload in TLS 1.3
  | ClientKeyExchange _   // only for client signing
  | NewSessionTicket _    // for server finished in TLS 1.2
  | Finished _ -> true    // for 2nd Finished
  | _ -> false
// NB CCS is not explicitly handled here, but can trigger tagging and end-of-flights.

(* TODO
- add subregion discipline and the corresponding framing conditions
- make prior ghost
- add record-layer calls, keeping track of bytes buffers and their effective lengths
- support abstract plaintexts and multiple epochs
*)

let weak_valid_transcript hsl =
    match hsl with
    | [] -> true
    | [ClientHello ch] -> true
    | (ClientHello ch) :: (ServerHello sh) :: rest -> true
    | _ -> false

let transcript_version (x: list msg { weak_valid_transcript x } ) = match x with
    | (ClientHello ch) :: (ServerHello sh) :: rest -> Some sh.sh_protocol_version
    | _ -> None

(* TODO: move to something like FStar.List.GTot *)
let rec gforall (#a: Type) (f: (a -> GTot bool)) (l: list a) : GTot bool =
  match l with
  | [] -> true
  | x :: q -> f x && gforall f q

let valid_transcript hsl : GTot bool =
  weak_valid_transcript hsl &&
  gforall (valid_hs_msg_prop (transcript_version hsl)) hsl

let hs_transcript: Type0 = l:list msg {valid_transcript l}

let append_transcript (l:hs_transcript) (m:list msg {valid_transcript (l @ m)}): Tot hs_transcript = l @ m

val transcript_bytes: hs_transcript -> GTot bytes

// formatting of the whole transcript is injective (what about binders?)
val transcript_format_injective: ms0:hs_transcript -> ms1:hs_transcript ->
  Lemma(Bytes.equal (transcript_bytes ms0) (transcript_bytes ms1) ==> ms0 == ms1)

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
          valid_transcript prior /\ (
          let t = transcript_bytes prior in
          (  tagLength h = tagLen a /\
             (  let h = narrowTag a h in
                hashed a t /\ h == hash a t /\
                tags a prior ms hs ))
          )
      | false, hs -> tags a prior ms hs
      | _ -> False

val tags_append: a:alg -> prior: list msg -> ms0: list msg -> ms1: list msg -> hs0: list anyTag -> hs1: list anyTag -> Lemma (tags a prior ms0 hs0 /\ tags a (prior@ms0) ms1 hs1 ==> tags a prior (ms0 @ ms1) (hs0 @ hs1))

(*
type usage =
  | HandshakeOnly
  | Writable
  | Complete // always usable for writing appdata
*)

(* STATE *)

val log: Type0
type t = log

val get_reference: log -> GTot HS.some_ref
let region_of s =
  let (HS.Ref r) = get_reference s in
  HS.frameOf r

let modifies_one (s: log) (h0 h1: HS.mem) =
  let (HS.Ref r) = get_reference s in
  let rg = region_of s in (
    HS.modifies (Set.singleton rg) h0 h1 /\
    HS.modifies_ref rg (Set.singleton (HS.as_addr r)) h0 h1
  )

// not needed.

// the Handshake can write
val writing: h:HS.mem -> log -> GTot bool

// the assigned hash algorithm, if any
val hashAlg: h:HS.mem -> log -> GTot (option Hashing.alg)

// the transcript of past messages, in both directions
val transcript: h:HS.mem -> log -> GTot hs_transcript

//17-04-12 for now always called with pv = None.
val create: reg:TLSConstants.rgn -> pv:option TLSConstants.protocolVersion -> ST log
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
    modifies_one s h0 h1 /\
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
    modifies_one s h0 h1 /\
    writing h1 s /\
    hashAlg h1 s == hashAlg h0 s /\
    transcript h1 s == transcript h0 s @ [m]

val load_stateless_cookie: s:log -> h:hrr -> digest:bytes -> ST unit
  (requires (fun h0 -> writing h0 s /\ valid_transcript (transcript h0 s)))
  (ensures (fun h0 _ h1 -> modifies_one s h0 h1 /\ writing h1 s))

val send: s:log -> m:msg -> ST unit
  (requires (fun h0 ->
    writing h0 s /\
    valid_transcript (transcript h0 s @ [m])))
  (ensures (fun h0 _ h1 -> write_transcript h0 h1 s m))

val hash_tag: #a:alg -> s:log -> ST (tag a)
  (requires fun h0 -> True)
  (ensures fun h0 h h1 ->
    let bs = transcript_bytes (transcript h1 s)  in
    h0 == h1 /\
    hashed a bs /\ h == hash a bs )

val hash_tag_truncated: #a:alg -> s:log -> suffix_len:nat -> ST (tag a)
  (requires fun h0 ->
    let bs = transcript_bytes (transcript h0 s) in
    None? (hashAlg h0 s) /\
    suffix_len <= length bs )
  (ensures fun h0 h h1 ->
    let bs = transcript_bytes (transcript h1 s)  in
    h0 == h1 /\ suffix_len <= length bs /\ (
    let prefix, _ = split_ bs (length bs - suffix_len)  in
    hashed a prefix /\ h == hash a prefix))

val send_tag: #a:alg -> s:log -> m:msg -> ST (tag a)
  (requires fun h0 ->
    writing h0 s /\
    valid_transcript (transcript h0 s @ [m]))
  (ensures fun h0 h h1 ->
    let bs = transcript_bytes (transcript h1 s)  in
    write_transcript h0 h1 s m /\
    hashed a bs /\ h == hash a bs )

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
val send_signals: s:log -> next_keys:option (bool * bool) -> complete:bool -> ST unit
  (requires fun h0 ->
    writing h0 s /\
    (Some? next_keys || complete))
  (ensures fun h0 _ h1 ->
    modifies_one s h0 h1 /\
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

type next_keys_use = {
  out_appdata: bool; // immediately enable sending AppData fragments
  out_ccs_first: bool; // send a CCS fragment *before* installing the new key
  out_skip_0RTT: bool; // skip void server-to-client 0RTT epoch
}

// What the HS asks the record layer to do, in that order.
type outgoing (i:id) (* initial index *) =
  | Outgoing:
      send_first: option (fragment i) -> // HS fragment to be sent;  (with current id)
      next_keys : option next_keys_use -> // the writer index increases; details included
      complete: bool                        -> // the handshake is complete!
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
    modifies_one s h0 h1 /\ (
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
    modifies_one s h0 h1 /\
    hashAlg h0 s == hashAlg h1 s /\ (
    match res with
    | Error _ -> True // left underspecified
    | Correct (ml,tl,h) ->
       t1 == t0 @ ml /\ tags a t0 ml tl)))
