(** outlining the HS Log API *)
(* recording semantics, a trade-off to have fewer transitions. *)
module HSL // an outline of Handshake.Log

open Platform.Bytes
open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Ghost // after HH so as not to shadow reveal :( 

open Hashing
open Hashing.CRF // now using incremental, collision-resistant, agile Hashing.


(* Handshake.Msg *) 
// simplified handshake messages; for this outline we show that the client 
// agrees with the server on the two offers after checking the Finished message

assume type offer: Type0
// 17-01-19 Still confused about concrete syntax for universes + eqtypes
noeq type msg: Type0 = | ClientHello of offer | ServerHello of offer | Finished of (tag SHA256)

assume val format: msg -> Tot bytes 
assume val parse_msg: b:bytes -> Tot (option (m:msg {b = format m}))

val tagged: msg -> Tot bool // do we compute a hash of the transcript ending with this message?
let tagged = function
  | ServerHello _ -> true 
  | _ -> false 

val eoflight: msg -> Tot bool // does this message complete the flight? 
let eoflight = function
  | ClientHello _ | Finished _ -> true 
  | _ -> false 


(* An outline of Handshake.Log *)

let transcript_bytes ms = List.Tot.fold_left (fun a m -> a @| format m) empty_bytes ms
// we will need to prove it is injective, we will rely in turn on concrete msg formats
// should use a named lambda

// formatting of the whole transcript is injective (what about binders?)
assume val transcript_format_injective: ms0:list msg -> ms1:list msg -> 
  Lemma(Seq.equal (transcript_bytes ms0) (transcript_bytes ms1) ==> ms0 == ms1)

//17-01-23  how to prove this from the definition above??
assume val transcript_bytes_append: ms0: list msg -> ms1: list msg -> 
  Lemma (transcript_bytes (ms0 @ ms1) = transcript_bytes ms0 @| transcript_bytes ms1)


// full specification of the hashed-prefix tags required for a given flight 
// switching to a relational style to capture computational-hashed 
val tags: a:alg -> prior: list msg -> ms: list msg -> hs: list (tag a) -> Tot Type0 (decreases ms)
let rec tags a prior ms hs = 
  match ms with 
  | [] -> hs == [] 
  | m :: ms -> 
      let prior = prior @ [m] in
      match tagged m, hs with 
      | true, h::hs -> let t = transcript_bytes prior in (hashed a t /\ h == hash a t /\ tags a prior ms hs)
      | false, hs -> tags a prior ms hs
      | _ -> False 
(* was:
val tags: prior: list msg -> incoming: list msg -> Tot (list tag) (decreases incoming) 
let rec tags prior incoming = 
  match incoming with 
  | [] -> [] 
  | m :: ms -> 
      let prior = List.Tot.append #msg prior [m] in
      let rest = tags prior ms in 
      if tagged m then 
        hash (transcript_bytes prior) :: rest
      else 
        rest
*) 

val tags_nil_nil: a:alg -> prior: list msg -> Lemma (tags a prior [] [])
let tags_nil_nil a prior = ()

//17-01-23 plausible ? 
assume val tags_append: a:alg -> prior: list msg -> ms0: list msg -> ms1: list msg -> hs0: list (tag a) -> hs1: list (tag a) -> 
  Lemma(tags a prior (ms0 @ ms1) (hs0 @ hs1) <==> tags a prior ms0 hs0 /\ tags a (prior @ ms0) ms1 hs1)
(*
let rec tags_append prior in0 in1 = 
  match in0 with
  | [] -> ( assert(prior @ in0 == prior) )
  | m :: ms -> ...
*)      


(* STATE *)

//17-01-23 erasing the transcript involved many hide/reveal annotations and restrictions on embedding proofs in
//17-01-23 stateful code. Besides, we need conditional ghosts... We may try again once the code is more stable.

noeq type state (a:alg) = | State:
  transcript: (*erased*) list msg -> // session transcript shared with the HS so far 
  input_msgs: list msg -> // partial incoming flight, hashed & parsed, with selected intermediate tags
  input_hashes: list (tag a) { tags a transcript input_msgs input_hashes } -> 
  hash: accv a { content hash = transcript_bytes (transcript @ input_msgs) } -> // current hash state
  state a
type t (a:alg) = r:ref (state a) // 17-01-19 HS naming!?

val transcripT: h:mem -> #a:alg -> t a -> GTot (list msg) // the current transcript shared with the handshake
let transcripT h #a r = (FStar.HyperStack.sel h r).transcript

(*

(*
// type flight (prior:erased (list msg)) = ms:list msg & hs:list tag { hs = tags (reveal prior) ms }

// internal state (although we may initially keep it transparent) 
abstract type plainbytes i = bytes  // a shortcut: HSL merges handshake traffic at different indexes
abstract type state = State
  transcript: erased (list Msg.t) // session transcript shared with the HS so far 
  output_bytes: buffer byte      // outgoing messages, already formatted and hashed.
  input_bytes: buffer byte       // received fragments; untrusted; not yet hashed or parsed
  input_msgs: flight  // partial incoming flight, hashed & parsed, with selected intermediate tags
  hash: Hash.t { hash = HashA (transcript_bytes (List.Tot.append transcript input_msgs)) } // current hash state
*)

We will also need to keep track of lengths in the input/output buffers
To separate between Reading and Writing modes, a precondition for sending a message should be that both input_bytes and input_msgs are empty. 
(unclear who should check for emptyset, and how to react to extra bytes buffered past the input flight)
*)

(* commenting out the rest of the outline not used in the sample code for now: 

type t  // a stateful instance of HS log, including I/O buffers

val writing: mem -> t -> GTot bool // can we currently send a HS message? 

val create: r:region -> ST t 
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> "allocated in r" /\ writing h1 r /\ transcript h1 r = Seq.createEmpty

// Flights are delimited by changes either of epoch or direction.

// We send one message at a time (or in two steps for CH)

val send: t -> i:id -> msg:Msg.t -> ST (if tagged msg then tag else unit)
  (requires (fun h0 -> writing h0 t)) 
  (ensures (fun h0 r h1 -> 
    transcript h1 t = snoc (transcript h0 t) msg /\
    if tagged msg then Hash.hashed r (transcript h1 t) // we need to witness the hash computation, not just t = H (transcript h1 t)
  ))

// For the record layer (no effect on the abstract HS state)
val next_fragment: t -> i:id -> ST (option fragment)
  (ensures (fun h0 r h1 -> transcript h0 t = transcript h1 t)) 
*)

// We receive messages in whole flights 
val receive: #a:alg -> r:t a -> bytes -> ST (option (list msg * list (tag a)))
  (requires (fun h0 -> True))
  (ensures (fun h0 o h1 -> 
    let t0 = transcripT h0 r in
    let t1 = transcripT h1 r in
    match o with 
    | Some (ms, hs) -> t1 == t0 @ ms /\ tags a t0 ms hs
    | None -> t1 == t0
  ))
 
//17-01-23 typechecking of this function still failing in many ways
let receive #a r bs = 
  match parse_msg bs with // assuming bs is a potential whole message
  | None -> None
  | Some m -> (
      let State prior ms hs v = !r in
      let content0 = transcript_bytes (prior @ ms) in 
      let content1 = transcript_bytes (prior @ (ms @ [m])) in 
      //let content1 = transcript_bytes ((transcript @ ms) @ [m]) in 
      assume((prior @ ms) @ [m] == prior @ (ms @ [m])); //17-01-24 dubious
      transcript_bytes_append prior ms;
      transcript_bytes_append prior (ms@[m]);
      transcript_bytes_append (prior@ms) [m];
      assert(Seq.equal content1 (content0 @| transcript_bytes [m]));
      assert_norm(Seq.equal (transcript_bytes [m]) (format m));
      assert(Seq.equal content1 (content0 @| format m));
      assert(tags a prior ms hs); 
      //tags_append prior ms [m] hs 
      let ms = ms @ [m]  in
      assert_norm(Seq.equal (transcript_bytes [m]) (format m));
      let v = extend v bs in
      assert(content v == content1);
      let hs : hs: list (tag a) { tags a prior ms hs } = 
        if tagged m 
          then (
            hs @ [finalize v]) 
          else 
            hs in 
      if eoflight m then  
        let prior1 = prior @ ms in 
        ( tags_nil_nil a prior1; 
          assert(tags a prior1 [] []);
          assert(content v == transcript_bytes prior1);
          r := State prior1 [] [] v; 
          Some (ms,hs) ) 
      else (
        r := State prior ms hs v; 
        None ))

(*
design: ghost log vs forall log?
design: how to return flights with intermediate tags?
TODO: support multiple epochs? 
*)



////// An outline of Handshake

assume val nego: offer -> GTot offer // the server's choice of parameters
assume val mac_verify: a:alg -> h:tag a -> t:tag SHA256-> 
// in existential style, did not manage to trigger on offer.
//  Tot (b:bool { b ==> (exists offer.  h = hash(transcript_bytes [ClientHello offer; ServerHello (nego offer)])) })
  Tot (b:bool { b ==> (forall c s.  
    let tr = transcript_bytes [ClientHello c; ServerHello s] in 
    (hashed a tr /\ h = hash a tr ==> s == nego c)) })

(*
let inj_format c0 s0 c1 s1 : Lemma ( 
  hash (transcript_bytes [ClientHello c0; ServerHello s0]) == 
  hash (transcript_bytes [ClientHello c1; ServerHello s1]) ==> c0 == c1 /\ s0 == s1 ) = 
  assume false
*)

noeq type result 'a = 
  | Result of 'a
  | Error of string 
  | Retry

// the HS handler for receiving the server flight after sending a client offer
val process: a:alg -> log:t a -> bytes -> c:offer -> ST (result offer)
  (requires (fun h0 -> 
    transcripT h0 log == [ClientHello c]))
  (ensures (fun h0 r h1 -> 
    match r with 
    | Result s -> ( s == nego c /\ (exists (t:tag SHA256). transcripT h1 log == [ClientHello c; ServerHello s; Finished t]))
    | Retry -> transcripT h1 log == transcripT h0 log 
    | Error _ -> True))
let process a log (raw:bytes) c = 
  match receive log raw with 
  | None -> Retry
  | Some ([ServerHello s; Finished t], [hash_ch_sh]) -> 
    if mac_verify a hash_ch_sh t then  (
      let h1 = ST.get() in 
      assert(transcripT h1 log == [ClientHello c; ServerHello s; Finished t]);
      assert(hashed a hash_ch_sh);
      assert(hash_ch_sh = hash a (transcript_bytes [ClientHello c; ServerHello s])); 
      assert(s == nego c);
      Result s
    )
    else Error "bad Mac"
  | _ -> Error "bad Flight" 
