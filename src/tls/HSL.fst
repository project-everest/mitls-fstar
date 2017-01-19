(** outlining the HS Log API *)
(* recording semantics, a trade-off to have fewer transitioms. *)
module HSL  // an outline of lHandshake.Log

open Platform.Bytes
open FStar.Heap
open FStar.HyperHeap
open FStar.Ghost // afer HH so as not to shadow reveal :(
//open FStar.HyperStack

///// From Hash

assume type tag: eqtype // used here both as hash tags and MAC tags 
assume type acc
assume val hash: bytes -> Tot tag // computed in one step (specification)
assume val hashA: bytes -> Tot acc   // partial computation (specification) 
assume val extend: a0:acc -> b:bytes -> Tot (a: acc { forall (b0:bytes). a0 == hashA b0 ==> a == hashA (b0 @| b) })
assume val finalize: a:acc -> Tot (d:tag { forall (b:bytes). a == hashA b ==> d == hash b})

///// From Handshake.Msg

assume type offer: eqtype
type msg = | ClientHello of offer | ServerHello of offer | Finished of tag
// simplified handshake message; for this outline we show that the client agrees with the server on the two offers after checking the Finished message

assume val format: msg -> Tot bytes 
// TODO formatting is injective

assume val parse_msg: b:bytes -> Tot (option (m:msg {b = format m}))
assume val tagged: msg -> Tot bool // do we compute a hash of the transcript ending with this message?
assume val eoflight: msg -> Tot bool // does this message complete the flight? 

///// An outline of HSL 

let transcript_bytes ms = List.Tot.fold_left (fun a m -> a @| format m) empty_bytes ms
// we will need to prove it is injective, we will rely in turn on concrete msg formats

// a specification of the hashed-prefix tags required for a given flight 
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


(* STATE *)

// partial flights
type flight (prior:erased (list msg)) = ms:list msg & hs:list tag { hs = tags (reveal prior) ms }

(*
// internal state (although we may initially keep it transparent) 
// to be wrapped in a reference 
abstract type plainbytes i = bytes  // a shortcut: HSL merges handshake traffic at different indexes
abstract type state = State
  transcript: erased (list Msg.t) // session transcript shared with the HS so far 
  output_bytes: buffer byte      // outgoing messages, already formatted and hashed.
  input_bytes: buffer byte       // received fragments; untrusted; not yet hashed or parsed
  input_msgs: flight  // partial incoming flight, hashed & parsed, with selected intermediate tags
  hash: Hash.t { hash = HashA (transcript_bytes (List.Tot.append transcript input_msgs)) } // current hash state
*)
type state = | State:
  transcript: erased (list msg) -> // session transcript shared with the HS so far 
  input_msgs: list msg -> // partial incoming flight, hashed & parsed, with selected intermediate tags
  input_hashes: list tag { input_hashes = tags (reveal transcript) input_msgs } -> 
  hash: acc { hash = hashA (transcript_bytes (reveal transcript @ input_msgs)) } -> // current hash state
  state
type t = rref root state

val transcripT: FStar.HyperHeap.t -> GTot (list msg) // the current transcript shared with the handshake

let transcripT h (r:t) = (FStar.HyperHeap.sel h r).transcript

(*
We will also need to keep track of lengths in the input/output buffers To separate between Reading and Writing modes, a precondition for sending a message should be that both input_bytes and input_msgs are empty.(unclear who should check for emptyset, and how to react to extra bytes buffered past the input flight)
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
val receive: r:t -> bytes -> ST (option (list msg * list tag))
  (requires (fun h0 -> True))
  (ensures (fun h0 o h1 -> 
    let prior = transcripT r h0 in
    match o with 
    | Some (ms, hs) -> transcripT r h1 = prior @ ms /\ hs = tags prior ms
    | None -> transcripT r h1 = prior
  ))

let receive r bs = 
  match parse_msg bs with // assuming bs is a potential whole message
  | None -> None
  | Some m -> 
      let State transcript ms hs a = !r in
      let ms = ms @ [m]  in
      let a = extend a bs in
      let hs = if tagged m then (hs @ [finalize a]) else hs in
      if eoflight m then  
        let transcript = transcript @ ms in 
        r := State transcript [] [] a; 
        Some (ms,hs)
      else
        r := State transcript ms hs a;
        None

(*
design: ghost log vs forall log?
design: how to return flights with intermediate tags?
TODO: support multiple epochs? 
*)


////// An outline of HS 

assume val nego: offer -> GTot offer // the server's choice of parameters
assume val mac_verify: h:tag -> t:tag -> 
  Tot (b:bool { b ==> (exists offer.  h = format (ClientHello offer) @| format (ServerHello (nego offer)) ) })

val process: log:t -> bytes -> c:offer -> ST (option (s:offer {s = nego c}))
  (requires (fun h0 -> transcripT log h0 = [ClientHello c]))
  (ensures (fun h0 r h1 -> exists tag. transcripT log h1 = [ClientHello c; ServerHello (nego c); Finished tag]))
let process log (raw:bytes) client_offer = 
  match receive log raw with 
  | Some ([ServerHello server_offer; Finished tag], [hash_ch_sh]) -> 
    if mac_verify hash_ch_sh tag then   
    Some server_offer
    else 
    None
  | _ -> None
