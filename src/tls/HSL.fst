(** outlining the HS Log API *)
(* recording semantics, a trade-off to have fewer transitions. *)
module HSL // an outline of Handshake.Log

open Platform.Bytes
open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Ghost // after HH so as not to shadow reveal :( 

/// HASH outlining how to handle incrementality and collision-resistance. No agility yet.

let blocklen = 16 //unclear when to switch to machine integers
type block = lbytes blocklen // used here both as hash tags and MAC tags
type tag = lbytes blocklen

assume val compress: block -> block -> Tot block 

// supposing we add 4 bytes for the length and 1+ bytes for padding
assume val suffix: len:nat  -> Tot (c:bytes { (len + length c) % blocklen = 0 /\ length c <= 5 /\ length c < blocklen + 5 })
assume val block0: block 

val hash2: a:block -> b:bytes { length b % blocklen = 0 } -> Tot block (decreases (length b))
let rec hash2 a b = 
  if length b = 0 then a 
  else 
    let c,b = split b blocklen in 
    hash2 (compress a c) b 

// computed in one step (specification) 
val hash: bytes -> Tot tag 
let hash b = hash2 block0 (b @| suffix (length b)) 

type accv = | Acc: len:nat -> a:block -> b:lbytes (len % blocklen) -> accv 

// partial computation (specification) 
val hashA: bytes -> Tot accv
let hashA b = 
  let pending = length b % blocklen in 
  let hashed, rest = split b (length b - pending) in
  Acc (length b) (hash2 block0 hashed) rest

//type acc = content:bytes (* TODO: ghost in real mode *) & v:accv { v = hashA content }

let start = hashA empty_bytes // i.e. block0

// this interface requires that the caller knows what he is hashing, to keep track of computed collisions
val extend: 
  content:bytes (* TODO: ghost in real mode *) -> 
  a:accv { a == hashA content } ->
  b:bytes ->
  Tot (a:accv { a == hashA (content @| b) })

assume val hash2_append:
  a:block -> 
  b0:bytes { length b0 % blocklen = 0 } -> 
  b1:bytes { length b1 % blocklen = 0 } -> 
  Lemma (hash2 a (b0 @| b1) = hash2 (hash2 a b0) b1)

let extend content v b = 
  let z = v.b @| b in 
  let pending = length z % blocklen in
  let hashed, rest = split z (length z - pending) in
  // proof only: unfolding a == hashA content
  assert(Seq.equal z (hashed @| rest)); 
  let b0, c0 = split content (length content - (length content % blocklen)) in 
  assert(Seq.equal content (b0 @| v.b));
  assert(v.len = length content);
  assert(v.a == hash2 block0 b0);
  hash2_append block0 b0 hashed; 
  let content' = content @| b in  // unfolding hashA (content @| b) 
  let b0', c0' = split content' (length content' - (length content' % blocklen)) in 
  assert(Seq.equal rest c0');
  assert(Seq.equal content' (b0' @| rest));
  assert(Seq.equal b0' (b0 @| hashed));
  assert(pending = length content' % blocklen);
  assert(v.len + length b = length (content @| b));
  assert(hash2 v.a hashed = hash2 block0 (b0 @| hashed));
  Acc (v.len + length b) (hash2 v.a hashed) rest

// witnessing that we hashed this particular content (for collision detection)
assume val hashed: bytes -> Type
val finalize: 
  content:bytes (* TODO: ghost in real mode *) ->
  a:accv { a = hashA content } -> 
  ST tag 
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> 
    t = hash content /\ 
    hashed content /\
    h0 == h1 
    // to be adjusted, e.g. 
    // modifies_one h0 h1 hashTable /\ 
    //sel h1 hashTable == snoc (sel h0 hashTable) (content, t)
  ))

let finalize content v = 
  assume(hashed content); 
  let b0, rest = split content (length content - length content % blocklen) in 
  assert(Seq.equal content (b0 @| rest));
  let b1 = v.b @| suffix v.len in 
  let b = content @| suffix v.len in 
  assert(Seq.equal b (b0 @| b1)); 
  hash2_append block0 b0 b1; 
  hash2 v.a b1


///// From Handshake.Msg

assume type offer: Type0
// 17-01-19 Still confused about concrete syntax for universes + eqtypes
noeq type msg: Type0 = | ClientHello of offer | ServerHello of offer | Finished of tag
// simplified handshake message; for this outline we show that the client agrees with the server on the two offers after checking the Finished message

assume val format: msg -> Tot bytes 
// TODO formatting is injective

assume val parse_msg: b:bytes -> Tot (option (m:msg {b = format m}))
assume val tagged: msg -> Tot bool // do we compute a hash of the transcript ending with this message?
assume val eoflight: msg -> Tot bool // does this message complete the flight? 

///// An outline of HSL 

let transcript_bytes ms = List.Tot.fold_left (fun a m -> a @| format m) empty_bytes ms
// we will need to prove it is injective, we will rely in turn on concrete msg formats

//17-01-23  how to prove this from the definition above??
assume val transcript_bytes_append: ms0: list msg -> ms1: list msg -> 
  Lemma (transcript_bytes (ms0 @ ms1) = transcript_bytes ms0 @| transcript_bytes ms1)

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

val tags_nil_nil: prior: list msg -> Lemma (tags prior [] = [])
let tags_nil_nil prior = ()

//17-01-23 plausible ? 
assume val tags_append: prior: list msg -> in0: list msg -> in1: list msg -> Lemma(tags prior (in0 @ in1) = tags prior in0 @ tags (prior @ in0) in1)


(* STATE *)

//17-01-23 erasing the transcript involved many hide/reveal annotations and restrictions on embedding proofs in
//17-01-23 stateful code. Besides, we need conditional ghosts... We may try again once the code is more stable.

noeq type state = | State:
  transcript: (*erased*) list msg -> // session transcript shared with the HS so far 
  input_msgs: list msg -> // partial incoming flight, hashed & parsed, with selected intermediate tags
  input_hashes: list tag { input_hashes == tags transcript input_msgs } -> 
  hash: accv { hash == hashA (transcript_bytes (transcript @ input_msgs)) } -> // current hash state
  state
type t = r:ref state // 17-01-19 HS naming!?

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

val transcripT: h:mem -> t -> GTot (list msg) // the current transcript shared with the handshake
let transcripT h (r:t) = 
  let s = FStar.HyperStack.sel h r in 
  s.transcript

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
    let prior = transcripT h0 r in
    match o with 
    | Some (ms, hs) -> transcripT h1 r == prior @ ms /\ hs = tags prior ms
    | None -> transcripT h1 r == prior
  ))

//17-01-23 still failing in many ways
let receive r bs = 
  match parse_msg bs with // assuming bs is a potential whole message
  | None -> None
  | Some m -> (
      let State transcript ms hs a = !r in
      let content0 = transcript_bytes (transcript @ ms) in 
      let content1 = transcript_bytes ((transcript @ ms) @ [m]) in 
      transcript_bytes_append (transcript @ ms) [m];
      assert(hs = tags transcript ms); 
      tags_append transcript ms [m];
      let ms = ms @ [m]  in
      assert_norm(Seq.equal (transcript_bytes [m]) (format m));
      assert(Seq.equal content1 (content0 @| format m));
      let a = extend content0 a bs in
      assert(a == hashA content1);
      let hs : hs: list tag { hs = tags transcript ms } = 
        if tagged m 
          then (hs @ [finalize content1 a]) 
          else [] in 
      if eoflight m then  
        let transcript = transcript @ ms in 
        ( tags_nil_nil transcript; 
          assert(a == hashA (transcript_bytes transcript));
          r := State transcript [] [] a; 
          Some (ms,hs) ) 
      else (
        r := State transcript ms hs a; 
        None ))


(*
design: ghost log vs forall log?
design: how to return flights with intermediate tags?
TODO: support multiple epochs? 
*)

////// An outline of HS 

assume val nego: offer -> GTot offer // the server's choice of parameters
assume val mac_verify: h:tag -> t:tag -> 
  Tot (b:bool { b ==> (exists offer.  h = hash (format (ClientHello offer) @| format (ServerHello (nego offer)))) })

let inj_format c0 s0 c1 s1 : Lemma ( 
  hash (format (ClientHello c0) @| format (ServerHello s0)) == 
  hash (format (ClientHello c1) @| format (ServerHello s1)) ==> c0 == c1 /\ s0 == s1 ) = 
  assume false


val process: log:t -> bytes -> c:offer -> ST (option offer)
  (requires (fun h0 -> transcripT h0 log == [ClientHello c]))
  (ensures (fun h0 o h1 -> 
    match o with 
    | Some s -> ( s == nego c /\ (exists tag. transcripT h1 log == [ClientHello c; ServerHello s; Finished tag]))
    | None -> transcripT h1 log == transcripT h0 log ))
let process log (raw:bytes) client_offer = 
  match receive log raw with 
  | Some ([ServerHello server_offer; Finished tag], [hash_ch_sh]) -> 
    if mac_verify hash_ch_sh tag then  (
    assert(hash_ch_sh = hash (format (ClientHello client_offer) @| format (ServerHello (server_offer)))); 
    assert(exists offer.  hash_ch_sh == hash (format (ClientHello offer) @| format (ServerHello (nego offer))));
    assert(server_offer == nego client_offer);
    assume false;
    Some server_offer 
    )
    else 
    None
  | _ -> None
