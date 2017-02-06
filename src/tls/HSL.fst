(** outlining the HS Log API *)
(* recording semantics, a trade-off to have fewer transitions. *)
module HSL // an outline of Handshake.Log

open Platform.Bytes
open FStar.Ghost // after HH so as not to shadow reveal :( 

open Hashing
open Hashing.CRF // now using incremental, collision-resistant, agile Hashing.

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

(* A dummy Handshake.Msg *) 

// simplified handshake messages; for this outline we show that the client 
// agrees with the server on the two offers after checking the Finished message

assume type offer: Type0
noeq type msg: Type0 = | ClientHello of offer | ServerHello of offer | Finished of (tag SHA256)
// 17-01-19 Still confused about concrete syntax for universes + eqtypes

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
assume val transcript_format_injective: ms0:list msg -> ms1:list msg -> 
  Lemma(Seq.equal (transcript_bytes ms0) (transcript_bytes ms1) ==> ms0 == ms1)

//17-01-23  how to prove this from the definition above??
assume val transcript_bytes_append: ms0: list msg -> ms1: list msg -> 
  Lemma (transcript_bytes (ms0 @ ms1) = transcript_bytes ms0 @| transcript_bytes ms1)

// full specification of the hashed-prefix tags required for a given flight 
// (in relational style to capture computational-hashed)
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

private val tags_nil_nil: a:alg -> prior: list msg -> Lemma (tags a prior [] [])
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
  // output_bytes: buffer byte ->     // outgoing messages, already formatted and hashed.
  // input_bytes: buffer byte ->       // received fragments; untrusted; not yet hashed or parsed
  state a
type t (a:alg) = r:HS.ref (state a) // 17-01-19 HS naming!?

//  specification-level transcript of all handshake messages logged so far
val transcriptT: h:HS.mem -> #a:alg -> t a -> GTot (list msg) 
let transcriptT h #a r = (HS.sel h r).transcript

// specification-level guard for sending: we have not started receiving the next flight
val writing: h:HS.mem -> #a:alg -> t a -> GTot bool 
let writing h #a r = List.Tot.isEmpty (HS.sel h r).input_msgs

val create: a:alg -> ST (t a) 
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> // "allocated in r" /\ writing h1 r /\ 
    writing h1 r /\  
    transcriptT h1 r == []))
let create a = 
  let v = Hashing.start a in 
  ST.ralloc HH.root (State [] [] [] v)
  
// We send one message at a time (or in two steps for CH); 
// for call-site simplicity we distinguish between tagged and untagged messages
// We require ms_0 be empty; otherwise the hash computation is messed up

val send: #a:alg -> r:t a -> m:msg {~(tagged m)} -> ST unit 
  (requires (fun h0 -> 
    writing h0 r
  )) 
  (ensures (fun h0 _ h1 -> 
    writing h1 r /\
    transcriptT h1 r == transcriptT h0 r @ [m] 
  ))
let send #a r m = 
  let State prior_0 [] hs_0 v_0 = !r in // using pattern matching to assert ms = [] 
  let bs = format m in
  let v_1 = extend v_0 bs in 
  let prior_1 = prior_0 @ [m] in 
  let hs_1 = hs_0 @ [] in
  List.Tot.append_assoc prior_0 [m] [];
  List.Tot.append_assoc prior_0 [] [m];
  transcript_bytes_append (prior_0 @ []) [m];
  assert_norm(Seq.equal (transcript_bytes [m]) bs);
  ST.recall r;
  r := State prior_1 [] hs_1 v_1

val send_tag: #a:alg -> r:t a -> m:msg {tagged m} -> ST (tag a)
  (requires (fun h0 -> 
    writing h0 r
  )) 
  (ensures (fun h0 h h1 -> 
    let t_0 = transcriptT h0 r in 
    let t_1 = transcriptT h1 r in 
    let bs = transcript_bytes t_1 in
    writing h1 r /\
    t_1 == t_0 @ [m] /\
    hashed a bs /\ h == hash a bs
  ))
let send_tag #a r m = 
  let State prior_0 [] hs_0 v_0 = !r in // using pattern matching to assert ms = [] 
  let bs = format m in
  let v_1 = extend v_0 bs in 
  let h = finalize v_1 in 
  let prior_1 = prior_0 @ [m] in 
  let hs_1 = hs_0 in
  List.Tot.append_assoc prior_0 [m] [];
  List.Tot.append_assoc prior_0 [] [m];
  transcript_bytes_append (prior_0 @ []) [m];
  assert_norm(Seq.equal (transcript_bytes [m]) bs);
  ST.recall r;
  r := State prior_1 [] hs_1 v_1;
  h

(*
// For the record layer (no effect on the abstract HS state)
val next_fragment: t -> i:id -> ST (option fragment)
  (ensures (fun h0 r h1 -> transcript h0 t = transcript h1 t)) 
*)

// We receive messages in whole flights; 
// note that, untill a full flight is received, we lose "writing h1 r"
val receive: #a:alg -> r:t a -> bytes -> ST (option (list msg * list (tag a)))
  (requires (fun h0 -> True))
  (ensures (fun h0 o h1 -> 
    let t0 = transcriptT h0 r in
    let t1 = transcriptT h1 r in
    match o with 
    | Some (ms, hs) -> t1 == t0 @ ms /\ tags a t0 ms hs /\ writing h1 r
    | None -> t1 == t0
  ))

#reset-options "--z3rlimit 40" 
let receive #a r bs = 
  match parse_msg bs with // assuming bs is a potential whole message
  | None -> None
  | Some m -> (
      let State prior ms_0 hs_0 v_0 = !r in
      let ms_1 = ms_0 @ [m]  in
      let content_0 = transcript_bytes (prior @ ms_0) in 
      let content_1 = transcript_bytes (prior @ ms_1) in 
      List.Tot.append_assoc prior ms_0 [m];

      transcript_bytes_append (prior@ms_0) [m];
      assert_norm(Seq.equal (transcript_bytes [m]) (format m));
      let v_1 = extend v_0 bs in
      // assert(content v_1 == content_1);

      let hs' = if tagged m then [finalize v_1] else [] in
      assert(tags a (prior@ms_0) [m] hs'); //17-02-06 this assert is brittle, why?
      assert(tags a prior ms_0 hs_0); 
      tags_append a prior ms_0 [m] hs_0 hs';
      let hs_1 = hs_0 @ hs' in
      // assert(tags a prior ms_1 hs_1);

      ST.recall r;
      if eoflight m then  
        let prior_1 = prior @ ms_1 in 
        ( tags_nil_nil a prior_1; 
          List.Tot.append_l_nil prior_1; // seems necessary...
          // assert(prior_1 @ [] == prior @ ms_1);
          // assert(content v_1 == transcript_bytes (prior_1 @ []));
          r := State prior_1 [] [] v_1; 
          Some (ms_1,hs_1) ) 
      else (
        r := State prior ms_1 hs_1 v_1; 
        None ))
#reset-options ""

(* An outline of Handshake, to check usability *) 

assume val nego: offer -> Tot offer // the server's choice of parameters
assume val mac_verify: a:alg -> h:tag a -> t:tag SHA256-> 
// in existential style, did not manage to trigger on offer.
//  Tot (b:bool { b ==> (exists offer.  h = hash(transcript_bytes [ClientHello offer; ServerHello (nego offer)])) })
  Tot (b:bool { b ==> (forall c s.  
    let tr = transcript_bytes [ClientHello c; ServerHello s] in 
    (hashed a tr /\ h = hash a tr ==> s == nego c)) })

assume val mac_compute: a:alg -> h:tag a -> Tot (t:tag SHA256
  { forall c s.  
    let tr = transcript_bytes [ClientHello c; ServerHello s] in 
    (hashed a tr /\ h = hash a tr ==> s == nego c) })

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

val server_process: #a:alg -> log: t a -> bytes -> ST (result (offer * offer * tag SHA256)) 
  (requires (fun h0 -> 
    transcriptT h0 log == []))
  (ensures (fun h0 r h1 -> 
    match r with 
    | Result (c,s,t) -> 
        //(exists (c:offer) (t:tag SHA256). s == nego c /\ transcriptT h1 log == [ClientHello c; ServerHello s; Finished t])
        s == nego c /\ transcriptT h1 log == [ClientHello c; ServerHello s; Finished t]
    | Retry -> transcriptT h1 log == transcriptT h0 log 
    | Error _ -> True))
#reset-options "--z3rlimit 100"
let server_process #a log (raw:bytes) = 
  match receive log raw with 
  | None -> Retry
  | Some ([ClientHello c], []) -> (
      let s = nego c in
      let h = send_tag log (ServerHello s) in
      let t = mac_compute a h in
      //assert_norm([]@[ClientHello c]@[ServerHello s]@[Finished t] == [ClientHello c; ServerHello s; Finished t]);
      send log (Finished t);
      Result (c,s,t))
  | _ -> Error "bad Flight"

// the HS handler for receiving the server flight after sending a client offer
val client_process: #a:alg -> log:t a -> bytes -> c:offer -> ST (result offer)
  (requires (fun h0 -> 
    transcriptT h0 log == [ClientHello c]))
  (ensures (fun h0 r h1 -> 
    match r with 
    | Result s -> ( s == nego c /\ (exists (t:tag SHA256). transcriptT h1 log == [ClientHello c; ServerHello s; Finished t]))
    | Retry -> transcriptT h1 log == transcriptT h0 log 
    | Error _ -> True))
let client_process #a log (raw:bytes) c = 
  match receive log raw with 
  | None -> Retry
  | Some ([ServerHello s; Finished t], [hash_ch_sh]) -> 
    if mac_verify a hash_ch_sh t then Result s
      //17-02-05 full automation!
      //let h1 = ST.get() in 
      //assert_norm([ClientHello c] @ [ServerHello s; Finished t] == [ClientHello c; ServerHello s; Finished t]);
      //assert(transcriptT h1 log == [ClientHello c] @ [ServerHello s; Finished t]);
      //assert(tags a [ClientHello c] [ServerHello s; Finished t] [hash_ch_sh]);
      //assert(hashed a (transcript_bytes [ClientHello c; ServerHello s]));
      //assert(hash_ch_sh = hash a (transcript_bytes [ClientHello c; ServerHello s])); 
      //assert(hash_ch_sh = hash a (transcript_bytes ([ClientHello c]@[ServerHello s]))); 
      //assert(s == nego c);
    else Error "bad Mac"
  | _ -> Error "bad Flight" 
