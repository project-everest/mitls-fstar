(*--build-config
options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include . --include ideal-flags;
--*)
module Handshake.Log


open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
 // for e.g. found
open FStar.Set
open Platform.Error
open Platform.Bytes
open TLSError
open TLSConstants
open TLSInfo
open HandshakeMessages
open Hashing
open Hashing.CRF // now using incremental, collision-resistant, agile Hashing.
module HH = FStar.HyperHeap
module HS = FStar.HyperStack


(* A flag for runtime debugging of handshakelog data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)
inline_for_extraction let hsl_debug = false

type msg = hs_msg

let eoflight = 
  let open HandshakeMessages in function
  | ClientHello _
  | HelloRetryRequest _
  | ServerHello _
  | ServerHelloDone 
  | Finished _ -> true
  | _ -> false

val tagged: msg -> Tot bool
let tagged m =
  match m with
  | ClientHello _ -> true
  | ServerHello _ -> true
  | Certificate _ -> true // for CertVerify payload in TLS 1.3
  | CertificateVerify _ -> true // for ServerFinish payload in TLS 1.3
  | ClientKeyExchange _ -> true
  | Finished _ -> true // for 2nd Finished
  | _ -> false

val valid_transcript: list msg -> Tot bool
let valid_transcript hsl =
    match hsl with
    | [] -> true
    | [ClientHello ch] -> true
    | (ClientHello ch) :: (ServerHello sh) :: rest -> true
    | _ -> false

let hs_transcript : Type0 =
    if hsl_debug then l:list msg{valid_transcript l}
    else FStar.Ghost.erased (l:list msg{valid_transcript l})

let reveal_log (l:hs_transcript) : GTot (x:list msg{valid_transcript x}) =
    if hsl_debug then l
    else FStar.Ghost.reveal l

let hide_log (l:(x:list msg{valid_transcript x})) : Tot hs_transcript =
    if hsl_debug then l
    else FStar.Ghost.hide l

val transcript_version: hsl:hs_transcript -> GTot (option protocolVersion)
let transcript_version hsl =
    match reveal_log hsl with
    | (ClientHello ch) :: (ServerHello sh) :: rest -> Some sh.sh_protocol_version
    | _ -> None

// ADL Apr 5 Verification is in progress
#set-options "--lax"
let empty_transcript : hs_transcript = hide_log []
let append_transcript (l:hs_transcript) (m:msg) : Tot hs_transcript =
    if hsl_debug then l @ [m]
    else FStar.Ghost.elift1 (fun l -> l @ [m]) l

let print_hsl (hsl:hs_transcript) : Tot bool =
    if hsl_debug then
    let sl = List.Tot.map HandshakeMessages.string_of_handshakeMessage hsl in
    let s = List.Tot.fold_left (fun x y -> x^", "^y) "" sl in
    IO.debug_print_string("Current log: " ^ s ^ "\n")
    else false

val transcript_bytes: hsl:hs_transcript -> GTot bytes
let transcript_bytes l = handshakeMessagesBytes (transcript_version l) (reveal_log l)

val transcript_bytes_injective: ms0:list msg -> ms1:list msg ->
  Lemma(Seq.equal (transcript_bytes ms0) (transcript_bytes ms1) ==> ms0 == ms1)

val transcript_bytes_append: ms0: list msg -> ms1: list msg ->
  Lemma (transcript_bytes (ms0 @ ms1) = transcript_bytes ms0 @| transcript_bytes ms1)

let narrowTag a (b:anyTag { length b = tagLen a}) : tag a = b
let tagLength (b:anyTag) = length b

let rec tags (a:alg) (prior: list msg) (ms: list msg) (hs:list anyTag) : Tot Type0 (decreases ms) = 
  match ms with 
  | [] -> hs == [] 
  | m :: ms -> 
      let prior = prior @ [m] in
      match tagged m, hs with 
      | true, h::hs -> let t = transcript_bytes prior in (tagLength h = tagLen a /\ (let h = narrowTag a h in hashed a t /\ h == hash a t /\ tags a prior ms hs))
      | false, hs -> tags a prior ms hs
      | _ -> False 

val tags_append: a:alg -> prior: list msg -> ms0: list msg -> ms1: list msg -> hs0: list anyTag -> hs1: list anyTag ->
  Lemma (tags a prior ms0 hs0 /\ tags a (prior @ ms0) ms1 hs1 ==> tags a prior (ms0 @ ms1) (hs0 @ hs1))

//The type below includes buffers, the log, the hash, and the params needed to parse and hash the log.
//Note that a lot of this information is available in the log itself.
//In particular: pv+kex+hash_alg can be read from CH/SH, dh_group can be read from SKE
//TODO: decide whether to keep these parameters explicit or compute them from the log

noeq type hashState (prior parsed: list msg) = 
  | OpenHash: b:bytes { b = transcript_bytes (prior @ parsed) } -> hashState prior parsed
  | FixedHash: 
      a: Hashing.alg -> 
      state: accv a { Hashing.content state = transcript_bytes (prior @ parsed) } -> 
      hashes: list (tag a) { tags a prior parsed hashes } -> 
      hashState prior parsed

noeq type state =
  | State:
    transcript: hs_transcript ->

    outgoing: bytes -> // outgoing data, alrady formatted and hashed
    outgoing_ccs: option bytes ->
    outgoing_next_keys: bool ->
    outgoing_complete: bool ->            
    
    incoming: bytes -> // received fragments; untrusted; not yet hashed or parsed
    parsed: list msg{valid_transcript (transcript @ parsed)} -> 
                       // partial incoming flight, hashed & parsed, with selected intermediate tags
    hashes: hashState transcript parsed  -> 

  // flags

  // memoized parameters
    pv: option protocolVersion ->             // Initially: the pv in the clientHello, then the pv in the serverHello
    kex: option kexAlg ->                    // Used for the CKE and SKE
    dh_group: option CommonDH.group -> // Used for the CKE
    state
// TODO, not urgent, bound the lengths of the bytes and lists.

// the reference already carries the region
// instead of 
type log = HS.ref state
type t = log

// static precondition for HS writing messages & signals
val writing: h:HS.mem -> log -> GTot bool 
let writing h st = 
    let s = HS.sel h st in
    List.Tot.isEmpty s.parsed

// must be checked before incrementing the read epoch.
val notReading: state -> Tot bool 
let noReading st = st.parsed = [] && st.incoming = empty_bytes

val hashAlg: h:HS.mem -> log -> GTot (option Hashing.alg)
let hashAlg h st = 
    let s = HS.sel h st in 
    match s.hashes with
    | OpenHash _ -> None
    | FixedHash a _ _ -> Some a


//  specification-level transcript of all handshake messages logged so far
val transcript: h:HS.mem -> log -> GTot (list msg)
let transcript h t =
    if hsl_debug then
    (sel h t).transcript
    else
    FStar.Ghost.reveal ((sel h t).transcript)

val create: #reg:rid -> pv:option protocolVersion -> ST log
  (requires (fun h -> True))
  (ensures (fun h0 out h1 ->
    modifies (Set.singleton reg) h0 h1 /\
//    HS.is_in reg out /\
    transcript h1 out == [] /\
    writing h1 out /\
   (let s = sel h1 out in
    s.hashes = OpenHash empty_bytes /\
    s.pv = pv /\
    s.kex = None /\
    s.dh_group = None)))
let create #reg pv =
    let l = State empty_transcript empty_bytes None false false
    	    	  empty_bytes [] (OpenHash empty_bytes) 
		  pv None None in
    let st = ralloc reg l in
    st

let modifies_0 (s:log) h0 h1 = 
  HS.(mods [Ref s] h0 h1) /\
  transcript h1 s == transcript h0 s /\
  writing h1 s == writing h0 s /\
  hashAlg h1 s = hashAlg h0 s
  
val setParams: s:log -> 
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
let setParams l pv ha kexo dho =
  let st = !l in
  match st.hashes with
  | OpenHash msgs -> 
      let acc = Hashing.start ha in
      let acc = Hashing.extend #ha acc msgs in // TODO prove that content h = transcript_bytes ...
      let hs = FixedHash ha acc [] in
      l := State st.transcript st.outgoing st.outgoing_ccs st.outgoing_next_keys st.outgoing_complete
      	   	 st.incoming st.parsed hs (Some pv) kexo dho

(* SEND *)
let write_transcript h0 h1 (s:log) (m:msg) = 
    HS.(mods [Ref s] h0 h1) /\
    writing h1 s /\
    hashAlg h1 s == hashAlg h0 s /\
    transcript h1 s == transcript h0 s @ [m] 


val send: s:log -> m:msg -> ST unit 
  (requires (fun h0 -> writing h0 s)) 
  (ensures (fun h0 _ h1 -> write_transcript h0 h1 s m))
let send l m =
  let st = !l in
  let mb = handshakeMessageBytes st.pv m in
  let h : hashState st.transcript (st.parsed @ [m]) =
    match st.hashes with
    | FixedHash a acc hl ->
      let acc = Hashing.extend #a acc mb in
      FixedHash a acc hl              
    | OpenHash p ->
      OpenHash (p @| mb)
    in
  let o = st.outgoing @| mb in
  let t = append_transcript st.transcript m in
  l := State t o st.outgoing_ccs st.outgoing_next_keys st.outgoing_complete
       	       st.incoming st.parsed h st.pv st.kex st.dh_group

val send_tag: #a:alg -> s:log -> m:msg -> ST (tag a)
  (requires (fun h0 -> 
    writing h0 s /\
    hashAlg h0 s = Some a )) 
  (ensures (fun h0 h h1 -> 
    let bs = transcript_bytes (transcript h1 s)  in
    write_transcript h0 h1 s m /\ 
    hashed a bs /\ h == hash a bs ))
let send_tag #a l m =
  let st = !l in
  let mb = handshakeMessageBytes st.pv m in
  let (h,tg) : (hashState st.transcript (st.parsed @ [m]) * anyTag) = 
    match st.hashes with
    | FixedHash a acc hl ->
      let acc = Hashing.extend #a acc mb in
      let tg = Hashing.finalize #a acc in
      (FixedHash a acc hl,tg)
    in
  let o = st.outgoing @| mb in
  let t = append_transcript st.transcript m in
  l := State t o st.outgoing_ccs st.outgoing_next_keys st.outgoing_complete
       st.incoming st.parsed h st.pv st.kex st.dh_group;
  tg


// An ad hoc variant for caching a message to be sent immediately after the CCS
// We always increment the writer, sometimes report handshake completion.

val send_CCS_tag: #a:alg -> s:log -> m:msg -> complete:bool -> ST (tag a)
  (requires (fun h0 -> 
    writing h0 s /\
    hashAlg h0 s = Some a )) 
  (ensures (fun h0 h h1 -> 
    let bs = transcript_bytes (transcript h1 s)  in
    write_transcript h0 h1 s m /\ 
    hashed a bs /\ h == hash a bs ))
let send_CCS_tag #a l m c =
  send_tag #a l m 


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

// ADL Apl 5: TODO Cedric needs to implement the flag storage/reset logic here
let next_fragment l (i:id) =
  let st = !l in
//(State pv ha kex dh l b h) = !st in
  let out_msg =
    let o = st.outgoing in
    let lo = length o in
    if (lo = 0) then None else
    if (lo <= max_TLSPlaintext_fragment_length) then
      let rg = (lo, lo) in
      Some (| rg, o |)
    else
      let (x,y) = split o max_TLSPlaintext_fragment_length in
      l := State st.transcript y st.outgoing_ccs st.outgoing_next_keys st.outgoing_complete
      	    	  st.incoming st.parsed st.hashes st.pv st.kex st.dh_group;
      let lx = length x in
      let rg = (lx, lx) in
      Some (| rg, x |)
  in
  Outgoing out_msg false false false // FIXME Flag bufferization

(* RECEIVE *)

val parseHandshakeMessages : pvo: option protocolVersion ->
    			     kexo: option kexAlg ->
			     buf: bytes -> ST (result (bytes * list msg * list bytes))
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies Set.empty h0 h1))
let rec parseHandshakeMessages pvo kexo buf =
    match parseMessage buf with
    | Error z -> Error z
    | Correct(None) -> Correct(buf,[],[])
    | Correct(Some (|rem,hstype,pl,to_log|)) ->
      (match parseHandshakeMessage pvo kexo hstype pl with
       | Error z -> Error z
       | Correct hsm ->
       	     if eoflight hsm then Correct(rem,[hsm],[to_log]) else
             (match parseHandshakeMessages pvo kexo rem with
             | Error z -> Error z
             | Correct (r,hl,bl) -> Correct (r,hsm::hl,to_log::bl)))

val hashHandshakeMessages : t: hs_transcript ->
    			    p: list msg ->
			    hashes: hashState t p ->
			    next: (list msg) -> 
			    nextb: (list bytes) -> 
			    ST (hashState t (p @ next) * 
				list anyTag)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies Set.empty h0 h1))
let rec hashHandshakeMessages  t p hs n nb = 
    match n,nb with
    | [],[] -> (hs,[])
    | m::mrest,mb::brest -> 
         (match hs with 
	  | OpenHash b ->
	    let hs = OpenHash (b @| mb) in
	    let (hs,tl) = hashHandshakeMessages t (p @ [m]) hs mrest brest in
	    (hs,tl)
	  | FixedHash a acc tl ->
	    let acc = Hashing.extend #a acc mb in
	    let tl = if tagged m then   
	    	     let t = Hashing.finalize #a acc in
		     tl @ [t] 
		     else tl in
	    let hs = FixedHash a acc tl in
	    let (hs,tl') = hashHandshakeMessages t (p @ [m]) hs mrest brest in
	    (hs,tl@tl'))    

val receive: s:log -> bytes -> ST (option (list msg * list anyTag))
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
let receive l mb =
  let st = !l in
  let ib = st.incoming @| mb in
  match parseHandshakeMessages st.pv st.kex ib with
  | Error z -> None
  | Correct(r,[],[]) ->
       l := State st.transcript st.outgoing st.outgoing_ccs st.outgoing_next_keys st.outgoing_complete
      	    	   r st.parsed st.hashes st.pv st.kex st.dh_group;
       Some ([],[])
  | Correct(r,ml,bl) ->
       let (hs,tl) = hashHandshakeMessages st.transcript st.parsed st.hashes ml bl in
       l := State st.transcript st.outgoing st.outgoing_ccs st.outgoing_next_keys st.outgoing_complete
      	    	  r st.parsed hs st.pv st.kex st.dh_group;
       Some (ml,tl)

