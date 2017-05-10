module HandshakeLog


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
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("HSL| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if Flags.debug_HSL then print else (fun _ -> ())


let erased_transcript : Type0 =
    if Flags.debug_HSL then hs_transcript
    else FStar.Ghost.erased hs_transcript

let reveal_log (l:erased_transcript) : GTot (hs_transcript) =
    if Flags.debug_HSL then l
    else FStar.Ghost.reveal l

let hide_log (l:hs_transcript) : Tot erased_transcript =
    if Flags.debug_HSL then l
    else FStar.Ghost.hide l

val transcript_version: hsl:erased_transcript -> GTot (option protocolVersion)
let transcript_version hsl =
    match reveal_log hsl with
    | (ClientHello ch) :: (ServerHello sh) :: rest -> Some sh.sh_protocol_version
    | _ -> None

// ADL Apr 5 Verification is in progress
#set-options "--lax"

let empty_hs_transcript : erased_transcript = hide_log []
let extend_hs_transcript (l:erased_transcript) (m:msg) : Tot erased_transcript =
    if Flags.debug_HSL then append_transcript l [m]
    else FStar.Ghost.elift1 (fun l -> append_transcript l [m]) l
let append_hs_transcript (l:erased_transcript) (ml:list msg) : Tot erased_transcript =
    if Flags.debug_HSL then append_transcript l ml
    else FStar.Ghost.elift1 (fun l -> append_transcript l ml) l

let print_hsl (hsl:erased_transcript) : Tot bool =
    if Flags.debug_HSL then
    let sl = List.Tot.map HandshakeMessages.string_of_handshakeMessage hsl in
    let s = List.Tot.fold_left (fun x y -> x^", "^y) "" sl in
    IO.debug_print_string ("Current log: " ^ s)
    else false

let transcript_bytes l = handshakeMessagesBytes (transcript_version l) (reveal_log l)

let transcript_format_injective ms0 ms1 = admit()

//The type below includes buffers, the log, the hash, and the params needed to parse and hash the log.
//Note that a lot of this information is available in the log itself.
//In particular: pv+kex+hash_alg can be read from CH/SH, dh_group can be read from SKE
//TODO: decide whether to keep these parameters explicit or compute them from the log

let tags_append a p ms0 ms1 hs1 hs1 = admit()

noeq type hashState (prior parsed: list msg) = 
  | OpenHash: b:bytes { b = transcript_bytes (prior @ parsed) } -> hashState prior parsed
  | FixedHash: 
      a: Hashing.alg -> 
      state: accv a { Hashing.content state = transcript_bytes (prior @ parsed) } -> 
      hashes: list (tag a) { tags a prior parsed hashes } -> 
      hashState prior parsed

noeq type state =
  | State:
    transcript: erased_transcript ->

    outgoing: bytes -> // outgoing data, alrady formatted and hashed
    outgoing_ccs: option bytes ->
    outgoing_next_keys: bool ->
    outgoing_complete: bool ->            
    
    incoming: bytes -> // received fragments; untrusted; not yet hashed or parsed
    parsed: list msg{valid_transcript (transcript @ parsed)} -> 
                       // partial incoming flight, hashed & parsed, with selected intermediate tags
    hashes: hashState transcript parsed  -> 

    // memoized parameters
    pv: option protocolVersion ->             // Initially: the pv in the clientHello, then the pv in the serverHello
    kex: option kexAlg ->                    // Used for the CKE and SKE
    dh_group: option CommonDH.group -> // Used for the CKE
    state
// TODO, not urgent, bound the lengths of the bytes and lists.

let log = HS.ref state

let get_reference l = 
    HS.(Ref l)

val init: h:HS.mem -> log -> option TLSConstants.protocolVersion -> GTot bool
let init h (st:log) (pvo: option protocolVersion) = 
   let s = sel h st in
   s.hashes = OpenHash empty_bytes &&
   s.pv = pvo &&
   s.kex = None &&
   s.dh_group = None

// static precondition for HS writing messages & signals
let writing h st = 
    let s = HS.sel h st in
    List.Tot.isEmpty s.parsed

// must be checked before incrementing the read epoch.
val notReading: state -> Tot bool 
let notReading st = st.parsed = [] && st.incoming = empty_bytes

let hashAlg h st = 
    let s = HS.sel h st in 
    match s.hashes with
    | OpenHash _ -> None
    | FixedHash a _ _ -> Some a


//  specification-level transcript of all handshake messages logged so far
let transcript h t =
    if Flags.debug_HSL then
    (sel h t).transcript
    else
    FStar.Ghost.reveal ((sel h t).transcript)

let create reg pv =
    let l = State empty_hs_transcript empty_bytes None false false
              empty_bytes [] (OpenHash empty_bytes) 
      pv None None in
    let st = ralloc reg l in
    st

let modifies_0 (s:log) h0 h1 = 
  HS.(mods [Ref s] h0 h1) /\
  transcript h1 s == transcript h0 s /\
  writing h1 s == writing h0 s /\
  hashAlg h1 s = hashAlg h0 s
  
let setParams l pv ha kexo dho =
  let st = !l in
  match st.hashes with
  | OpenHash msgs -> 
      let acc = Hashing.start ha in
      let acc = Hashing.extend #ha acc msgs in // TODO prove that content h = transcript_bytes ...
      let hs = FixedHash ha acc [] in
      l := State st.transcript st.outgoing st.outgoing_ccs st.outgoing_next_keys st.outgoing_complete
              st.incoming st.parsed hs (Some pv) kexo dho

(*
val getHash: #ha:hash_alg -> t:log -> ST (tag ha)
    (requires (fun h -> hashAlg h t == Some ha))
    (ensures (fun h0 i h1 -> h0 == h1))
let getHash #ha (LOG #reg st) =
    let cst = !st in
    let b =
        if Flags.debug_HSL then
            print_hsl cst.transcript
        else false in
    Hashing.finalize #ha cst.hash
*)

(* SEND *)
let send l m =
  trace ("emit "^HandshakeMessages.string_of_handshakeMessage m);
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
  let t = extend_hs_transcript st.transcript m in
  l := State t o st.outgoing_ccs st.outgoing_next_keys st.outgoing_complete
                st.incoming st.parsed h st.pv st.kex st.dh_group

let hash_tag #a l = 
  let st = !l in
  match st.hashes with
  | FixedHash a' acc hl -> 
      if a <> a' then trace "BAD HASH (statically excluded)";
      Hashing.finalize #a acc 

// maybe just compose the two functions above?
let send_tag #a l m =
  trace ("emit "^HandshakeMessages.string_of_handshakeMessage m^" and hash");
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
  let t = extend_hs_transcript st.transcript m in
  l := State t o st.outgoing_ccs st.outgoing_next_keys st.outgoing_complete
       st.incoming st.parsed h st.pv st.kex st.dh_group;
  tg

// An ad hoc variant for caching a message to be sent immediately after the CCS
// We always increment the writer, sometimes report handshake completion.

let send_CCS_tag #a l m cf =
  let st = !l in
  let mb = handshakeMessageBytes st.pv m in
  let (h,tg) : (hashState st.transcript (st.parsed @ [m]) * anyTag) = 
    match st.hashes with
    | FixedHash a acc hl ->
      let acc = Hashing.extend #a acc mb in
      let tg = Hashing.finalize #a acc in
      (FixedHash a acc hl,tg)
    in
  let t = extend_hs_transcript st.transcript m in
  let c = match st.outgoing_ccs with
     | None -> Some mb in
  l := State t st.outgoing c true cf
       st.incoming st.parsed h st.pv st.kex st.dh_group;
  tg

// TODO require or check that both flags are clear before the call
let send_signals l outgoing_next_keys1 outgoing_complete1 = 
  let State transcript outgoing outgoing_ccs outgoing_next_keys0 outgoing_complete0 incoming parsed hashes pv kex dh_group = !l in 
  if outgoing_next_keys0 && outgoing_next_keys1 then trace "WARNING: dirty next flag";
  if outgoing_complete0 && outgoing_complete1 then trace "WARNING: dirty complete flag";
  l := State transcript outgoing outgoing_ccs outgoing_next_keys1 outgoing_complete1  incoming parsed hashes pv kex dh_group 

let next_fragment l (i:id) =
  let st = !l in
  // do we have a fragment to send? 
  let fragment, outgoing' =
    let o = st.outgoing in
    let lo = length o in
    if lo = 0 then // nothing to send
       (None, empty_bytes)
    else // at most one fragment
    if (lo <= max_TLSPlaintext_fragment_length) then
      let rg = (lo, lo) in
      (Some (| rg, o |), empty_bytes)
    else // at least two fragments
      let (x,y) = split o max_TLSPlaintext_fragment_length in
      let lx = length x in
      let rg = (lx, lx) in
      (Some (| rg, x |), y) in 
    if length outgoing' = 0 
    then (
      // send signals only after flushing the output buffer
      let send_ccs, outgoing' = match st.outgoing_ccs with
      | Some finishedFragment -> true, finishedFragment
      | None -> false, outgoing' in 
      l := State 
              st.transcript outgoing'  None false false 
              st.incoming st.parsed st.hashes st.pv st.kex st.dh_group;
      Outgoing fragment send_ccs st.outgoing_next_keys st.outgoing_complete ) 
    else (
      l := State 
              st.transcript outgoing' st.outgoing_ccs st.outgoing_next_keys st.outgoing_complete
              st.incoming st.parsed st.hashes st.pv st.kex st.dh_group;
      Outgoing fragment false false false ) 

(* RECEIVE *)

//17-04-24 avoid parsing loop? may be simpler at the level of receive.
//17-05-09 but returning a list is convenient for handling truncated ClientHello
val parseMessages: 
  pvo: option protocolVersion -> kexo: option kexAlg -> b: bytes -> 
  ST (result (
    bool (* end of flight? *) * 
    bytes (* remaining bytes *) * 
    list msg (* parsed messages *) * 
    list bytes (* ...and their unparsed bytes for hashes *)  ))
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies Set.empty h0 h1))
let rec parseMessages pvo kexo buf =
  match HandshakeMessages.parseMessage buf with
  | Error z -> Error z
  | Correct None -> trace "more bytes required"; Correct (false, buf, [], [])
  | Correct (Some (| rem, hstype, pl, to_log |)) ->
    ( trace ("parsing " ^
        (if pvo = Some TLS_1p3 then "(1.3) " else if pvo = Some TLS_1p2 then  "(1.2) " else "(?) ") ^
        Platform.Bytes.print_bytes pl);
      if hstype = HT_client_hello
      then (
        match parseClientHello pl with // ad hoc case: we parse into one or two messages
        | Error z -> Error z
        | Correct (ch, None) -> (
          trace ("parsed [ClientHello] -- end of flight "^(if length rem > 0 then " (bytes waiting)" else ""));
          Correct(true, rem, [ClientHello ch], [to_log]))
        | Correct (ch, Some (binders, truncated)) -> (
          trace ("parsed [ClientHello; Binders] -- end of flight "^(if length rem > 0 then " (bytes waiting)" else ""));
          let chBytes, bindersBytes = split to_log (length to_log - truncated) in
          Correct(true, rem, [ClientHello ch; Binders binders], [chBytes; bindersBytes])))
      else (
        match parseHandshakeMessage pvo kexo hstype pl with
        | Error z -> Error z
        | Correct msg ->
          trace ("parsed "^HandshakeMessages.string_of_handshakeMessage msg);
          if eoflight msg
          then (
            trace ("end of flight"^(if length rem > 0 then " (bytes waiting)" else ""));
            Correct(true, rem, [msg], [to_log]) )
          else (
            match parseMessages pvo kexo rem with
            | Error z -> Error z
            | Correct (b,r,hl,bl) -> Correct (b,r,msg::hl,to_log::bl))))

val hashHandshakeMessages : t: erased_transcript ->
              p: list msg ->
          hashes: hashState t p ->
          next: (list msg) -> 
          nextb: (list bytes) -> 
          ST (hashState t (p @ next))
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies Set.empty h0 h1))
let rec hashHandshakeMessages t p hs n nb = 
    match n,nb with
    | [],[] -> hs
    | m::mrest,mb::brest -> 
         (match hs with 
    | OpenHash b ->
      let hs = OpenHash (b @| mb) in
      hashHandshakeMessages t (p @ [m]) hs mrest brest 
    | FixedHash a acc tl ->
      let acc = Hashing.extend #a acc mb in
      let tl = if tagged m then   
             let t = Hashing.finalize #a acc in
         tl @ [t] 
         else tl in
      let hs = FixedHash a acc tl in
      hashHandshakeMessages t (p @ [m]) hs mrest brest)

let receive l mb =
  let st = !l in
  let ib = st.incoming @| mb in
  match parseMessages st.pv st.kex ib with
  | Error z -> Error z
  | Correct (false,r,[],[]) -> (
       l := State 
         st.transcript st.outgoing st.outgoing_ccs st.outgoing_next_keys st.outgoing_complete 
         r st.parsed st.hashes st.pv st.kex st.dh_group;
       Correct None )
  | Correct(eof,r,ml,bl) ->
      let hs = hashHandshakeMessages st.transcript st.parsed st.hashes ml bl in
      let ml = st.parsed @ ml in
      if eof then (
        let nt = append_hs_transcript st.transcript ml in
        let (hs,tl) : hashState nt [] * list anyTag = 
          match hs with
          | FixedHash a ac htl -> FixedHash a ac [], htl
          | OpenHash _ -> hs,[] in
        l := State 
          nt st.outgoing st.outgoing_ccs st.outgoing_next_keys st.outgoing_complete
          r [] hs st.pv st.kex st.dh_group;
        Correct (Some (ml,tl)))
      else (
        l := State 
          st.transcript st.outgoing st.outgoing_ccs st.outgoing_next_keys st.outgoing_complete
          r ml hs st.pv st.kex st.dh_group;
        Correct None )
 

// We receive CCS as external end-of-flight signals;
// we return the messages processed so far, and their final tag; 
// we still can't write.
// This should *fail* if there are pending input bytes. 
let receive_CCS #a l =
  let st = !l in
  if length st.incoming > 0 
  then (
    trace ("too many bytes: "^print_bytes st.incoming);
    Error (AD_unexpected_message, "unexpected fragment after CCS"))
  else 
  match st.hashes with 
  | OpenHash b -> Error (AD_internal_error, "the hash is open")
  | FixedHash a acc tl -> 
    begin
      let nt = append_hs_transcript st.transcript st.parsed in
      let hs': hashState nt [] = FixedHash a acc [] in
      let h = Hashing.finalize #a acc in
      l := State 
          nt st.outgoing st.outgoing_ccs st.outgoing_next_keys st.outgoing_complete
          st.incoming [] hs' st.pv st.kex st.dh_group;
      Correct (st.parsed, tl, h)
    end 
