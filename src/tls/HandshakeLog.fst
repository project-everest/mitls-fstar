module HandshakeLog

(* see als comments in Handshake.fsti *)

open FStar.Seq
open FStar.Error

open Mem
open TLSError
open TLSConstants
open TLSInfo
open HandshakeMessages
open Hashing
open Hashing.CRF // now using incremental, collision-resistant, agile Hashing.
open FStar.Bytes //18-08-31 reordered
open Range  // cwinter: the extracted OCaml file contains a reference to this, which is not reflected in the .depend file?

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
unfold let trace = if DebugFlags.debug_HSL then print else (fun _ -> ())

let erased_transcript : Type0 = FStar.Ghost.erased hs_transcript

let reveal_log (l:erased_transcript) : GTot (hs_transcript) =
    FStar.Ghost.reveal l

let hide_log (l:hs_transcript) : Tot erased_transcript =
    FStar.Ghost.hide l

(** TODO: move to FStar.Ghost (breach of abstraction)  *)
let elift1_def (#a #b: Type) (f: (a -> GTot b)) (x: FStar.Ghost.erased a) : Lemma (FStar.Ghost.elift1 f x == FStar.Ghost.hide (f (FStar.Ghost.reveal x))) = ()

let ghost_bind
  (#a #b: Type)
  (x: erased a)
  (f: (
    (x': a) ->
    Pure (erased b)
    (requires (x' == FStar.Ghost.reveal x))
    (ensures (fun _ -> True))
  ))
: Tot (y: erased b { y == f (FStar.Ghost.reveal x) } )
= f (FStar.Ghost.reveal x)

inline_for_extraction
let bind_log
  (l: erased_transcript)
  (f: (
    (x: hs_transcript) ->
    Pure erased_transcript
    (requires (x == reveal_log l))
    (ensures (fun _ -> True))
  ))
: Tot (y: erased_transcript { y == f (reveal_log l) } )
= ghost_bind #hs_transcript #hs_transcript l f

let empty_hs_transcript : erased_transcript = hide_log []

let append_hs_transcript
    (l:erased_transcript)
    (ml:list msg { valid_transcript (reveal_log l @ ml) } )
    : Tot erased_transcript =
      bind_log l (fun l' -> hide_log (append_transcript l' ml))

let extend_hs_transcript (l:erased_transcript) (m:msg { valid_transcript (reveal_log l @ [m]) } ) : Tot erased_transcript =
    append_hs_transcript l [m]

let print_hsl (hsl:erased_transcript) : Tot bool = false
(*
    if false then
    let sl = List.Tot.map HandshakeMessages.string_of_handshakeMessage hsl in
    let s = List.Tot.fold_left (fun x y -> x^", "^y) "" sl in
    IO.debug_print_string ("Current log: " ^ s)
    else false
*)

(* TODO: move to something like List.GTot *)
let rec gforall_list_to_list_refined
  (#a: Type)
  (f: (a -> GTot bool))
  (l: list a { gforall f l } )
: Tot (l': list (x: a {f x}))
= match l with
  | [] -> []
  | x :: q -> x :: gforall_list_to_list_refined f q

(*
let rec valid_transcript_to_list_valid_hs_msg_aux
  (v: option protocolVersion)
  (l: list msg )
  : Tot (list (valid_hs_msg v)) =
  match l with
  | [] -> []
  | a :: q -> a :: valid_transcript_to_list_valid_hs_msg_aux v q

let rec valid_transcript_to_list_valid_hs_msg_aux_inj
  (v: option protocolVersion)
  (l1: list hs_msg { gforall (valid_hs_msg_prop v) l1 } )
  (l2: list hs_msg { gforall (valid_hs_msg_prop v) l2 } )
: Lemma
  (requires (valid_transcript_to_list_valid_hs_msg_aux v l1 == valid_transcript_to_list_valid_hs_msg_aux v l2))
  (ensures (l1 == l2))
= match l1, l2 with
  | _ :: q1, _ :: q2 -> valid_transcript_to_list_valid_hs_msg_aux_inj v q1 q2
  | _ -> ()
*)

#set-options "--z3rlimit 64 --admit_smt_queries true"

let msg_bytes = function
| Msg h -> handshake_serializer32 h
| Msg12 h -> handshake12_serializer32 h
| Msg13 h -> handshake13_serializer32 h

let transcript_bytes l =
  List.Tot.fold_left (fun b m -> b @| (msg_bytes m)) empty_bytes l

(*
  : GTot bytes (decreases (List.Tot.length l)) =
  match l with
  | [] -> empty_bytes
  | h::t -> (empty_bytes) @| (transcript_bytes t)

  let v = transcript_version l in
  handshakeMessagesBytes v (valid_transcript_to_list_valid_hs_msg_aux v l)
*)


let transcript_format_injective ms0 ms1 = admit()
(*
  let f ()
  : Lemma
    (requires (FStar.Bytes.equal (transcript_bytes ms0) (transcript_bytes ms1)))
    (ensures (ms0 == ms1))
  = match ms0 with
    | [] -> ()
    | ClientHello ch0 :: q0 ->
      let v = transcript_version ms0 in
      let (ClientHello ch1 :: q1) = ms1 in
      let v1 = transcript_version ms1 in
      let l0 = handshakeMessagesBytes v (valid_transcript_to_list_valid_hs_msg_aux v q0) in
      let l1 = handshakeMessagesBytes v1 (valid_transcript_to_list_valid_hs_msg_aux v1 q1) in
      clientHelloBytes_is_injective_strong ch0 l0 ch1 l1;
      begin match q0 with
      | [] -> ()
      | ServerHello sh0 :: q0' ->
        let (ServerHello sh1 :: q1') = q1 in
        serverHelloBytes_is_injective_strong sh0 (handshakeMessagesBytes v (valid_transcript_to_list_valid_hs_msg_aux v q0')) sh1 (handshakeMessagesBytes v1 (valid_transcript_to_list_valid_hs_msg_aux v1 q1'));
        handshakeMessagesBytes_is_injective v (valid_transcript_to_list_valid_hs_msg_aux v ms0) (valid_transcript_to_list_valid_hs_msg_aux v ms1);
        valid_transcript_to_list_valid_hs_msg_aux_inj v ms0 ms1
      end
  in
  Classical.move_requires f ()
*)

//The type below includes buffers, the log, the hash, and the params needed to parse and hash the log.
//Note that a lot of this information is available in the log itself.
//In particular: pv+kex+hash_alg can be read from CH/SH, dh_group can be read from SKE
//TODO: decide whether to keep these parameters explicit or compute them from the log

#reset-options "--admit_smt_queries true"

private
let rec tags_append_aux
  (a: alg)
  (prior ms0 ms1: list msg)
  (hs0 hs1: list anyTag)
: Lemma
  (requires (tags a prior ms0 hs0 /\ tags a (prior @ ms0) ms1 hs1))
  (ensures (tags a prior (ms0 @ ms1) (hs0 @ hs1)))
  (decreases ms0)
= match ms0 with
  | [] ->
    List.Tot.append_l_nil prior
  | m :: ms ->
    let prior_before = prior in
    let prior = prior @ [m] in
    let _ : squash (tags a (prior @ ms) ms1 hs1) =
      List.Tot.append_assoc prior_before [m] ms
    in
    if tagged m
    then
      let (_::hs) = hs0 in
      tags_append_aux a prior ms ms1 hs hs1
    else
      tags_append_aux a prior ms ms1 hs0 hs1

let tags_append a prior ms0 ms1 hs0 hs1 =
  Classical.move_requires (tags_append_aux a prior ms0 ms1 hs0) hs1

noeq type hashState (prior: erased_transcript) (parsed: list msg) =
  | OpenHash: b:bytes { valid_transcript (reveal_log prior @ parsed) /\ b = transcript_bytes (reveal_log prior @ parsed) } -> hashState prior parsed
  | FixedHash:
      a: Hashing.alg ->
      state: accv a { valid_transcript (reveal_log prior @ parsed) /\ Hashing.content state = transcript_bytes (reveal_log prior @ parsed) } ->
      hashes: list anyTag { tags a (reveal_log prior) parsed hashes } ->
      hashState prior parsed

/// towards separate high-level temporary HSL.Send
///
///
open FStar.Integers
noeq
inline_for_extraction
type outbuffer (*rrel rel: srel byte*) = {
  base: Buffer.buffer UInt8.t;
  pos: (pos: UInt32.t{ v pos <= Buffer.length base });
  len: (len: UInt32.t{ v len = Buffer.length base });
}

noeq type send_state = {
  // outgoing data, already formatted and hashed. Overflows are fatal.
  outgoing: bytes; // should become an [outbuffer]

  // still supporting the high-level API to TLS and Record;
  // as next_keys_use, with next fragment after CCS
  outgoing_next_keys: option (bool & option bytes & bool);
  outgoing_complete: bool;
}
let send_state0 = {
  outgoing = empty_bytes;
  outgoing_next_keys = None;
  outgoing_complete = false; }

noeq type state =
  | State:
    transcript: erased_transcript ->

    out: send_state ->
    incoming: bytes -> // received fragments; untrusted; not yet hashed or parsed
    parsed: list msg{valid_transcript (reveal_log transcript @ parsed)} ->
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
   let s = HS.sel h st in
   OpenHash? s.hashes &&
   OpenHash?.b s.hashes = empty_bytes &&
   s.pv = pvo &&
   s.kex = None &&
   s.dh_group = None

// static precondition for HS writing messages & signals
let writing h st =
    let s = HS.sel h st in
    List.Tot.isEmpty s.parsed

// must be checked before incrementing the read epoch.
val notReading: state -> Tot bool
let notReading st = List.Tot.isEmpty st.parsed && st.incoming = empty_bytes

let hashAlg h st =
    let s = HS.sel h st in
    match s.hashes with
    | OpenHash _ -> None
    | FixedHash a _ _ -> Some a


//  specification-level transcript of all handshake messages logged so far
let transcript h t =
    reveal_log ((HS.sel h t).transcript)

#set-options "--admit_smt_queries true"
let create reg pv =
    let l = State empty_hs_transcript send_state0
              empty_bytes [] (OpenHash empty_bytes)
      pv None None in
    let st = ralloc reg l in
    st

let setParams l pv ha kexo dho =
  let st = !l in
  match st.hashes with
  | OpenHash msgs ->
      let acc = Hashing.start ha in
      let acc = Hashing.extend #ha acc msgs in
      let _ : squash (Hashing.content acc == msgs) =
        admit () (* append_empty_bytes_l msgs //TODO bytes JR 09/27 *)
      in
      assume (tags ha (reveal_log st.transcript) st.parsed []); // TODO: FIXME: should this be part of OpenHash?
      let hs = FixedHash ha acc [] in
      recall l;
      l := State
        st.transcript st.out st.incoming st.parsed
        hs (Some pv) kexo dho

(*
val getHash: #ha:hash_alg -> t:log -> ST (tag ha)
    (requires (fun h -> hashAlg h t == Some ha))
    (ensures (fun h0 i h1 -> h0 == h1))
let getHash #ha (LOG #reg st) =
    let cst = !st in
    let b =
        if false then
            print_hsl cst.transcript
        else false in
    Hashing.finalize #ha cst.hash
*)

#set-options "--admit_smt_queries true"
// Must be called after receiving a CH in the Init state of nego, indicating
// that the retry is stateless.
let load_stateless_cookie (l:log) hrr digest =
  let st = !l in
  // The cookie is loaded after CH2 is written to the hash buffer
  let OpenHash ch2b = st.hashes in  
  let fake_ch = (bytes_of_hex "fe0000") @| (Parse.vlbytes 1 digest) in
  trace ("Installing prefix to transcript: "^(hex_of_bytes fake_ch));
  let hrb = handshake_serializer32 (M_server_hello (serverHello_of_hrr hrr)) in
  trace ("HRR bytes: "^(hex_of_bytes hrb));
  let h = OpenHash (fake_ch @| hrb @| ch2b) in  
  l := State st.transcript st.out st.incoming st.parsed h st.pv st.kex st.dh_group

///
/// SEND --> high & low adaptor between Old.Handshake and Transcript

module HRR = Parsers.HelloRetryRequest

let send_truncated l m tr =
  trace ("emit "^string_of_handshakeType (tag_of m));
  let st = !l in
  let mb = msg_bytes m in
  let e = FStar.UInt32.(Bytes.len mb -^ tr) in
  let mb = Bytes.slice mb 0ul e in
  let h : hashState st.transcript (st.parsed @ [m]) =
    match st.hashes with
    | FixedHash a acc hl ->
      let acc = Hashing.extend #a acc mb in
      FixedHash a acc hl
    | OpenHash p ->
      (match m with
      | Msg (M_server_hello sh) ->
        if is_hrr sh then
          let hrr = get_hrr sh in
          let Some cs = cipherSuite_of_name hrr.HRR.cipher_suite in
          let hmsg = Hashing.compute (verifyDataHashAlg_of_ciphersuite cs) p in
          let hht = (bytes_of_hex "fe0000") @| (bytes_of_int 1 (length hmsg)) @| hmsg in
          OpenHash (hht @| mb)
	else OpenHash (p @| mb)
      | _ -> OpenHash (p @| mb))
    in
  let sto = st.out in
  let sto' = { sto with outgoing = sto.outgoing @| mb; } in
  let t = extend_hs_transcript st.transcript m in
  l := State t sto' st.incoming st.parsed h st.pv st.kex st.dh_group

let send l m = send_truncated l m 0ul

let send_raw l b =
  trace ("emit raw "^hex_of_bytes b);
  let st = !l in
  let h : hashState st.transcript st.parsed =
    match st.hashes with
    | FixedHash a acc hl ->
      let acc = Hashing.extend #a acc b in
      FixedHash a acc hl
    | OpenHash p -> OpenHash (p @| b)
    in
  let sto = { st.out with outgoing = st.out.outgoing @| b } in
  l := State st.transcript sto st.incoming st.parsed h st.pv st.kex st.dh_group

let hash_tag #a l =
  let st = !l in
  match st.hashes with
  | FixedHash a' acc hl ->
      if a <> a' then trace "BAD HASH (statically excluded)";
      Hashing.finalize #a acc
  | OpenHash b -> Hashing.compute a b

let hash_tag_truncated #a l cut =
  let open FStar.UInt32 in
  let st = !l in
  match st.hashes with
  | OpenHash b -> Hashing.compute a (Bytes.slice b 0ul (len b -^ cut))

(*
// How to create a Transcript.label_repr?  The message to hash will be
// in a new output buffer in the outgoing state, subject to

let send_tag' #a (tr:Transcript.state a) m =
  trace ("emit "^string_of_handshakeType (tag_of m)^" and hash");
  let st = !l in
  let mb = msg_bytes m in // TODO turn it into a slice, or (better) reuse new outb
  let (h,tg) : (hashState st.transcript (st.parsed @ [m]) * anyTag) =
    match st.hashes with
    | FixedHash a' acc hl ->
      let acc = Hashing.extend #a acc mb in
      let tg = Hashing.finalize #a acc in
      (FixedHash a acc hl,tg)
    | OpenHash b ->
      let b = b @| mb in
      (OpenHash b, Hashing.compute a b)
    in
  let o = st.outgoing @| mb in
  let t = extend_hs_transcript st.transcript m in
  l := State t o st.outgoing_next_keys st.outgoing_complete
       st.incoming st.parsed h st.pv st.kex st.dh_group;
  tg
*)

// maybe just compose the two functions above?
let send_tag #a l m =
  trace ("emit "^string_of_handshakeType (tag_of m)^" and hash");
  let st = !l in
  let mb = msg_bytes m in
  let (h, tg) : (hashState st.transcript (st.parsed @ [m]) & anyTag) =
    match st.hashes with
    | FixedHash a' acc hl ->
      let acc = Hashing.extend #a acc mb in
      let tg = Hashing.finalize #a acc in
      (FixedHash a acc hl,tg)
    | OpenHash b ->
      let b = b @| mb in
      (OpenHash b, Hashing.compute a b)
    in
  let sto = { st.out with outgoing = st.out.outgoing @| mb } in
  let t = extend_hs_transcript st.transcript m in
  l := State t sto st.incoming st.parsed h st.pv st.kex st.dh_group;
  tg

// An ad hoc variant for caching a message to be sent immediately after the CCS
// We always increment the writer, sometimes report handshake completion.

let send_CCS_tag #a l m cf =
  let st = !l in
  let mb = msg_bytes m in
  let (h,tg) : (hashState st.transcript (st.parsed @ [m]) & anyTag) =
    match st.hashes with
    | FixedHash a acc hl ->
      let acc = Hashing.extend #a acc mb in
      let tg = Hashing.finalize #a acc in
      (FixedHash a acc hl,tg)
    in
  let t = extend_hs_transcript st.transcript m in
  let nk =
    match st.out.outgoing_next_keys with
    | None -> Some (false, Some mb, false) in
  let sto = { st.out with outgoing_next_keys = nk; outgoing_complete = cf } in
  l := State t sto
    st.incoming st.parsed h st.pv st.kex st.dh_group;
  tg

#set-options "--admit_smt_queries true"
// TODO require or check that both flags are clear before the call
let send_signals l next_keys1 complete1 =
  let State transcript sto incoming parsed hashes pv kex dh_group = !l in
  if Some? sto.outgoing_next_keys then trace "WARNING: dirty next-key flag -- use send_CCS instead";
  if sto.outgoing_complete then trace "WARNING: dirty complete flag";
  let outgoing_next_keys1 =
    match next_keys1 with
    | Some (enable_appdata,skip_0rtt) -> Some (enable_appdata, None, skip_0rtt)
    | None -> None in
  let sto = { sto with outgoing_next_keys = outgoing_next_keys1; outgoing_complete = complete1 } in
  l := State transcript sto incoming parsed hashes pv kex dh_group

let to_be_written (l:log) =
  let st = !l in
  length st.out.outgoing

// For QUIC handshake interface
// do not do TLS fragmentation, support
// max output buffer size
let write_at_most (l:log) (i:id) (max:nat)
  : ST (outgoing i)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 ->
    modifies_one l h0 h1 /\
    hashAlg h0 l == hashAlg h1 l /\
    transcript h0 l == transcript h1 l)
  =
  let st = !l in
  // do we have a fragment to send?
  let fragment, outgoing' =
    let o = st.out.outgoing in
    let lo = length o in
    if lo = 0 then // nothing to send
       (None, empty_bytes)
    else // at most one fragment
    if (lo <= max) then
      let rg = (lo, lo) in
      (Some (| rg, o |), empty_bytes)
    else // at least two fragments
      let (x,y) = split_ o max in
      let lx = length x in
      let rg = (lx, lx) in
      (Some (| rg, x |), y) in
  if length outgoing' = 0 || max = 0
    then (
      // send signals only after flushing the output buffer
      let next_keys1, outgoing1 = match st.out.outgoing_next_keys with
      | Some(a, Some finishedFragment, z) ->
        (if a || z then trace "unexpected 1.2 signals");
        Some({
          out_appdata = a;
          out_ccs_first = true;
          out_skip_0RTT = z}), finishedFragment
      | Some(a, None, z) ->
        Some({
          out_appdata = a;
          out_ccs_first = false;
          out_skip_0RTT = z}), outgoing'
      | None -> None, outgoing' in
      let sto = { outgoing = outgoing1; outgoing_next_keys = None; outgoing_complete = false } in
      l := State
              st.transcript sto
              st.incoming st.parsed st.hashes st.pv st.kex st.dh_group;
      Outgoing fragment next_keys1 st.out.outgoing_complete
      )
    else (
      let sto = { st.out with outgoing = outgoing' } in
      l := State st.transcript sto st.incoming st.parsed st.hashes st.pv st.kex st.dh_group;
      Outgoing fragment None false )

let next_fragment l (i:id) =
  write_at_most l i max_TLSPlaintext_fragment_length




#reset-options
(* RECEIVE *)

//17-04-24 avoid parsing loop? may be simpler at the level of receive.
//17-05-09 but returning a list is convenient for handling truncated ClientHello
val parseMessages:
  pvo: option protocolVersion ->
  b: bytes ->
  ST (result (
    bool (* end of flight? *) &
    bytes (* remaining bytes *) &
    list msg (* parsed messages *) &
    list bytes (* ...and their unparsed bytes for hashes *)  ))
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies_none h0 h1))

inline_for_extraction let msg_parser pvo buf =
  match pvo with
  | None ->
    (match handshake_parser32 buf with
    | None -> fatal Decode_error "Bad CH/SH/HRR"
    | Some (msg,l) -> Correct (Msg msg, l))
  | Some TLS_1p3 ->
    (match handshake13_parser32 buf with
    | None -> fatal Decode_error "Bad handshake13 message"
    | Some (msg,l) -> Correct (Msg13 msg, l))
  | _ ->
    (match handshake12_parser32 buf with
    | None -> fatal Decode_error "Bad handshake12 message"
    | Some (msg,l) -> Correct (Msg12 msg, l))

#reset-options "--admit_smt_queries true"
let rec parseMessages pvo buf =
  let open FStar.UInt32 in
  if len buf <^ 4ul then
    Correct (false, buf, [], [])
  else
  match handshakeHeader_parser32 buf with
  | None -> fatal Decode_error "Bad message header"
  | Some (hh, _) ->
    trace ("Read header of type "^(string_of_handshakeType hh.msg_type)^" and length "^(string_of_int (4 + v hh.length))^" / "^(string_of_int (length buf)));
    if hh.length +^ 4ul >^ len buf then
      Correct (false, buf, [], [])
    else
      match msg_parser pvo buf with
      | Error z -> Error z
      | Correct (msg, l) ->
        let to_log, rest = split buf l in
        if eoflight (tag_of msg) then
          Correct (true, rest, [msg], [to_log])
        else
          match parseMessages pvo rest with
          | Error z -> Error z
          | Correct (eof, r, msg_list, log_list) ->
            Correct (eof, r, msg::msg_list, to_log::log_list)

val hashHandshakeMessages : t: erased_transcript ->
              p: list msg ->
          hashes: hashState t p ->
          next: (list msg) ->
          nextb: (list bytes) ->
          ST (hashState t (p @ next))
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies_none h0 h1))

let rec hashHandshakeMessages t p hs n nb =
    match n,nb with
    | [],[] -> hs
    | m::mrest, mb::brest ->
      (match hs with
      | OpenHash b ->
        let hs =
	  match m with
          | Msg (M_server_hello sh) ->
	    if is_hrr sh then
	     begin
	      let hrr = get_hrr sh in
              let hmsg = match cipherSuite_of_name hrr.HRR.cipher_suite with
                | Some cs -> Hashing.compute (verifyDataHashAlg_of_ciphersuite cs) b
                | None -> b in
              let hht = (bytes_of_hex "fe0000") @| (Parse.vlbytes 1 hmsg) in
              trace ("Replacing CH1 in transcript with "^(hex_of_bytes hht));
              trace ("HRR bytes: "^(hex_of_bytes mb));
              OpenHash (hht @| mb)
	     end
	    else OpenHash (b @| mb)
          | _ -> OpenHash (b @| mb)
        in
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
  match parseMessages st.pv ib with
  | Error z -> Error z
  | Correct (false,r,[],[]) -> (
       l := State
         st.transcript st.out
         r st.parsed st.hashes st.pv st.kex st.dh_group;
       Correct None )
  | Correct(eof,r,ml,bl) ->
      let hs = hashHandshakeMessages st.transcript st.parsed st.hashes ml bl in
      let ml = st.parsed @ ml in
      if eof then (
        let nt = append_hs_transcript st.transcript ml in
        let (hs,tl) : hashState nt [] & list anyTag =
          match hs with
          | FixedHash a ac htl -> FixedHash a ac [], htl
          | OpenHash _ -> hs,[] in
        l := State
          nt st.out
          r [] hs st.pv st.kex st.dh_group;
        Correct (Some (ml,tl)))
      else (
        l := State
          st.transcript st.out
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
    fatal Unexpected_message "unexpected fragment after CCS")
  else
  match st.hashes with
  | OpenHash b -> fatal Internal_error "the hash is open"
  | FixedHash a acc tl ->
    begin
      let nt = append_hs_transcript st.transcript st.parsed in
      let hs': hashState nt [] = FixedHash a acc [] in
      let h = Hashing.finalize #a acc in
      l := State
          nt st.out st.incoming [] hs' st.pv st.kex st.dh_group;
      Correct (st.parsed, tl, h)
    end
#reset-options
