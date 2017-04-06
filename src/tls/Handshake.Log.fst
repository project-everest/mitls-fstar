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

(* we decided to use a simpler version that does not depend on pv, which is hard to bind.
val tagged: protocolVersion -> hs_msg -> Tot bool
let tagged pv m =
  match (pv,m) with
  | TLS_1p3,ClientHello _ -> true
  | TLS_1p3,ServerHello _ -> true
  | TLS_1p3,Certificate _ -> true // for CertVerify payload in TLS 1.3
  | _,CertificateVerify _ -> true // for ServerFinish payload in TLS 1.3
  | _,ClientKeyExchange _ -> true
  | _,Finished _ -> true // for 2nd Finished
  | _ -> false
*)

(* was used for restricting the scope of signing *)
val validLog: list hs_msg -> Tot bool
let validLog hsl =
    match hsl with
    | [] -> true
    | [ClientHello ch] -> true
    | (ClientHello ch) :: (ServerHello sh) :: rest -> true
    | _ -> false

let hs_log : Type0 =
    if hsl_debug then l:list hs_msg{validLog l}
    else FStar.Ghost.erased (l:list hs_msg{validLog l})

let reveal_log (l:hs_log) : GTot (x:list hs_msg{validLog x}) =
    if hsl_debug then l
    else FStar.Ghost.reveal l

let hide_log (l:(x:list hs_msg{validLog x})) : Tot hs_log =
    if hsl_debug then l
    else FStar.Ghost.hide l

// ADL Apr 5 Verification is in progress
#set-options "--lax"
let empty_log : hs_log = hide_log []
let append_log (l:hs_log) (m:hs_msg) : Tot hs_log =
    if hsl_debug then l @ [m]
    else FStar.Ghost.elift1 (fun l -> l @ [m]) l

let print_hsl (hsl:hs_log) : Tot bool =
    if hsl_debug then
    let sl = List.Tot.map HandshakeMessages.string_of_handshakeMessage hsl in
    let s = List.Tot.fold_left (fun x y -> x^", "^y) "" sl in
    IO.debug_print_string("Current log: " ^ s ^ "\n")
    else false

val getServerHelloVersion: hsl:hs_log -> GTot (option protocolVersion)
let getServerHelloVersion hsl =
    match reveal_log hsl with
    | (ClientHello ch) :: (ServerHello sh) :: rest -> Some sh.sh_protocol_version
    | _ -> None

val getLogBytes: pv: protocolVersion -> hsl:hs_log -> GTot bytes
let getLogBytes pv l = handshakeMessagesBytes (Some pv) (reveal_log l)

val getLogBytes_injective: pv:protocolVersion -> ms0:list hs_msg -> ms1:list hs_msg ->
  Lemma(Seq.equal (getLogBytes pv ms0) (getLogBytes pv ms1) ==> ms0 == ms1)

val getLogBytes_append: pv:protocolVersion -> ms0: list hs_msg -> ms1: list hs_msg ->
  Lemma (getLogBytes pv (ms0 @ ms1) = getLogBytes pv ms0 @| getLogBytes pv ms1)

type tagged_msg (pv:protocolVersion) (a:Hashing.alg) =
     | T : h:hs_msg -> o:(option (tag a)){match o with | None -> ~(tagged pv h) | Some _ -> tagged pv h} -> tagged_msg pv a

type hs_msg_bufs (pv:protocolVersion) (a:Hashing.alg) = {
     writing: bool;
     hs_incoming_parsed : list (tagged_msg pv a);  // messages parsed and hashed earlier
     hs_incoming: bytes;                         // incomplete message received earlier
     hs_outgoing: bytes;                         // messages to be sent in current epoch
     hs_outgoing_epochchange: option rw;         // Whether to increment the reader or writer epoch after sending the messages in the current epoch
     hs_outgoing_ccs: bool;                      // Whether a CCS signal is buffered for the local writer
}

let hs_msg_bufs_init() = {
     writing = true;
     hs_incoming_parsed = [];
     hs_incoming = empty_bytes;
     hs_outgoing = empty_bytes;
     hs_outgoing_epochchange = None;
     hs_outgoing_ccs = false; //17-03-28 should now hold a formatted fragment.
}

//The type below includes buffers, the log, the hash, and the params needed to parse and hash the log.
//Note that a lot of this information is available in the log itself.
//In particular: pv+kex+hash_alg can be read from CH/SH, dh_group can be read from SKE
//TODO: decide whether to keep these parameters explicit or compute them from the log

noeq type log_state =
  | LOG_ST:  pv: protocolVersion ->    // Initially: the pv in the clientHello, then the pv in the serverHello
         hash_alg: Hashing.alg ->  // Initially: the hash_alg(s?) in the clientHello, then the hash_alg chosen in the serverHello
         kex: option kexAlg ->	           // Used for the CKE and SKE
	 dh_group: option CommonDH.group -> // Used for the CKE
         transcript: hs_log ->
	 buffers: hs_msg_bufs pv hash_alg ->
	 hash: accv hash_alg { content hash = getLogBytes pv transcript} ->
	 log_state


(* NEW *) 
type hs_msg_bufs (pv:protocolVersion) (a:Hashing.alg) = {
     writing: bool;
     hs_incoming_parsed : list (tagged_msg pv a);  // messages parsed and hashed earlier
     hs_incoming: bytes;                         // incomplete message received earlier
     hs_outgoing: bytes;                         // messages to be sent in current epoch
     hs_outgoing_epochchange: option rw;         // Whether to increment the reader or writer epoch after sending the messages in the current epoch
     hs_outgoing_ccs: bool;                      // Whether a CCS signal is buffered for the local writer
}

let hs_msg_bufs_init() = {
     writing = true;
     hs_incoming_parsed = [];
     hs_incoming = empty_bytes;
     hs_outgoing = empty_bytes;
     hs_outgoing_epochchange = None;
     hs_outgoing_ccs = false; //17-03-28 should now hold a formatted fragment.
}

// to be adjusted
assume val transcript_bytes: list hs_msg -> bytes 
let tags a b c d = True

//The type below includes buffers, the log, the hash, and the params needed to parse and hash the log.
//Note that a lot of this information is available in the log itself.
//In particular: pv+kex+hash_alg can be read from CH/SH, dh_group can be read from SKE
//TODO: decide whether to keep these parameters explicit or compute them from the log

noeq type hashState (prior parsed: list hs_msg) = 
  | OpenHash: b:bytes { b = transcript_bytes (prior @ parsed) } -> hashState prior parsed
  | FixedHash: 
      a: Hashing.alg -> 
      state: accv a { Hashing.content state = transcript_bytes (prior @ parsed) } -> 
      hashes: list (tag a) { tags a prior parsed hashes } -> 
      hashState prior parsed

noeq (* abstract *) type state = | State:
  transcript: (*erased*) list hs_msg -> // session transcript shared with the HS so far 

  // untrusted hints for parsing --- we do not verify they are synchronized with Nego
  pv: option protocolVersion -> // Initially: the pv in the clientHello, then the pv in the serverHello
  kex: option kexAlg -> // Used for the CKE and SKE
  dh_group: option CommonDH.group -> // Used for the CKE

  // incoming
  incoming: bytes -> // received fragments; untrusted; not yet hashed or parsed
  parsed: list hs_msg -> // partial incoming flight, hashed & parsed, with selected intermediate tags
  hashes: hashState transcript parsed  -> 

  // outgoing 
  outgoing: bytes -> // outgoing messages, already formatted and hashed.
  outgoing_next_keys: bool -> // for now only in the outgoing direction (as in Outgoing) although we may need to add  incoming key changes.
  outgoing_complete: bool -> // deferred signal (as in Outgoing)
  outgoing_ccs: option bytes -> // at most one fragment for the (already-hashed) Finished message to be sent immediately after CCS.

  state
// TODO, not urgent, bound the lengths of the bytes and lists.

// static precondition for HS writing messages & signals
val writing: h:HS.mem -> state -> GTot bool 
let writing h st = List.Tot.isEmpty (HS.sel h r).parsed

// must be checked before incrementing the read epoch.
val notReading: state -> Tot bool 
let noReading st = st.parsed = [] & emptyBytes st.incoming

// the reference already carries the region
// instead of 
type log = HS.ref log_state

val getHash: #ha:hash_alg -> t:log -> ST (tag ha)
    (requires (fun h -> (sel h t.state).hash_alg == ha))
    (ensures (fun h0 i h1 -> h0 == h1))
let getHash #ha (LOG #reg st) =
    let (LOG_ST pv ha kex dh hsl b h) = !st in
    let b =
        if hsl_debug then
            print_hsl hsl
        else false in
    Hashing.finalize #ha h



//  specification-level transcript of all handshake messages logged so far
val transcriptT: h:HS.mem -> log -> GTot (list hs_msg)
let transcriptT h t =
    if hsl_debug then
    (sel h t.state).transcript
    else
    FStar.Ghost.reveal ((sel h t.state).transcript)

// specification-level guard for sending: we have not started receiving the next flight
val writing: h:HS.mem -> log -> GTot bool
let writing h t =
  let (LOG_ST pv ha kex dh hsl b acc) = sel h t.state in
  b.writing

val create: #reg:rid -> pv:protocolVersion -> h:Hashing.alg -> ST log
  (requires (fun h -> True))
  (ensures (fun h0 out h1 ->
    modifies (Set.singleton reg) h0 h1 /\
    out.region == reg /\
    transcriptT h1 out == [] /\
    writing h1 out))
let create #reg pv ha =
    let hsl: hs_log = empty_log in
    let b = hs_msg_bufs_init() in
    let h = Hashing.start ha in
    let l = LOG_ST pv ha None None hsl b h in
    let st = ralloc reg l in
    LOG #reg st

val setParams: l:log -> pv:protocolVersion -> h:Hashing.alg -> kexo: option kexAlg -> dho:option CommonDH.group -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 ->
    modifies (Set.singleton l.region) h0 h1 /\
    transcriptT h1 l == transcriptT h0 l /\
    writing h1 l == writing h0 l
    ))
let setParams (LOG #reg st) pv ha kex dh =
  match !st with
  | LOG_ST _ _ _ _ hsl b h -> st := LOG_ST pv ha kex dh hsl b h

(* SEND *)

let send (LOG #reg st) m =
  let (LOG_ST pv ha kex dh l b h) = !st in
  let mb = handshakeMessageBytes (Some pv) m in
  let h = Hashing.extend #ha h mb in
  let b = {b with hs_outgoing = b.hs_outgoing @| mb} in
  let l = append_log l m in
  st := LOG_ST pv ha kex dh l b h

val send_tag: #a:Hashing.alg -> l:log -> m:hs_msg (*{tagged m}*) -> ST (tag a)
  (requires (fun h0 -> writing h0 l  /\
		    (sel h0 l.state).hash_alg == a))
  (ensures (fun h0 h h1 ->
    let t_0 = transcriptT h0 l in
    let t_1 = transcriptT h1 l in
    let pv = (sel h1 l.state).pv in
    let bs = getLogBytes pv t_1 in
    writing h1 l /\
    t_1 == t_0 @ [m] /\
    hashed a bs /\ h == hash a bs ))
let send_tag #a (LOG #reg st) m =
  let (LOG_ST pv ha kex dh l b h) = !st in
  let mb = handshakeMessageBytes (Some pv) m in
  let h = Hashing.extend #ha h mb in
  let t = Hashing.finalize #ha h in
  let b = {b with hs_outgoing = b.hs_outgoing @| mb} in
  let l = append_log l m in
  st := LOG_ST pv ha kex dh l b h;
  t

//ADL Apr. 5: implement me !
assume val send_CCS_tag: #a:Hashing.alg -> l:log -> m:hs_msg -> complete:bool -> St (tag a)


// ADL Apl 5: TODO Cedric needs to implement the flag storage/reset logic here
let next_fragment (LOG #reg st) (i:id) =
  let out_msg =
    let (LOG_ST pv ha kex dh l b h) = !st in
    let o = b.hs_outgoing in
    let lo = length o in
    if (lo = 0) then None else
    if (lo <= max_TLSPlaintext_fragment_length) then
      let rg = (lo, lo) in
      Some (| rg, o |)
    else
      let (x,y) = split o max_TLSPlaintext_fragment_length in
      let b = {b with hs_outgoing = y} in
      st := LOG_ST pv ha kex dh l b h;
      let lx = length x in
      let rg = (lx, lx) in
      Some (| rg, x |)
  in
  Outgoing out_msg false false false // FIXME Flag bufferization

(* RECEIVE *)

val parseHashHandshakeMessages : pv:protocolVersion -> a:Hashing.alg ->
				 option kexAlg -> buf:bytes -> Hashing.accv a ->
				 ST  (result (rem:bytes *
					       acc:Hashing.accv a *
					       list (tagged_msg pv a)))
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies Set.empty h0 h1))
let rec parseHashHandshakeMessages pv a kex buf acc =
    match parseMessage buf with
    | Error z -> Error z
    | Correct(None) -> Correct(buf,acc,[])
    | Correct(Some (|rem,hstype,pl,to_log|)) ->
      (match parseHandshakeMessage (Some pv) kex hstype pl with
       | Error z -> Error z
       | Correct hsm ->
             let acc = Hashing.extend #a acc to_log in
	     let tg = if tagged pv hsm then Some (Hashing.finalize acc) else None in
             (match parseHashHandshakeMessages pv a kex rem acc with
       	     | Error z -> Error z
       	     | Correct (r,acc,hsl) -> Correct (r,acc,(T hsm tg)::hsl)))


// full specification of the hashed-prefix tags required for a given flight
// (in relational style to capture computational-hashed)
//val tags: a:alg -> prior: list msg -> ms: list msg -> hs: list (tag a) -> Tot Type0 (decreases ms)
let rec tags (pv:protocolVersion) (a:alg) (prior: list hs_msg)
	     (ms: list (tagged_msg pv a)) : Tot Type0 (decreases ms) =
  match ms with
  | [] -> True
  | (T m h) :: ms ->
      let prior = prior @ [m] in
      match tagged pv m, h with
      | true, Some hv ->
	let t = getLogBytes pv prior in
	(hashed a t /\ hv == hash a t /\ tags pv a prior ms)
      | false, None -> tags pv a prior ms
      | _ -> False

let rec split_flight = function
  | [] -> [], []
  | (T m h)::t -> if eoflight m then [T m h], t else
		let (x,y) = split_flight t in
		if (x <> []) then (T m h)::x,y else x, (T m h)::y

val receive: #pv:protocolVersion -> #a:Hashing.alg -> l:log -> bytes -> ST (option (list (tagged_msg pv a)))
  (requires (fun h -> (sel h l.state).hash_alg == a /\ (sel h l.state).pv == pv))
  (ensures (fun h0 o h1 ->
    let t0 = transcriptT h0 l in
    let t1 = transcriptT h1 l in
    match o with
    | Some tl -> tags pv a t0 tl /\ writing h1 l
    | None -> t1 == t0 ))
let receive #pv #a (LOG #reg st) mb =
  let (LOG_ST pv ha kex dh l b acc) = !st in
  let b = {b with hs_incoming = b.hs_incoming @| mb} in
  match parseHashHandshakeMessages pv ha kex b.hs_incoming acc with
  | Error z -> None
  | Correct(r,acc,l') ->
       let p = b.hs_incoming_parsed @ l' in
       let (x,y) = split_flight p in
       let l = l @ l' in
       let b = {b with hs_incoming = r;
		       hs_incoming_parsed = y} in
       st := LOG_ST pv ha kex dh l b acc;
       Some x



//16-06-01 handshake state-machine transitions; could separate between C and S.

(*
val recv_fragment: s:hs -> #i:id -> message i -> ST incoming
  (requires (hs_inv s))
  (ensures (recv_ensures s))
let recv_fragment hs #i f =
    let (| rg,rb |) = f in
    let b =
      if hs_debug then
        IO.debug_print_string ("   ***** RAW "^(print_bytes rb)^"\n")
      else false in
    let (HS #r0 r res cfg id lgref hsref) = hs in
    let b = !(hsref.hs_buffers).hs_incoming in
    let b = b @| rb in
    let pv,kex,res =
      (match !(hsref.hs_nego) with
       | None -> None, None, None
       | Some n -> Some n.n_protocol_version, Some n.n_kexAlg, Some n.n_resume) in
    match parseHandshakeMessages pv kex b with
    | Error (ad, s) ->
      let _ =
        if hs_debug then
          IO.debug_print_string ("Failed to parse message: "^(string_of_ad ad)^": "^s^"\n")
        else false in
      InError (ad,s)
    | Correct(r,hsl) ->
       let hsl = List.Tot.append !(hsref.hs_buffers).hs_incoming_parsed hsl in
       hsref.hs_buffers := {!(hsref.hs_buffers) with hs_incoming = r; hs_incoming_parsed = hsl};
      let b =
        if hs_debug then
          print_hsl hsl
        else false in
      (match !(hsref.hs_state),hsl with
       | C (C_Idle ri), _ -> InError(AD_unexpected_message, "Client hasn't sent hello yet")
       | C (C_HelloSent ri ch), (ServerHello(sh),l)::hsl
	 when (sh.sh_protocol_version <> TLS_1p3 || hsl = []) ->
           let _ =
            if hs_debug then
              IO.debug_print_string "Processing client hello...\n"
            else false in
	   hsref.hs_buffers := {!(hsref.hs_buffers) with hs_incoming_parsed = hsl};
	   client_handle_server_hello hs [(ServerHello(sh),l)]
       | C (C_HelloReceived n), (Certificate(c),l)::
			          (ServerKeyExchange(ske),l')::
				  (ServerHelloDone,l'')::
				  hsl
	 when (Some? pv && pv <> Some TLS_1p3 && res = Some false &&
	       (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
	   hsref.hs_buffers = {!(hsref.hs_buffers) with hs_incoming_parsed = hsl};
			   client_handle_server_hello_done hs
			   [(Certificate(c),l) ;
			   (ServerKeyExchange(ske),l') ;
			   (ServerHelloDone,l'')]
			   []
       | C (C_HelloReceived n), (Certificate(c),l)::
			          (ServerKeyExchange(ske),l')::
			          (CertificateRequest(cr),l'')::
				  (ServerHelloDone,l''')::
				  hsl
	 when (Some? pv && pv <> Some TLS_1p3 && res = Some false &&
	       (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
	   hsref.hs_buffers = {!(hsref.hs_buffers) with hs_incoming_parsed = hsl};
			   client_handle_server_hello_done hs
			   [(Certificate(c),l) ;
			   (ServerKeyExchange(ske),l') ;
			   (ServerHelloDone,l''')]
			   [(CertificateRequest(cr),l'')]

       | C (C_CCSReceived n cv), (Finished(f),l)::hsl
       	 when (Some? pv && pv <> Some TLS_1p3) ->
	   hsref.hs_buffers = {!(hsref.hs_buffers) with hs_incoming_parsed = hsl};
			   client_handle_server_finished hs
			   [(Finished(f),l)]

       | C (C_HelloReceived n), (EncryptedExtensions(ee),l1)::
			          (Certificate(c),l2)::
			          (CertificateVerify(cv),l3)::
				  (Finished(f),l4)::
				  []
	 when (Some? pv && pv = Some TLS_1p3 &&
	       (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
	   hsref.hs_buffers = {!(hsref.hs_buffers) with hs_incoming_parsed = []};
			   client_handle_server_finished_13 hs
			   [(EncryptedExtensions(ee),l1);
			   (Certificate(c),l2) ;
			   (CertificateVerify(cv),l3) ;
			   (Finished(f),l4)]
       | C (C_HelloReceived n), (EncryptedExtensions(ee),l1)::
			          (CertificateRequest(cr),ll)::
			          (Certificate(c),l2)::
			          (CertificateVerify(cv),l3)::
				  (Finished(f),l4)::
				  []
	 when (Some? pv && pv = Some TLS_1p3 &&
	       (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
	   hsref.hs_buffers = {!(hsref.hs_buffers) with hs_incoming_parsed = []};
			   client_handle_server_finished_13 hs
			   [(EncryptedExtensions(ee),l1);
			   (CertificateRequest(cr),ll);
			   (Certificate(c),l2) ;
			   (CertificateVerify(cv),l3) ;
			   (Finished(f),l4)]

       | S (S_Idle ri), (ClientHello(ch),l)::hsl ->
	   hsref.hs_buffers = {!(hsref.hs_buffers) with hs_incoming_parsed = hsl};
			   server_handle_client_hello hs
			   [(ClientHello(ch),l)]
       | S (S_CCSReceived s), (Finished(f),l)::hsl
         when (Some? pv && pv <> Some TLS_1p3) ->
	   hsref.hs_buffers = {!(hsref.hs_buffers) with hs_incoming_parsed = hsl};
			   server_handle_client_finished hs
			   [(Finished(f),l)]

       | S (S_FinishedSent s), (Finished(f),l')::[]
         when (Some? pv && pv = Some TLS_1p3) ->
	   hsref.hs_buffers = {!(hsref.hs_buffers) with hs_incoming_parsed = []};
	   server_handle_client_finished_13 hs [(Finished(f),l')] []

       | S (S_FinishedSent s), (Certificate(c),l2)::
			       (CertificateVerify(cv),l3)::
			       (Finished(f),l4)::[]
         when (Some? pv && pv = Some TLS_1p3) ->
	   hsref.hs_buffers = {!(hsref.hs_buffers) with hs_incoming_parsed = []};
	   server_handle_client_finished_13 hs [(Finished(f),l4)] [(Certificate(c),l2);(CertificateVerify(cv),l3)]

       | C (C_Error e),_ -> InError e
       | S (S_Error e),_ -> InError e
       | _ , _ -> InAck false false)


val recv_ccs: s:hs -> ST incoming  // special case: CCS before 1p3; could merge with recv_fragment
  (requires (hs_inv s)) // could require pv <= 1p2
  (ensures (fun h0 result h1 ->
    recv_ensures s h0 result h1 /\
    (InError? result \/ result = InAck true false)
    ))
let recv_ccs hs =
    let b =
      if hs_debug then
        IO.debug_print_string ("CALL recv_ccs\n")
      else false in
    let (HS #r0 r res cfg id lgref hsref) = hs in
    let pv,kex =
      (match !(hsref.hs_nego) with
       | None -> None, None
       | Some n -> Some n.n_protocol_version, Some n.n_kexAlg) in
    (match !((hsref.hs_state),!(hsref.hs_buffers).hs_incoming_parsed) with
    | C (C_FinishedSent n cv), [] ->
       hsref.hs_buffers = {!(hsref.hs_buffers) with hs_incoming_parsed = []};
       client_handle_server_ccs hs []
    | C (C_FinishedSent n cv),
      (SessionTicket(st),l)::[] ->
       hsref.hs_buffers = {!(hsref.hs_buffers) with hs_incoming_parsed = []};
       client_handle_server_ccs hs
        [(SessionTicket(st),l)]
    | S (S_HelloDone n),
      (ClientKeyExchange(cke),l)::[]
      when (Some? pv && pv <> Some TLS_1p3 &&
            (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
      hsref.hs_buffers = {!(hsref.hs_buffers) with hs_incoming_parsed = []};
      server_handle_client_ccs hs
      [(ClientKeyExchange(cke),l)] []
    | S (S_HelloDone n),
      (Certificate(c),l)::
      (ClientKeyExchange(cke),l')::[]
      when (c.crt_chain = [] && Some? pv && pv <> Some TLS_1p3 &&
            (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
      hsref.hs_buffers = {!(hsref.hs_buffers) with hs_incoming_parsed = []};
      server_handle_client_ccs hs
      [(ClientKeyExchange(cke),l')] [(Certificate(c),l)]
    | S (S_HelloDone n),
      (Certificate(c),l)::
      (ClientKeyExchange(cke),l')::
      (CertificateVerify(cv),l'')::[]
      when (Some? pv && pv <> Some TLS_1p3 &&
            (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
      hsref.hs_buffers = {!(hsref.hs_buffers) with hs_incoming_parsed = []};
      server_handle_client_ccs hs
      [(ClientKeyExchange(cke),l')] [(Certificate(c),l);(CertificateVerify(cv),l'')]
    | C (C_Error e),_ -> InError e
    | S (S_Error e),_ -> InError e
    | _,_ -> InError(AD_unexpected_message, "ClientCCS received at wrong time"))

*)

(*

let print_log hs_log : Tot bool =
    let sl = List.Tot.map (HandshakeMessages.string_of_handshakeMessage) hs_log in
    let s = List.Tot.fold_left (fun x y -> x^", "^y) "" sl in
    IO.debug_print_string("LOG : " ^ s ^ "\n")

val append_log: l:log -> hm:hs_msg -> ST bytes
    (requires (fun h ->
	       let (|pv,hsl,lb|) = sel h l.logref in
	       validLog (hide_hs_log (List.Tot.append (reveal_hs_log hsl) [hm]))))
    (ensures (fun h0 _ h1 ->
      let LOG #r lr = l in
      modifies (Set.singleton r) h0 h1
      /\ modifies_rref r !{as_ref lr} h0.h h1.h))
let append_log (LOG #reg lref) hm =
    let (| pv, hsl, lb |) = !lref in
    let hsl' = FStar.List.Tot.append hsl [hm] in
    let pv = getLogVersion hsl' in
    let mb = handshakeMessageBytes pv hm in
    let lb' = lb @| mb in
    lref := (| pv, hsl', lb' |);
    mb

let op_At_At l h = append_log l h

val getMessages: log -> St hs_log
let getMessages (LOG #reg lref) =
    let (| pv, hsl, lb |) = !lref in hsl

val getBytes: log -> St bytes
let getBytes (LOG #reg lref) =
    let (| pv, hsl, lb |) = !lref in lb


type validLog_CH (l:hs_log) =
  (match l with
  | [ClientHello _] -> True
  | _ -> False)

let projectLog_CH (l:hs_log{validLog_CH l}) : logInfo_CH =
  match l with
  | [ClientHello ({
      ch_client_random = cr;
      ch_sessionID = sid;
      ch_extensions = Some el
    })] -> ({
      li_ch_cr = cr;
//      li_ch_ed_psk = empty_bytes;
//      li_ch_ed_ae = AEAD CoreCrypto.AES_128_GCM SHA256;
//      li_ch_ed_hash = SHA256;
      li_ch_psk = [];
    })

val getHash_CH : l:log -> h:hash_alg ->
  ST ( li:logInfo{LogInfo_CH? li} & tag h )
    (requires (fun h0 ->
      let lref = l.logref in
      let (| _, hsl, _ |) = sel h0 lref in validLog_CH hsl))
    (ensures (fun h0 (| li, hash |) h1 ->
	h1 = h0 /\ log_info li hash))

let getHash_CH (LOG #reg lref) (h:hash_alg) =
  let (| _, hsl, lb |) = !lref in
  let loginfo = projectLog_CH hsl in
  let tag = Hashing.compute h lb in
  (| LogInfo_CH loginfo, tag |)

type validLog_SH (l:hs_log) =
  (match l with
  | (ClientHello _) :: r ->
    (match r with
    | _ -> False)
  | _ -> False)

assume val checkLogSessionHash: hs_log -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> GTot bool
assume val checkLogClientFinished: hs_log -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> GTot bool
assume val checkLogServerFinished: hs_log -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> GTot bool
*)
