(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

(* Handshake protocol messages *)
module Handshake
open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found
open FStar.Set  

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSExtensions
open TLSInfo
open Range
open HandshakeMessages
open StatefulLHAE
open HSCrypto
			  
(* Negotiation: HELLO sub-module *)

type ri = (cVerifyData * sVerifyData) 
type b_log = bytes 
//or how about: 
//type log = list (m:bytes{exists ht d. m = messageBytes ht d})
type nego = {
     n_resume: bool;
     n_client_random: TLSInfo.random;
     n_server_random: TLSInfo.random;
     n_sessionID: sessionID;
     n_protocol_version: protocolVersion;
     n_kexAlg: TLSConstants.kexAlg;
     n_aeAlg: TLSConstants.aeAlg;
     n_sigAlg: option TLSConstants.sigAlg;
     n_cipher_suite: cipherSuite;
     n_compression: compression;
     n_extensions: negotiatedExtensions;
     n_scsv: list scsv_suite;
}                 

type hs_id = {
     id_cert: Cert.chain;
     id_sigalg: option Sig.alg;
}

type ake = {
     ake_server_id: option hs_id;
     ake_client_id: option hs_id;
     ake_pms: bytes;
     ake_session_hash: bytes;
     ake_ms: bytes;
}

type session = {
     session_nego: nego;
     session_ake: ake;
}     




type eph_s = option kex_s_priv
type eph_c = list kex_s_priv


val prepareClientHello: config -> option ri -> option sessionID -> ST (ch * b_log)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let prepareClientHello cfg ri sido : ch * b_log =
  let crand = Nonce.mkHelloRandom() in
  let sid = (match sido with | None -> empty_bytes | Some x -> x) in
  let ci = initConnection Client crand in
  let ext = prepareExtensions cfg ci ri in
  let ch = 
  {ch_protocol_version = cfg.maxVer;
   ch_client_random = crand;
   ch_sessionID = sid;
   ch_cipher_suites = cfg.ciphersuites;
   ch_raw_cipher_suites = None;
   ch_compressions = cfg.compressions;
   ch_extensions = Some ext;} in
   (ch,clientHelloBytes ch)

(* Is [pv1 >= pv2]? *)
val gte_pv: protocolVersion -> protocolVersion -> Tot bool
let gte_pv pv1 pv2 =
  match pv1 with
  | SSL_3p0 -> (match pv2 with | SSL_3p0 -> true | _ -> false)
  | TLS_1p0 -> (match pv2 with | SSL_3p0 | TLS_1p0 -> true | _ -> false)
  | TLS_1p1 -> (match pv2 with | SSL_3p0 | TLS_1p0 | TLS_1p1 -> true | _ -> false)
  | TLS_1p2 -> (match pv2 with | TLS_1p3 -> false | _ -> true)
  | TLS_1p3 -> true

(* Returns [c] if [c] is within the range of acceptable versions for [cfg],
 * [Error] otherwise. *)
val negotiateVersion: cfg:config -> c:protocolVersion -> Tot (result protocolVersion)
let negotiateVersion cfg c =
  if gte_pv c cfg.minVer && gte_pv cfg.maxVer c then Correct c
  else Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Protocol version negotiation failed")

val negotiate:list 'a -> list 'a -> Tot (option 'a)
let negotiate l1 l2 =
  List.Tot.tryFind (fun s -> List.Tot.existsb (fun c -> c = s) l1) l2

val negotiateCipherSuite: cfg:config -> pv:protocolVersion -> c:known_cipher_suites -> Tot (result (TLSConstants.kexAlg * option TLSConstants.sigAlg * TLSConstants.aeAlg * known_cipher_suite))
let negotiateCipherSuite cfg pv c =
  match negotiate c cfg.ciphersuites with
  | Some(CipherSuite kex sa ae) -> Correct(kex,sa,ae,CipherSuite kex sa ae)
  | None -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Cipher suite negotiation failed")

val negotiateCompression: cfg:config -> pv:protocolVersion -> c:list compression -> Tot (result compression)
let negotiateCompression cfg pv c =
  match negotiate c cfg.compressions with
  | Some(cs) -> Correct(cs)
  | None -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Compression negotiation failed")

// TODO : IMPLEMENT
val getCachedSession: cfg:config -> ch:ch -> ST (option session)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let getCachedSession cfg cg = None

// FIXME: TLS1.3
val prepareServerHello: config -> option ri -> ch -> b_log -> ST (result (bytes * nego * option ake * b_log))
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let prepareServerHello cfg ri ch i_log =
  let srand = Nonce.mkHelloRandom() in
  match getCachedSession cfg ch with
  | Some sentry -> 
    (match negotiateServerExtensions sentry.session_nego.n_protocol_version ch.ch_extensions ch.ch_cipher_suites cfg sentry.session_nego.n_cipher_suite ri true with
     | Error(z) -> Error(z)
     | Correct(sext,next) ->
       let shB = 
           serverHelloBytes (
            {sh_protocol_version = sentry.session_nego.n_protocol_version;
             sh_sessionID = Some (sentry.session_nego.n_sessionID);
             sh_server_random = srand;
             sh_cipher_suite = sentry.session_nego.n_cipher_suite;
             sh_compression = Some (sentry.session_nego.n_compression);
             sh_extensions = sext}) in
       let o_log = i_log @| shB in
       let o_nego = {sentry.session_nego with n_extensions = next} in
       Correct (shB,o_nego,Some sentry.session_ake,o_log))
  | None ->
    (match negotiateVersion cfg ch.ch_protocol_version with
    | Error(z) -> Error(z)
    | Correct(pv) ->
    match negotiateCipherSuite cfg pv ch.ch_cipher_suites with
    | Error(z) -> Error(z)
    | Correct(kex,sa,ae,cs) ->
    match negotiateCompression cfg pv ch.ch_compressions with
    | Error(z) -> Error(z)
    | Correct(cm) ->
    match negotiateServerExtensions pv ch.ch_extensions ch.ch_cipher_suites cfg cs ri false with
    | Error(z) -> Error(z)
    | Correct(sext,next) ->
  //  let sid = Nonce.random 32 in
    let sid = magic() in
    let shB = 
      serverHelloBytes (
      {sh_protocol_version = pv;
       sh_sessionID = Some sid;
       sh_server_random = srand;
       sh_cipher_suite = cs;
       sh_compression = Some cm;
       sh_extensions = sext}) in
    let nego = 
      {n_client_random = ch.ch_client_random;
       n_server_random = srand;
       n_sessionID = sid;
       n_protocol_version = pv;
       n_kexAlg = kex;
       n_sigAlg = sa;
       n_aeAlg  = ae;
       n_cipher_suite = cs;
       n_compression = cm;
       n_scsv = [];
       n_extensions = next;
       (* [getCachedSession] returned [None], so no session resumption *)
       n_resume = false} in
    let o_log = i_log @| shB in
    Correct (shB,nego,None,o_log))

(* Is this one of the special random values indicated by the RFC (6.3.1.1)? *)
val isSentinelRandomValue: protocolVersion -> protocolVersion -> TLSInfo.random -> Tot bool
let isSentinelRandomValue c_pv s_pv s_random =
  gte_pv c_pv TLS_1p3 && gte_pv TLS_1p2 s_pv && equalBytes (abytes "DOWNGRD\x01") s_random ||
  gte_pv c_pv TLS_1p2 && gte_pv TLS_1p1 s_pv && equalBytes (abytes "DOWNGRD\x00") s_random

(* If [true], then:
  - both the client and server versions are within the range specified by [cfg]
  - the server is not newer than the client
  - there is no undesired downgrade (as indicated by the special random values).
*)
val acceptableVersion: config -> ch -> protocolVersion -> TLSInfo.random -> Tot bool
let acceptableVersion cfg ch s_pv s_random =
  match negotiateVersion cfg ch.ch_protocol_version with
  | Correct c_pv -> 
    gte_pv c_pv s_pv && gte_pv s_pv cfg.minVer &&
    not (isSentinelRandomValue c_pv s_pv s_random)
  | Error _ ->
    false

(* If [true], then:
  - [s_cs] is has been offered previously;
  - [s_cs] is consistent with the [config];
  - TODO: [s_cs] is supported by the protocol version (e.g. no GCM with
    TLS<1.2).
*)
val acceptableCipherSuite: config -> ch -> protocolVersion -> known_cipher_suite -> Tot bool
let acceptableCipherSuite cfg ch s_pv s_cs =
  // JP: I would think the first line implies the second one?
  List.Tot.existsb (fun x -> x = s_cs) ch.ch_cipher_suites &&
  List.Tot.existsb (fun x -> x = s_cs) cfg.ciphersuites &&
  not (isAnonCipherSuite s_cs) || cfg.allowAnonCipherSuite
  

(* Our server implementation doesn't support compression, meaning [cmp] is
 always [NullCompression], so it's always a valid compression. *)
val acceptableCompression: config -> ch -> protocolVersion -> compression -> Tot bool
let acceptableCompression cfg ch pv cmp =
  true

val processServerHello: c:config -> option ri -> eph_c -> ch -> sh ->
                           ST (result (nego * option ake))
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let processServerHello cfg ri eph ch sh =
  let res = ch_is_resumption ch in
  // FIXME 1.3
  if not (acceptableVersion cfg ch sh.sh_protocol_version sh.sh_server_random) then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Protocol version negotiation")
  else if not (acceptableCipherSuite cfg ch sh.sh_protocol_version sh.sh_cipher_suite) then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Ciphersuite negotiation")
  else if not (acceptableCompression cfg ch sh.sh_protocol_version (Some.v sh.sh_compression)) then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Compression negotiation") 
  else
    match negotiateClientExtensions sh.sh_protocol_version cfg ch.ch_extensions sh.sh_extensions sh.sh_cipher_suite ri res with
    | Error z -> Error z
    | Correct next -> 
      if res then
        match getCachedSession cfg ch with
        | None -> Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Resumption disallowed")
        | Some sentry ->
          if sh.sh_protocol_version <> sentry.session_nego.n_protocol_version ||
            sh.sh_cipher_suite <> sentry.session_nego.n_cipher_suite ||
            Some.v sh.sh_compression <> sentry.session_nego.n_compression
          then
            Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Resumption params do not match cached session")
          else 
            let o_nego = {sentry.session_nego with n_extensions = next} in
            Correct (o_nego, (Some sentry.session_ake))
      else          
        match sh.sh_cipher_suite with
	| CipherSuite kex sa ae ->
        let o_nego = 
          {n_client_random = ch.ch_client_random;
           n_server_random = sh.sh_server_random;
           n_sessionID = Some.v sh.sh_sessionID;
           n_protocol_version = sh.sh_protocol_version;
           n_kexAlg = kex;
           n_aeAlg = ae;
	   n_sigAlg = sa;
           n_cipher_suite = sh.sh_cipher_suite;
           n_compression = Some.v sh.sh_compression;
	   n_scsv = [];
           n_extensions = next;
           n_resume = false } in
        Correct (o_nego, None)
	| _ -> Error (AD_decode_error, "ServerHello CipherSuite not a real ciphersuite")


(* Handshake API: TYPES, taken from FSTI *)

type clientState = 
  | C_Idle: option ri -> clientState
  | C_HelloSent: option ri -> eph_c -> ch -> clientState
  | C_HelloReceived: nego -> option ake  -> clientState
  | C_OutCCS: session -> cVerifyData -> clientState
  | C_FinishedSent: session -> cVerifyData -> clientState
  | C_CCSReceived: session -> cVerifyData -> clientState
  | C_Error: error -> clientState

type serverState = 
     | S_Idle : option ri -> serverState
     | S_HelloSent : nego -> option ake -> serverState
     | S_HelloDone : nego -> option ake -> eph_s -> serverState
     | S_CCSReceived : session -> serverState
     | S_OutCCS: session -> serverState
     | S_FinishedSent : session -> serverState
     | S_ResumeFinishedSent : session -> serverState
     | S_ZeroRTTReceived : session -> serverState
     | S_Error: error -> serverState

  
type hs_msg_bufs = {
     hs_incoming_parsed : list (hs_msg * bytes);
     hs_incoming: bytes;
     hs_outgoing: bytes;
}

let hs_msg_bufs_init() = {
     hs_incoming_parsed = [];
     hs_incoming = empty_bytes;
     hs_outgoing = empty_bytes;
}

type role_state = 
    | C of clientState
    | S of serverState
     
type handshake_state (r:role) = 
     {
       hs_nego: option nego;
       hs_ake: option ake;
       hs_buffers: hs_msg_bufs;
       hs_state: role_state;
       hs_log: bytes;
       hs_reader: int;
       hs_writer: int;
     }

val handshake_state_init: (ver:protocolVersion) -> (r:role) -> Tot (handshake_state r )
let handshake_state_init (ver:protocolVersion) (r:role) =
   {hs_nego = None;
    hs_ake = None;
    hs_log = empty_bytes;
    hs_reader = -1;
    hs_writer = -1;
    hs_buffers = hs_msg_bufs_init();
    hs_state =
        (match r with
    	| Client -> C (C_Idle None)
    	| Server -> S (S_Idle None)) }

type handshake = 
  | Fresh of sessionInfo
  | Resumed of abbrInfo * sessionInfo 
val hsId: handshake -> Tot TLSInfo.id
let hsId h = noId // Placeholder

type epoch (rgn:rid) (peer:rid) =
  | Epoch: h: handshake ->
           r: reader (peerId (hsId h)) ->
           w: writer (hsId h) -> epoch rgn peer

(* This following function needs to call PRF.deriveKeys correctly to get StatefulLHAE keys *)
assume val deriveEpoch: (r:rid) -> (p:rid) -> session -> ST (epoch r p)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

type epochs (r:rid) (p:rid) = es: seq (epoch r p)

type hs =
  | HS: #region: rid ->
        #peer: rid ->
        r:role ->
        resume: option (sid:sessionID { r = Client }) ->
        cfg:config ->
        id: random -> 
        log: rref region (epochs region peer) -> 
        state: rref region (handshake_state r) -> 
        hs


type outgoing = // by default the state changes but not the epochs
  | OutIdle
  | OutSome:     rg:frange_any -> rbytes rg -> outgoing   // send a HS fragment
  | OutCCS                                              // signal new epoch (sending a CCS fragment first, up to 1.2)
  | OutComplete: rg:frange_any -> rbytes rg -> outgoing   // signal completion of current epoch
  | OutError: error -> outgoing
  
type incoming = // the fragment is accepted, and...
  | InAck
  | InQuery: Cert.chain -> bool -> incoming
  | InCCS             // signal new epoch (only in TLS 1.3)
  | InComplete        // signal completion of current epoch
  | InError of error  // how underspecified should it be?


(* Handshake API: INTERNAL Callbacks, hidden from API *)

val client_send_client_hello: hs -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let client_send_client_hello (HS #r0 #peer r res cfg id lgref hsref) = 
  match (!hsref).hs_state with
  | C(C_Idle ri) -> 
    let (ch,l) = prepareClientHello cfg ri None in
    hsref := {!hsref with 
            hs_buffers = {(!hsref).hs_buffers with hs_outgoing = l};
	    hs_log = l;
	    hs_state = C(C_HelloSent ri [] ch)}
  
	    
val client_handle_server_hello: hs -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let client_handle_server_hello (HS #r0 #peer r res cfg id lgref hsref) msgs =
  match (!hsref).hs_state, msgs with
  | C(C_HelloSent ri eph_c ch),[(ServerHello(sh),l)] ->
   (match (processServerHello cfg ri eph_c ch sh) with
    | Error z -> InError z
    | Correct (n,a) -> 
      hsref := {!hsref with
	       hs_nego = Some n;
	       hs_ake = a;
	       hs_log = (!hsref).hs_log @| l;
	       hs_state = C(C_HelloReceived n a)};
      InAck)


val client_handle_server_hello_done: hs -> list (hs_msg * bytes) -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let client_handle_server_hello_done (HS #r0 #peer r res cfg id lgref hsref) msgs opt_msgs =
  match (!hsref).hs_state, msgs with
  | C(C_HelloReceived n None), 
    [(Certificate(c),l1);
     (ServerKeyExchange(ske),l2);
     (ServerHelloDone,l3)] when 
     (n.n_protocol_version <> TLS_1p3 && is_Some n.n_sigAlg &&
      (n.n_kexAlg = Kex_DHE || n.n_kexAlg = Kex_ECDHE)) -> 
     // Validate the server certificate chain before doing anything with other message
     // TODO add check for n.n_extensions.ne_signature_algorithms
     if Cert.validate_chain c.crt_chain n.n_sigAlg cfg.peer_name cfg.ca_file then
       let ske_tbs = kex_s_to_bytes ske.ske_kex_s in
       let ske_sig = ske.ske_sig in
       let cs_sigalg = Some.v n.n_sigAlg in
       let csr = (n.n_client_random @| n.n_server_random) in
       if Cert.verify_signature c.crt_chain n.n_protocol_version csr cs_sigalg n.n_extensions.ne_signature_algorithms ske_tbs ske_sig then
         (match ske.ske_kex_s with
         | KEX_S_DHE gy ->
           let gx, pms = dh_shared_secret2 gy in
           let cke = {cke_kex_c = kex_c_of_dh_key gx} in
           let ckeb = clientKeyExchangeBytes n.n_protocol_version cke in
           let pvcs = (n.n_protocol_version, n.n_cipher_suite) in

           let ms = TLSPRF.prf pvcs pms (utf8 "master secret") csr 48 in
           let ake = {ake_server_id = None;
	          ake_client_id = None;
		  ake_pms = pms;
		  ake_session_hash = empty_bytes;
		  ake_ms = ms} in
           let s = {session_nego = n; session_ake = ake} in

           (match opt_msgs with 
            | [] ->  
              let log = (!hsref).hs_log @| l1 @| l2 @| l3 @| ckeb in
              let vd = TLSPRF.verifyData pvcs ms Client log in 
              hsref := {!hsref with 
                hs_buffers = {(!hsref).hs_buffers with hs_outgoing = ckeb};
                hs_log = log;
                hs_state = C(C_OutCCS s vd)};
              InAck
            | [(CertificateRequest(cr),l)] ->
              let cc = {crt_chain = []} in // TODO
              let ccb = certificateBytes cc in
              let log = (!hsref).hs_log @| l1 @| l2 @| l @| l3 @| ccb @| ckeb in
              let vd = TLSPRF.verifyData pvcs ms Client log in 
              hsref := {!hsref with 
                hs_buffers = {(!hsref).hs_buffers with hs_outgoing = ccb @| ckeb};
                hs_log = log;
                hs_state = C(C_OutCCS s vd)};
              InAck)
         )
       // Signature verification failed
       else InError (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "failed to check SKE signature")
     // Certificate validation failed
     else InError (AD_certificate_unknown_fatal, perror __SOURCE_FILE__ __LINE__ "Certification validation failure") 
  

val client_send_client_finished: hs -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let client_send_client_finished (HS #r0 #peer r res cfg id lgref hsref) =
  match (!hsref).hs_state with
  | C(C_OutCCS s vd) ->
     let fin = {fin_vd = vd} in
     let finb = finishedBytes fin in
     hsref := {!hsref with 
            hs_buffers = {(!hsref).hs_buffers with hs_outgoing = finb};
	    hs_log = (!hsref).hs_log @| finb;
	    hs_state = C(C_FinishedSent s vd)}
  
  
val client_handle_server_ccs: hs -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let client_handle_server_ccs (HS #r0 #peer r res cfg id lgref hsref) msgs =
  match (!hsref).hs_state, msgs with
  | C(C_FinishedSent s vd),[(SessionTicket(stick),l)] ->
      hsref := {!hsref with
	       hs_log = (!hsref).hs_log @| l;
	       hs_state = C(C_CCSReceived s vd)};
      InAck

val client_handle_server_finished: hs -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let client_handle_server_finished (HS #r0 #peer r res cfg id lgref hsref) msgs =
  match (!hsref).hs_state, msgs with
  | C(C_CCSReceived s vd), [(Finished(f),l)] ->
    let n = s.session_nego in
    let ake = s.session_ake in
    let pvcs = (n.n_protocol_version, n.n_cipher_suite) in
    let svd = TLSPRF.verifyData pvcs ake.ake_ms Server (!hsref).hs_log in 
    if (equalBytes svd f.fin_vd) then 
       (hsref := {!hsref with
		 hs_log = (!hsref).hs_log @| l;
  		 hs_state = C(C_Idle (Some (vd,svd)))};
        InAck)
    else InError (AD_decode_error, "Finished MAC did not verify")
    

assume val client_handle_server_finished_13: hs -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))


val server_handle_client_hello: hs -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let server_handle_client_hello (HS #r0 #peer r res cfg id lgref hsref) msgs =
  match (!hsref).hs_state, msgs with
  | S(S_Idle ri),[(ClientHello(ch),l)] ->
    (match (prepareServerHello cfg ri ch l) with
     | Error z -> InError z
     | Correct (shb,n,a,ol) ->
       hsref := {!hsref with
               hs_buffers = {(!hsref).hs_buffers with hs_outgoing = shb};
	       hs_nego = Some n;
	       hs_ake = a;
	       hs_log = ol;
	       hs_state = S(S_HelloSent n a)};
       InAck)
    

val server_send_server_hello_done: hs -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let server_send_server_hello_done (HS #r0 #peer r res cfg id lgref hsref) =
  match (!hsref).hs_state with
  | S(S_HelloSent n a) 
    when (n.n_protocol_version <> TLS_1p3 &&
	 (n.n_kexAlg = Kex_DHE || n.n_kexAlg = Kex_ECDHE)) -> 
    let c = {crt_chain = get_signing_cert cfg.peer_name n.n_sigAlg []} in
    let cb = certificateBytes c in
    let gy = CommonDH.keygen CommonDH.default_group in
    let kex_s = KEX_S_DHE gy in
    let sv = kex_s_to_bytes kex_s in
    (match (cert_sign c.crt_chain n.n_sigAlg [] sv) with
    | Correct signature -> 
       let ske = {ske_kex_s = kex_s; ske_sig = signature} in
       let skeb = serverKeyExchangeBytes ske in
       let shd = serverHelloDoneBytes in
       let nl = cb @| skeb @| shd in
	  hsref := {!hsref with
		 hs_buffers = {(!hsref).hs_buffers with hs_outgoing = nl};
		 hs_log = (!hsref).hs_log @| nl;
		 hs_state = S(S_HelloDone n None None)}
    | Error e -> 
	  hsref := {!hsref with
		 hs_state = S(S_Error e)})


assume val server_handle_client_ccs: hs -> list (hs_msg * bytes) -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
assume val server_handle_client_finished: hs -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
assume val server_send_server_finished: hs -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))


assume val server_handle_client_finished_13: hs -> list (hs_msg * bytes) -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
assume val server_send_server_finished_13: hs -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
assume val server_send_server_finished_res: hs -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))



(* Handshake API: PUBLIC Functions, taken from FSTI *)

val version: s:hs -> ST protocolVersion
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let version (HS r res cfg id l st) =
    match (!st).hs_nego with
    | Some n -> n.n_protocol_version
    | None -> cfg.minVer

// JP: the outside has been checked against the fsti which had another
// definition (at the bottom of this file)
val iT_old:  s:hs -> rw:rw -> ST int
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let iT_old (HS r res cfg id l st) rw =
  match rw with 
  | Reader -> (!st).hs_reader
  | Writer -> (!st).hs_writer


val init: r0:rid -> peer:rid -> r: role -> 
       cfg:config -> resume: option (sid: sessionID { r = Client })  ->
       ST hs
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let init r0 peer r cfg res = 
    let id = Nonce.mkHelloRandom() in
    let lg = createEmpty in
    let lgref = ralloc r0 lg in
    let hs = handshake_state_init cfg.maxVer r in
    let hsref = ralloc r0 hs in
    HS #r0 #peer r res cfg id lgref hsref


val next_fragment: s:hs -> ST outgoing
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let rec next_fragment hs = 
    let (HS #r0 #peer r res cfg id lgref hsref) = hs in
    let pv,kex,res = 
      (match (!hsref).hs_nego with 
       | None -> None, None, None
       | Some n -> Some n.n_protocol_version, Some n.n_kexAlg, Some n.n_resume) in
    let b = (!hsref).hs_buffers.hs_outgoing in
    let l = length b in
    if (l > 0) then (
       hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_outgoing = empty_bytes}};
       OutSome (l,l) b) 
    else 
      (match (!hsref).hs_state with 
       | C (C_Error e) -> OutError e
       | S (S_Error e) -> OutError e
       | C (C_Idle ri) -> (client_send_client_hello hs; next_fragment hs)
       | C (C_OutCCS s cv) -> (client_send_client_finished hs; OutCCS)
       | S (S_HelloSent n a) when (is_Some pv && pv <> Some TLS_1p3 && res = Some false) -> server_send_server_hello_done hs; next_fragment hs
       | S (S_HelloSent n a) when (is_Some pv && pv <> Some TLS_1p3 && res = Some true) -> server_send_server_finished_res hs; next_fragment hs
       | S (S_HelloSent n a) when (is_Some pv && pv = Some TLS_1p3) -> server_send_server_finished_13 hs; next_fragment hs
       | S (S_OutCCS s) -> server_send_server_finished hs; OutCCS)



val parseHandshakeMessages : option protocolVersion -> option kexAlg -> buf:bytes -> Tot (result (rem:bytes * list (hs_msg * bytes)))
let rec parseHandshakeMessages pv kex buf =
    match parseMessage buf with
    | Error z -> Error z
    | Correct(None) -> Correct (buf,[])
    | Correct(Some (|rem,hstype,pl,to_log|)) ->   
      (match parseHandshakeMessage pv kex hstype pl with
       | Error z -> Error z 
       | Correct hsm -> 
             (match parseHandshakeMessages pv kex rem with
       	     | Error z -> Error z
       	     | Correct (r,hsl) -> Correct(r,(hsm,to_log)::hsl)))


val recv_fragment: s:hs -> rg:Range.range -> rbytes rg -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let recv_fragment hs (rg:Range.range) (rb:rbytes rg) = 
    let (HS #r0 #peer r res cfg id lgref hsref) = hs in
    let b = (!hsref).hs_buffers.hs_incoming in
    let b = b @| rb in
    let pv,kex,res = 
      (match (!hsref).hs_nego with 
       | None -> None, None, None
       | Some n -> Some n.n_protocol_version, Some n.n_kexAlg, Some n.n_resume) in
    match parseHandshakeMessages pv kex b with
    | Error z -> InError z
    | Correct(r,hsl) -> 
       hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming = r; hs_incoming_parsed = hsl}};
      (match (!hsref).hs_state,hsl with 
       | C (C_Idle ri), _ -> InError(AD_unexpected_message, "Client hasn't sent hello yet")
       | C (C_HelloSent ri eph ch), (ServerHello(sh),l)::hsl 
	 when (sh.sh_protocol_version <> TLS_1p3 || hsl = []) -> 
	   hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = hsl}};
	   client_handle_server_hello hs [(ServerHello(sh),l)]
       | C (C_HelloReceived n a), (Certificate(c),l)::
			          (ServerKeyExchange(ske),l')::
				  (ServerHelloDone,l'')::
				  hsl 
	 when (is_Some pv && pv <> Some TLS_1p3 && res = Some false &&
	       (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
	   hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = hsl}};
			   client_handle_server_hello_done hs 
			   [(Certificate(c),l) ;
			   (ServerKeyExchange(ske),l') ;
			   (ServerHelloDone,l'')]
			   []
       | C (C_HelloReceived n a), (Certificate(c),l)::
			          (ServerKeyExchange(ske),l')::
			          (CertificateRequest(cr),l'')::
				  (ServerHelloDone,l''')::
				  hsl 
	 when (is_Some pv && pv <> Some TLS_1p3 && res = Some false &&
	       (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
	   hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = hsl}};
			   client_handle_server_hello_done hs 
			   [(Certificate(c),l) ;
			   (ServerKeyExchange(ske),l') ;
			   (ServerHelloDone,l''')] 
			   [(CertificateRequest(cr),l'')]

       
       | C (C_CCSReceived s cv), (Finished(f),l)::hsl 
       	 when (is_Some pv && pv <> Some TLS_1p3) ->
	   hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = hsl}};
			   client_handle_server_finished hs 
			   [(Finished(f),l)]

       | C (C_HelloReceived n a), (EncryptedExtensions(ee),l1)::
			          (Certificate(c),l2)::
			          (CertificateVerify(cv),l3)::
				  (Finished(f),l4)::
				  [] 
	 when (is_Some pv && pv = Some TLS_1p3 && 
	       (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
	   hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = []}};
			   client_handle_server_finished_13 hs 
			   [(EncryptedExtensions(ee),l1);
			   (Certificate(c),l2) ;
			   (CertificateVerify(cv),l3) ;
			   (Finished(f),l4)]
       | C (C_HelloReceived n a), (EncryptedExtensions(ee),l1)::
			          (CertificateRequest(cr),ll)::
			          (Certificate(c),l2)::
			          (CertificateVerify(cv),l3)::
				  (Finished(f),l4)::
				  [] 
	 when (is_Some pv && pv = Some TLS_1p3 && 
	       (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
	   hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = []}};
			   client_handle_server_finished_13 hs 
			   [(EncryptedExtensions(ee),l1);
			   (CertificateRequest(cr),ll);
			   (Certificate(c),l2) ;			   
			   (CertificateVerify(cv),l3) ;
			   (Finished(f),l4)]
			   
       
       | S (S_Idle ri), (ClientHello(ch),l)::hsl -> 
	   hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = hsl}};
			   server_handle_client_hello hs
			   [(ClientHello(ch),l)]
       | S (S_CCSReceived s), (Finished(f),l)::hsl 
         when (is_Some pv && pv <> Some TLS_1p3) ->
	   hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = hsl}};
			   server_handle_client_finished hs
			   [(Finished(f),l)]

       | S (S_FinishedSent s), (ClientKeyExchange(cke),l)::
			       (Finished(f),l')::[]  
         when (is_Some pv && pv = Some TLS_1p3) ->
	   hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = []}};
	   server_handle_client_finished_13 hs [(ClientKeyExchange(cke),l);(Finished(f),l')] []

       | S (S_FinishedSent s), (ClientKeyExchange(cke),l1)::
			       (Certificate(c),l2)::
			       (Finished(f),l3)::[]  
         when (is_Some pv && pv = Some TLS_1p3 && c.crt_chain = []) ->
	   hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = []}};
	   server_handle_client_finished_13 hs [(ClientKeyExchange(cke),l1);(Finished(f),l3)] [(Certificate(c),l2)]

       | S (S_FinishedSent s), (ClientKeyExchange(cke),l1)::
			       (Certificate(c),l2)::
			       (CertificateVerify(cv),l3)::
			       (Finished(f),l4)::[]  
         when (is_Some pv && pv = Some TLS_1p3) ->
	   hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = []}};
	   server_handle_client_finished_13 hs [(ClientKeyExchange(cke),l1);(Finished(f),l4)] [(Certificate(c),l2);(CertificateVerify(cv),l3)]

       | C (C_Error e),_ -> InError e
       | S (S_Error e),_ -> InError e
       | _ , _ -> InAck)
	   

val recv_ccs: s:hs -> ST incoming  // special case: CCS before 1p3 
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let recv_ccs hs = 
    let (HS #r0 #peer r res cfg id lgref hsref) = hs in
    let pv,kex = 
      (match (!hsref).hs_nego with 
       | None -> None, None
       | Some n -> Some n.n_protocol_version, Some n.n_kexAlg) in
    (match ((!hsref).hs_state,(!hsref).hs_buffers.hs_incoming_parsed) with 
    | C (C_FinishedSent s cv), 
      (SessionTicket(st),l)::[] ->
       hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = []}};
       client_handle_server_ccs hs 
        [(SessionTicket(st),l)]
    | S (S_HelloDone n i eph), 
      (ClientKeyExchange(cke),l)::[] 
      when (is_Some pv && pv <> Some TLS_1p3 && 
            (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
      hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = []}};
      server_handle_client_ccs hs
      [(ClientKeyExchange(cke),l)] []
    | S (S_HelloDone n i eph), 
      (Certificate(c),l)::
      (ClientKeyExchange(cke),l')::[] 
      when (c.crt_chain = [] && is_Some pv && pv <> Some TLS_1p3 && 
            (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
      hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = []}};
      server_handle_client_ccs hs
      [(ClientKeyExchange(cke),l')] [(Certificate(c),l)]
    | S (S_HelloDone n i eph), 
      (Certificate(c),l)::
      (ClientKeyExchange(cke),l')::
      (CertificateVerify(cv),l'')::[]
      when (is_Some pv && pv <> Some TLS_1p3 && 
            (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
      hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = []}};
      server_handle_client_ccs hs
      [(ClientKeyExchange(cke),l')] [(Certificate(c),l);(CertificateVerify(cv),l'')]
    | C (C_Error e),_ -> InError e
    | S (S_Error e),_ -> InError e
    | _,_ -> InError(AD_unexpected_message, "ClientCCS received at wrong time"))


assume val authorize: s:hs -> Cert.chain -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))


(* These definitions are here so that we can use Handshake.fst instead of
 * Handshake.fsti. TODO: they are meant to go away once we merge Handshake.fsti
 * into Handshake.fst *)
assume type hs_footprint_inv (s: hs) (h: HyperHeap.t): Type0
assume type hs_inv (s: hs) (h: HyperHeap.t): Type0
assume type epochs_footprint (#region:rid) (#peer:rid) (es: seq (epoch region peer)): Type0
assume val regions: #p:rid -> #q:rid -> e:epoch p q -> Tot (Set.set HyperHeap.rid)
assume type modifies_internal (h1: HyperHeap.t) (s: hs) (h2: HyperHeap.t): Type0

// Idle client starts a full handshake on the current connection
assume val rehandshake: s:hs -> config -> ST bool
  (requires (fun h -> hs_inv s h /\ HS.r s = Client))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))

// Idle client starts an abbreviated handshake resuming the current session
assume val rekey: s:hs -> config -> ST bool
  (requires (fun h -> hs_inv s h /\ HS.r s = Client))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))

// (Idle) Server requests an handshake
assume val request: s:hs -> config -> ST bool
  (requires (fun h -> hs_inv s h /\ HS.r s = Server))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))

assume val invalidateSession: s:hs -> ST unit
  (requires (hs_inv s))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1)) // underspecified

let logIndex (#t:Type) (log: seq t) = n:int { -1 <= n /\ n < Seq.length log }
// The return type is simplified for the sake of extraction.
assume val iT: s:hs -> rw:rw -> h:HyperHeap.t -> Tot int
assume val i: s:hs -> rw:rw -> St int
