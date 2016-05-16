(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

(* Handshake protocol messages *)
module Handshake
open TLSExtensions //the other opens are in the .fsti
open CoreCrypto
open HSCrypto
open HandshakeLog
module HH = FStar.HyperHeap

let hsId h = noId // Placeholder

(* Negotiation: HELLO sub-module *)

let ri = (cVerifyData * sVerifyData) 



let prepareClientHello cfg ks log ri sido =
  let cr = KeySchedule.ks_client_random ks in
  let kp = 
     (match cfg.maxVer with
      | TLS_1p3 -> 
         let gxl = KeySchedule.ks_client_13_init_1rtt ks cfg.namedGroups in 
	 Some (ClientKeyShare gxl)
      | _ -> 
      	 let _ = KeySchedule.ks_client_init_12 ks in 
	 None) in
  let sid = (match sido with | None -> empty_bytes | Some x -> x) in
  let ci = initConnection Client cr in
  let ext = prepareExtensions cfg ci ri kp in
  let ch = 
  {ch_protocol_version = cfg.maxVer;
   ch_client_random = cr;
   ch_sessionID = sid;
   ch_cipher_suites = cfg.ciphersuites;
   ch_raw_cipher_suites = None;
   ch_compressions = [NullCompression];
   ch_extensions = Some ext;} in
  let chb = log @@ (ClientHello ch) in
  (ClientHello ch, chb)

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
  else if gte_pv c cfg.maxVer then Correct cfg.maxVer
  else Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Protocol version negotiation failed")

val negotiate:list 'a -> list 'a -> Tot (option 'a)
let negotiate l1 l2 =
  List.Tot.tryFind (fun s -> List.Tot.existsb (fun c -> c = s) l1) l2

val negotiateCipherSuite: cfg:config -> pv:protocolVersion -> c:valid_cipher_suites -> Tot (result (TLSConstants.kexAlg * option TLSConstants.sigAlg * TLSConstants.aeAlg * valid_cipher_suite))
let negotiateCipherSuite cfg pv c =
  match negotiate c cfg.ciphersuites with
  | Some(CipherSuite kex sa ae) -> Correct(kex,sa,ae,CipherSuite kex sa ae)
  | None -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Cipher suite negotiation failed")

// TODO : IMPLEMENT
val getCachedSession: cfg:config -> ch:ch -> ST (option session)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let getCachedSession cfg cg = None

val negotiateGroupKeyShare: cfg:config -> protocolVersion -> kexAlg -> exts:option (list extension) -> Tot (result (namedGroup * option bytes))
let rec negotiateGroupKeyShare cfg pv kex exts = 
    match pv,kex,exts with
    | TLS_1p3, Kex_ECDHE, Some (E_keyShare (ClientKeyShare ((gn,gxb)::_)) :: _) ->
      Correct (gn,Some gxb)
    | TLS_1p3,_, Some (h::t) -> negotiateGroupKeyShare cfg pv kex (Some t)
    | TLS_1p2, Kex_ECDHE, _ -> Correct (SEC CoreCrypto.ECC_P256, None) 
    | _ -> Error(AD_decode_error, "no supported group or key share extension found")
    

// FIXME: TLS1.3
let prepareServerHello cfg ks log ri (ClientHello ch,_) =
  match negotiateVersion cfg ch.ch_protocol_version with
    | Error(z) -> Error(z)
    | Correct(pv) ->
  match negotiateCipherSuite cfg pv ch.ch_cipher_suites with
    | Error(z) -> Error(z)
    | Correct(kex,sa,ae,cs) ->
  match negotiateGroupKeyShare cfg pv kex ch.ch_extensions with
    | Error(z) -> Error(z)
    | Correct(gn,gxo) ->
  let srand = KeySchedule.ks_server_random ks in
  let ksl = 
    (match pv,gxo with
     | TLS_1p3,Some gxb -> 
       let gyb = KeySchedule.ks_server_13_1rtt_init ks ch.ch_client_random cs gn gxb in
       (Some (ServerKeyShare (gn,gyb)))
    | _ -> None) in
  match negotiateServerExtensions pv ch.ch_extensions ch.ch_cipher_suites cfg cs ri ksl false with
    | Error(z) -> Error(z)
    | Correct(sext,next) ->
    let sid = CoreCrypto.random 32 in
    let comp = match ch.ch_compressions with
      | [] -> None
      | _ -> Some NullCompression in
    let sh = 
      {sh_protocol_version = pv;
       sh_sessionID = Some sid;
       sh_server_random = srand;
       sh_cipher_suite = cs;
       sh_compression = comp;
       sh_extensions = sext} in
    let nego = 
      {n_client_random = ch.ch_client_random;
       n_server_random = srand;
       n_sessionID = Some sid;
       n_protocol_version = pv;
       n_kexAlg = kex;
       n_sigAlg = sa;
       n_aeAlg  = ae;
       n_cipher_suite = cs;
       n_compression = comp;
       n_dh_group = Some gn;
       n_scsv = [];
       n_extensions = next;
       (* [getCachedSession] returned [None], so no session resumption *)
       n_resume = false} in
    let _ = log @@ (ClientHello ch) in
    let shb = log @@ (ServerHello sh) in
    Correct (nego,(ServerHello sh,shb))

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
val acceptableCipherSuite: config -> ch -> protocolVersion -> valid_cipher_suite -> Tot bool
let acceptableCipherSuite cfg ch s_pv s_cs =
  // JP: I would think the first line implies the second one?
  List.Tot.existsb (fun x -> x = s_cs) ch.ch_cipher_suites &&
  List.Tot.existsb (fun x -> x = s_cs) cfg.ciphersuites &&
  not (isAnonCipherSuite s_cs) || cfg.allowAnonCipherSuite
  
let processServerHello cfg ks log ri ch (ServerHello sh,_) =
  let _ = log @@ (ServerHello sh) in
  // Assuming no resumption; TODO: add it 
  if not (acceptableVersion cfg ch sh.sh_protocol_version sh.sh_server_random) then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Protocol version negotiation")
  else  if not (acceptableCipherSuite cfg ch sh.sh_protocol_version sh.sh_cipher_suite) then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Ciphersuite negotiation")
  else
  let resume = false in
  match negotiateClientExtensions sh.sh_protocol_version cfg ch.ch_extensions sh.sh_extensions sh.sh_cipher_suite ri resume with
    | Error z -> Error z
    | Correct next -> 
        match sh.sh_cipher_suite with
	| CipherSuite kex sa ae ->
        let o_nego = 
          {n_client_random = ch.ch_client_random;
           n_server_random = sh.sh_server_random;
           n_sessionID = sh.sh_sessionID;
           n_protocol_version = sh.sh_protocol_version;
           n_kexAlg = kex;
           n_aeAlg = ae;
	   n_sigAlg = sa;
           n_cipher_suite = sh.sh_cipher_suite;
	   n_dh_group = None;
           n_compression = sh.sh_compression;
	   n_scsv = [];
           n_extensions = next;
           n_resume = false } in
	   (match sh.sh_protocol_version, kex, next.ne_keyShare with
	    | TLS_1p3, Kex_DHE, Some (gn,gyb) 
	    | TLS_1p3, Kex_ECDHE, Some (gn,gyb) -> Correct (o_nego)
            | _ -> Correct (o_nego))
	| _ -> Error (AD_decode_error, "ServerHello CipherSuite not a real ciphersuite")


(* Handshake API: TYPES, taken from FSTI *)

type clientState = 
  | C_Idle: option ri -> clientState
  | C_HelloSent: option ri -> ch -> clientState
  | C_HelloReceived: nego -> clientState
  | C_OutCCS: nego -> clientState
  | C_FinishedSent: nego -> cVerifyData -> clientState
  | C_CCSReceived: nego -> cVerifyData -> clientState
  | C_Error: error -> clientState

type serverState = 
     | S_Idle : option ri -> serverState
     | S_HelloSent : nego -> serverState
     | S_HelloDone : nego -> serverState
     | S_CCSReceived : nego -> serverState
     | S_OutCCS: nego -> serverState
     | S_FinishedSent : nego -> serverState
     | S_ResumeFinishedSent : nego -> serverState
     | S_ZeroRTTReceived : nego -> serverState
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
     
type handshake_state' (r:role) =
     {
       hs_state: role_state;
       hs_nego: option nego;
       hs_log: HandshakeLog.log;
       hs_ks: KeySchedule.ks;

       hs_buffers: hs_msg_bufs;
       hs_reader: int;
       hs_writer: int;
     }

//NS: needed this renaming trick for the .fsti
let handshake_state r = handshake_state' r

//to match the external interface
//let handshake_state (r:role) = handshake_state' r
let iT0 s rw st = -1 //TODO:Implement!
let i s rw = Platform.Error.unexpected "i: not yet implemented" //TODO:Implement

val handshake_state_init: (cfg:TLSInfo.config) -> (r:role) -> (reg:rid) -> ST (handshake_state r)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let handshake_state_init cfg (r:role) (reg:rid) =
   let ks, nonce = KeySchedule.create #reg r in
   {hs_nego = None;
    hs_log = HandshakeLog.create #reg;
    hs_ks  = ks;
    hs_reader = -1;
    hs_writer = -1;
    hs_buffers = hs_msg_bufs_init();
    hs_state =
        (match r with
    	| Client -> C (C_Idle None)
    	| Server -> S (S_Idle None)) }

//Defined in the .fsti
//type handshake
//type epoch 
//type epochs
//type hs
//type outgoing
//type incoming

(* This following function needs to call PRF.deriveKeys correctly to get StatefulLHAE keys *)
assume val deriveEpoch: (r:rid) -> (n:TLSInfo.random) -> session -> ST (epoch r n)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

(* Handshake API: INTERNAL Callbacks, hidden from API *)

val client_send_client_hello: hs -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let client_send_client_hello (HS #r0 r res cfg id lgref hsref) = 
  match (!hsref).hs_state with
  | C(C_Idle ri) -> 
    let (ClientHello ch,chb) = prepareClientHello cfg (!hsref).hs_ks (!hsref).hs_log ri None in
    hsref := {!hsref with 
            hs_buffers = {(!hsref).hs_buffers with hs_outgoing = chb};
	    hs_state = C(C_HelloSent ri ch)}
  
	    
val client_handle_server_hello: hs -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let client_handle_server_hello (HS #r0 r res cfg id lgref hsref) msgs =
  match (!hsref).hs_state, msgs with
  | C(C_HelloSent ri ch),[(ServerHello(sh),l)] ->
   (match (processServerHello cfg (!hsref).hs_ks (!hsref).hs_log ri ch (ServerHello sh,l)) with
    | Error z -> InError z
    | Correct (n) -> 
      hsref := {!hsref with
	       hs_nego = Some n;
	       hs_state = C(C_HelloReceived n)};
      InAck)


let processServerHelloDone cfg n ks log msgs opt_msgs =
  match msgs with
  | [(Certificate(c),_); (ServerKeyExchange(ske),_); (ServerHelloDone,_)] when 
     (n.n_protocol_version <> TLS_1p3 && is_Some n.n_sigAlg &&
      (n.n_kexAlg = Kex_DHE || n.n_kexAlg = Kex_ECDHE)) -> 
     // Validate the server certificate chain before doing anything with other message
     // TODO add check for n.n_extensions.ne_signature_algorithms
     if Cert.validate_chain c.crt_chain n.n_sigAlg cfg.peer_name cfg.ca_file then
       let ske_tbs = kex_s_to_bytes ske.ske_kex_s in
       let ske_sig = ske.ske_sig in
       let cs_sigalg = Some.v n.n_sigAlg in
       let csr = (n.n_client_random @| n.n_server_random) in
       let ems = n.n_extensions.ne_extended_ms in

       let valid = Cert.verify_signature c.crt_chain n.n_protocol_version Server (Some csr) 
          cs_sigalg n.n_extensions.ne_signature_algorithms ske_tbs ske_sig in
       let _ = IO.debug_print_string("Signature validation status = "^(if valid then "OK" else "FAIL")^"\n") in
       if true then // TODO: SIG VALIDATION CURRENTLY FAILS; this should be "if valid then"
         (match ske.ske_kex_s with
         | KEX_S_DHE gy ->
           let gx = KeySchedule.ks_client_12_full_dh ks n.n_server_random n.n_protocol_version 
	            n.n_cipher_suite n.n_extensions.ne_extended_ms gy in 
           let cke = {cke_kex_c = kex_c_of_dh_key gx} in
            (match opt_msgs with 
            | [] -> 
	      let _ = log @@ Certificate(c) in
	      let _ = log @@ ServerKeyExchange(ske) in
	      let _ = log @@ ServerHelloDone in
	      let b = log @@ ClientKeyExchange cke in
	      let lb = HandshakeLog.getBytes log in
	      if ems then KeySchedule.ks_client_12_set_session_hash ks lb;
	      Correct [(ClientKeyExchange cke,b)]
            | [(CertificateRequest(cr),_)] ->
              let cc = {crt_chain = []} in // TODO
	      let _ = log @@ Certificate(c) in
	      let _ = log @@ ServerKeyExchange(ske) in
	      let _ = log @@ CertificateRequest(cr) in
	      let _ = log @@ ServerHelloDone in
	      let b1 = log @@ ClientKeyExchange cke in	
	      let lb = HandshakeLog.getBytes log in
	      if ems then KeySchedule.ks_client_12_set_session_hash ks lb;
	      let b2 = log @@ Certificate(cc) in
      	    Correct [ClientKeyExchange cke,b1; Certificate cc,b2])
	  | _ -> Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "only support ECDHE/DHE SKE")
         )
       // Signature verification failed
       else Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "failed to check SKE signature")
     // Certificate validation failed
     else Error (AD_certificate_unknown_fatal, perror __SOURCE_FILE__ __LINE__ "Certificate validation failure") 


val client_handle_server_hello_done: hs -> list (hs_msg * bytes) -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let client_handle_server_hello_done (HS #r0 r res cfg id lgref hsref) msgs opt_msgs =
  match (!hsref).hs_state with
  | C(C_HelloReceived n) when 
     (n.n_protocol_version <> TLS_1p3 && is_Some n.n_sigAlg &&
      (n.n_kexAlg = Kex_DHE || n.n_kexAlg = Kex_ECDHE)) -> 
     (match processServerHelloDone cfg n (!hsref).hs_ks (!hsref).hs_log msgs opt_msgs with
      | Correct [(ClientKeyExchange(cke),b1)] ->
             hsref := {!hsref with 
                hs_buffers = {(!hsref).hs_buffers with hs_outgoing = b1};
                hs_state = C(C_OutCCS n)};
              InAck
      | Correct [(ClientKeyExchange(cke),b1);(Certificate(cc),b2)] ->
             hsref := {!hsref with 
                hs_buffers = {(!hsref).hs_buffers with hs_outgoing = b1 @| b2};
                hs_state = C(C_OutCCS n)};
              InAck
      | Error (x,y) -> InError(x,y))
   | _ -> InError (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "unexpected state")

let prepareClientFinished ks log = 
    let lb = HandshakeLog.getBytes log in
    let fin = {fin_vd = KeySchedule.ks_client_12_client_verify_data ks lb} in
    let finb = log @@ (Finished fin) in
    (Finished fin, finb)

val client_send_client_finished: hs -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let client_send_client_finished (HS #r0 r res cfg id lgref hsref) =
  let hs = !hsref in
  match hs.hs_state with
  | C(C_OutCCS n) ->
     let (Finished fin,finb) = prepareClientFinished (!hsref).hs_ks (!hsref).hs_log in
     hsref := {!hsref with 
            hs_buffers = {(!hsref).hs_buffers with hs_outgoing = finb};
	    hs_state = C(C_FinishedSent n fin.fin_vd)}
  
  
val client_handle_server_ccs: hs -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let client_handle_server_ccs (HS #r0 r res cfg id lgref hsref) msgs =
  match (!hsref).hs_state, msgs with
  | C(C_FinishedSent n vd),[(SessionTicket(stick),l)] ->
      let _ = (!hsref).hs_log @@ SessionTicket(stick) in
      hsref := {!hsref with
	       hs_state = C(C_CCSReceived n vd)};
      InAck

let processServerFinished ks log (m,l) =
   match m with
   | Finished(f) ->
     let lb = HandshakeLog.getBytes log in
     let svd = KeySchedule.ks_client_12_server_verify_data ks lb in
     if (equalBytes svd f.fin_vd) then 
     	let _ = log @@ (Finished(f)) in
	Correct svd
     else Error (AD_decode_error, "Finished MAC did not verify")
   | _ -> Error (AD_decode_error, "Unexpected state")

val client_handle_server_finished: hs -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let client_handle_server_finished (HS #r0 r res cfg id lgref hsref) msgs =
  match (!hsref).hs_state, msgs with
  | C(C_CCSReceived n vd), [(Finished(f),l)] ->
   (match processServerFinished (!hsref).hs_ks (!hsref).hs_log (Finished f,l) with
    | Error z -> InError z
    | Correct svd -> 
       hsref := {!hsref with
  		 hs_state = C(C_Idle (Some (vd,svd)))};
       InAck)
    

assume val client_handle_server_finished_13: hs -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))


val server_handle_client_hello: hs -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let server_handle_client_hello (HS #r0 r res cfg id lgref hsref) msgs =
  match (!hsref).hs_state, msgs with
  | S(S_Idle ri),[(ClientHello(ch),l)] ->
    (match (prepareServerHello cfg (!hsref).hs_ks (!hsref).hs_log ri (ClientHello ch,l)) with
     | Error z -> InError z
     | Correct (n,(sh,shb)) ->
       hsref := {!hsref with
               hs_buffers = {(!hsref).hs_buffers with hs_outgoing = shb};
	       hs_nego = Some n;
	       hs_state = S(S_HelloSent n)};
       InAck)
    

val server_send_server_hello_done: hs -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let server_send_server_hello_done (HS #r0 r res cfg id lgref hsref) =
  match (!hsref).hs_state with
  | S(S_HelloSent n) 
    when (n.n_protocol_version <> TLS_1p3 &&
	 (n.n_kexAlg = Kex_DHE || n.n_kexAlg = Kex_ECDHE)) ->
    (match Cert.lookup_server_chain cfg.cert_chain_file cfg.private_key_file n.n_protocol_version n.n_sigAlg n.n_extensions.ne_signature_algorithms with
    | Correct (chain, csk) -> 
      let c = {crt_chain = chain} in
      let cb = certificateBytes n.n_protocol_version c in
      let gy = CommonDH.keygen CommonDH.default_group in
      let kex_s = KEX_S_DHE gy in
      let sv = kex_s_to_bytes kex_s in
      let csr = n.n_client_random @| n.n_server_random in

      // Signature agility (following the broken rules of 7.4.1.4.1. in RFC5246
      let Some sa = n.n_sigAlg in
      let algs = match n.n_extensions.ne_signature_algorithms with
        | None -> [sa,Hash CoreCrypto.SHA1] | Some l -> l in
      let algs = List.Tot.filter (fun (s,_)->s=sa) algs in
      let alg = match algs with | h::_ -> h | [] -> (sa, Hash CoreCrypto.SHA1) in
      (match Cert.sign n.n_protocol_version Server (Some csr) csk alg sv with
      | Correct signature -> 
         let ske = {ske_kex_s = kex_s; ske_sig = signature} in
         let skeb = serverKeyExchangeBytes ske in
         let shd = serverHelloDoneBytes in
         let nl = cb @| skeb @| shd in
	    hsref := {!hsref with
		 hs_buffers = {(!hsref).hs_buffers with hs_outgoing = nl};
		 hs_log = (!hsref).hs_log (* @| nl *);
		 hs_state = S(S_HelloDone n)}
      | Error e -> 
	  hsref := {!hsref with hs_state = S(S_Error e)})
    | Error e ->
        hsref := {!hsref with hs_state = S(S_Error e)})

assume val server_handle_client_ccs: hs -> list (hs_msg * bytes) -> list (hs_msg * bytes) -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

(*
let server_handle_client_ccs (HS #r0 r res cfg id lgref hsref)  msgs opt_msgs = 
  match (!hsref).hs_state, msgs with
  | S(S_HelloDone n),[(ClientKeyExchange(cke),l)] when 
     (n.n_protocol_version <> TLS_1p3 && 
      (n.n_kexAlg = Kex_DHE || n.n_kexAlg = Kex_ECDHE)) ->
      let pms = CommonDH.dh_initiator k 
*)

    
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

//val version: see .fsti
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

//val init: see .fsti
let init r0 r cfg res = 
    let id = Nonce.mkHelloRandom r r0 in //NS: should this really be Client?
    let lg = createEmpty in
    let lgref = ralloc r0 lg in
    let hs = handshake_state_init cfg r r0 in
    let hsref = ralloc r0 hs in
    HS #r0 r res cfg id lgref hsref

// Idle client starts a full handshake on the current connection
let rehandshake s c = Platform.Error.unexpected "rehandshake: not yet implemented"

// Idle client starts an abbreviated handshake resuming the current session
let rekey s c = Platform.Error.unexpected "rekey: not yet implemented"

// (Idle) Server requests an handshake
let request s c = Platform.Error.unexpected "request: not yet implemented"

let invalidateSession hs = Platform.Error.unexpected "invalidateSession: not yet implemented"

//val next_fragment: see .fsti
let rec next_fragment hs = 
    let (HS #r0 r res cfg id lgref hsref) = hs in
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
       | C (C_OutCCS n) -> (client_send_client_finished hs; OutCCS)
       | S (S_HelloSent n) when (is_Some pv && pv <> Some TLS_1p3 && res = Some false) -> server_send_server_hello_done hs; next_fragment hs
       | S (S_HelloSent n) when (is_Some pv && pv <> Some TLS_1p3 && res = Some true) -> server_send_server_finished_res hs; next_fragment hs
       | S (S_HelloSent n) when (is_Some pv && pv = Some TLS_1p3) -> server_send_server_finished_13 hs; next_fragment hs
       | S (S_OutCCS s) -> server_send_server_finished hs; OutCCS)



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


//val recv_fragment: see .fsti
let recv_fragment hs (rg:Range.range) (rb:rbytes rg) = 
    let (HS #r0 r res cfg id lgref hsref) = hs in
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
       | C (C_HelloSent ri ch), (ServerHello(sh),l)::hsl 
	 when (sh.sh_protocol_version <> TLS_1p3 || hsl = []) -> 
	   hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = hsl}};
	   client_handle_server_hello hs [(ServerHello(sh),l)]
       | C (C_HelloReceived n), (Certificate(c),l)::
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
       | C (C_HelloReceived n), (Certificate(c),l)::
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

       
       | C (C_CCSReceived n cv), (Finished(f),l)::hsl 
       	 when (is_Some pv && pv <> Some TLS_1p3) ->
	   hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = hsl}};
			   client_handle_server_finished hs 
			   [(Finished(f),l)]

       | C (C_HelloReceived n), (EncryptedExtensions(ee),l1)::
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
       | C (C_HelloReceived n), (EncryptedExtensions(ee),l1)::
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
	   

//val recv_ccs: see .fsti  // special case: CCS before 1p3  
let recv_ccs hs = 
    let (HS #r0 r res cfg id lgref hsref) = hs in
    let pv,kex = 
      (match (!hsref).hs_nego with 
       | None -> None, None
       | Some n -> Some n.n_protocol_version, Some n.n_kexAlg) in
    (match ((!hsref).hs_state,(!hsref).hs_buffers.hs_incoming_parsed) with 
    | C (C_FinishedSent n cv), 
      (SessionTicket(st),l)::[] ->
       hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = []}};
       client_handle_server_ccs hs 
        [(SessionTicket(st),l)]
    | S (S_HelloDone n), 
      (ClientKeyExchange(cke),l)::[] 
      when (is_Some pv && pv <> Some TLS_1p3 && 
            (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
      hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = []}};
      server_handle_client_ccs hs
      [(ClientKeyExchange(cke),l)] []
    | S (S_HelloDone n), 
      (Certificate(c),l)::
      (ClientKeyExchange(cke),l')::[] 
      when (c.crt_chain = [] && is_Some pv && pv <> Some TLS_1p3 && 
            (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
      hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming_parsed = []}};
      server_handle_client_ccs hs
      [(ClientKeyExchange(cke),l')] [(Certificate(c),l)]
    | S (S_HelloDone n), 
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


let authorize s ch = Platform.Error.unexpected "authorize: not yet implemented"
