(*--build-config
  options:--codegen-lib CoreCrypto --codegen-lib Platform --codegen-lib Classical --codegen-lib SeqProperties --codegen-lib HyperHeap  --admit_fsi FStar.Char --admit_fsi FStar.HyperHeap --admit_fsi FStar.Set --admit_fsi FStar.Map --admit_fsi FStar.Seq --admit_fsi SessionDB --admit_fsi UntrustedCert --admit_fsi DHDB --admit_fsi CoreCrypto --admit_fsi Cert --admit_fsi Handshake --lax;
  other-files:FStar.FunctionalExtensionality.fst FStar.Classical.fst FStar.Set.fsi FStar.Heap.fst map.fsi FStar.List.Tot.fst FStar.HyperHeap.fsi stHyperHeap.fst allHyperHeap.fst char.fsi FStar.String.fst FStar.List.fst FStar.ListProperties.fst seq.fsi FStar.SeqProperties.fst /home/jkz/dev/FStar/contrib/Platform/fst/Bytes.fst /home/jkz/dev/FStar/contrib/Platform/fst/Date.fst /home/jkz/dev/FStar/contrib/Platform/fst/Error.fst /home/jkz/dev/FStar/contrib/Platform/fst/Tcp.fst /home/jkz/dev/FStar/contrib/CoreCrypto/fst/CoreCrypto.fst /home/jkz/dev/FStar/contrib/CoreCrypto/fst/DHDB.fst TLSError.fst TLSConstants-redux.fst Nonce.fst RSAKey.fst DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst UntrustedCert.fsti Cert.fsti TLSInfo.fst TLSExtensions_Redux.p.fst Range.p.fst DataStream.fst TLSPRF.fst Alert.fst Content.fst StatefulPlain.fst LHAEPlain.fst AEAD_GCM.fst StatefulLHAE.fsti StatefulLHAE.fst PRF-redux.p.fst HandshakeMessages_Redux.fst;
  --*)

(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

(* Handshake protocol messages *)
module Handshake
open FStar.Seq
open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSExtensions
open TLSInfo
open Range
open HandshakeMessages

type ri = (cVerifyData * sVerifyData) 
type log = bytes 
//or how about: 
//type log = list (m:bytes{exists ht d. m = messageBytes ht d})

type nego = {
     n_resume: bool;
     n_client_random: TLSInfo.random;
     n_server_random: TLSInfo.random;
     n_sessionID: sessionID;
     n_protocol_version: protocolVersion;
     n_cipher_suite: known_cipher_suite;
     n_compression: Compression;
     n_extensions: negotiatedExtensions;
}                 

type ID = {
     id_cert: Cert.chain;
     id_sigalg: option Sig.alg;
}

type ake = {
     ake_server_id: option ID;
     ake_client_id: option ID;
     ake_pms: PMS.pms; 
     ake_session_hash: bytes;
     ake_ms: PRF.masterSecret;
}

type Session = {
     session_nego: nego;
     session_ake: ake;
}     

type eph_s = option KEX_S_PRIV
type eph_c = list KEX_S_PRIV

type clientState (c:config) = 
  | C_Idle of option ri
  | C_HelloSent of option ri * eph_c * CH 
  | C_HelloReceived of nego * option ake 
  | C_FinishedSent of Session * cVerifyData 


assume val client_init: c:config -> s:clientState c{is_C_Idle s}
assume val getClientHello: c:config -> s:clientState c{is_C_Idle s} -> 
                           (s':clientState c{is_C_HelloSent s'} * CH)

assume val processServerHelloDone: c:config -> s:clientState c{is_C_HelloReceived s} -> 
                           CRT -> option SKE -> option CR ->
                           (s':clientState c{is_C_FinishedSent s'} * option CRT * CKE * option CV * FIN)

assume val processServerFinished: c:config -> s:clientState c{is_C_FinishedSent s} -> 
                           option STICKET -> FIN -> 
                           s':clientState c{is_C_Idle s'} 


type serverState (c:config) = 
     | S_Idle of option ri
     | S_HelloSent of nego * option ake
     | S_HelloDone of nego * ID * eph_s
     | S_CCSReceived of Session
     | S_ResumeFinishedSent of Session
     | S_FinishedSent of Session
     | S_ZeroRTTReceived of Session

assume val server_init: c:config -> s:serverState c{is_S_Idle s}
assume val processClientHello: c:config -> s:serverState c{is_S_Idle s} -> CH ->
                               (s':serverState c{is_S_HelloSent s'} * SH)

(* TLS 1.2 regular handshake *)
assume val getServerHelloDone12: c:config -> s:serverState c{is_S_HelloSent s} -> 
                         (s':serverState c{is_S_HelloDone s'} * CRT * option SKE * option CR)
assume val processClientCCS12: c:config -> s:serverState c{is_S_HelloDone s} -> 
                             option CRT -> CKE -> option CV -> FIN ->
                             s':serverState c{is_S_CCSReceived s'}
assume val processClientFinished12: c:config -> s:serverState c{is_S_CCSReceived s} -> 
                             FIN -> 
                             (s':serverState c{is_S_FinishedSent s'} * option STICKET * FIN)

(* TLS 1.2 abbreviated handshake *)
assume val getServerFinishedResume12: c:config -> s:serverState c{is_S_HelloSent s} -> 
                         (s':serverState c{is_S_ResumeFinishedSent s'} *  option STICKET * FIN)
assume val processClientFinishedResume12: c:config -> s:serverState c{is_S_ResumeFinishedSent s} -> 
                         s':serverState c{is_S_Idle s'}
  
(* TLS 1.3 0RTT-1RTT handshake *)
assume val getServerFinished13: c:config -> s:serverState c{is_S_HelloSent s} -> 
                         (s':serverState c{is_S_FinishedSent s'} * option CR * option SC * SC * CV * FIN)

assume val process0RTTClientFinished13: c:config -> s:serverState c{is_S_FinishedSent s} -> 
                         option CRT -> option CV -> FIN ->
                         s':serverState c{is_S_ZeroRTTReceived s'}

assume val skip0RTTClientFinished13: c:config -> s:serverState c{is_S_FinishedSent s} -> 
                         s':serverState c{is_S_ZeroRTTReceived s'}

assume val process1RTTClientFinished13: c:config -> s:serverState c{is_S_ZeroRTTReceived s} -> 
                         option CRT -> option CV -> FIN ->
                         s':serverState c{is_S_Idle s'}

val prepareClientHello: config -> option ri -> option sessionID -> (CH * log)
let prepareClientHello cfg ri sido : CH * log =
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

val negotiate:#a:Type -> list a -> list a -> Tot (option a)
let negotiate l1 l2 =
  List.tryFindT (fun s -> List.existsb (fun c -> c = s) l1) l2

val negotiateCipherSuite: cfg:config -> pv:protocolVersion -> c:known_cipher_suites -> Tot (result known_cipher_suite)
let negotiateCipherSuite cfg pv c =
  match negotiate c cfg.ciphersuites with
  | Some(cs) -> Correct(cs)
  | None -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Cipher suite negotiation failed")

val negotiateCompression: cfg:config -> pv:protocolVersion -> c:list Compression -> Tot (result Compression)
let negotiateCompression cfg pv c =
  match negotiate c cfg.compressions with
  | Some(cs) -> Correct(cs)
  | None -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Compression negotiation failed")

// TODO : IMPLEMENT
val getCachedSession: cfg:config -> ch:CH -> option Session
let getCachedSession cfg cg = None

// FIXME: TLS1.3
val prepareServerHello: config -> option ri -> CH -> log -> result (bytes * nego * option ake * log)
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
    | Correct(cs) ->
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
       n_cipher_suite = cs;
       n_compression = cm;
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
val acceptableVersion: config -> CH -> protocolVersion -> TLSInfo.random -> Tot bool
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
val acceptableCipherSuite: config -> CH -> protocolVersion -> known_cipher_suite -> Tot bool
let acceptableCipherSuite cfg ch s_pv s_cs =
  // JP: I would think the first line implies the second one?
  List.existsb (fun x -> x = s_cs) ch.ch_cipher_suites &&
  List.existsb (fun x -> x = s_cs) cfg.ciphersuites &&
  not (isAnonCipherSuite s_cs) || cfg.allowAnonCipherSuite
  

(* Our server implementation doesn't support compression, meaning [cmp] is
 always [NullCompression], so it's always a valid compression. *)
val acceptableCompression: config -> CH -> protocolVersion -> Compression -> Tot bool
let acceptableCompression cfg ch pv cmp =
  true

val processServerHello: c:config -> s:clientState c{is_C_HelloSent s} -> SH ->
                           result (s':clientState c{is_C_HelloReceived s'})
let processServerHello cfg (C_HelloSent (ri, eph, ch)) sh =
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
            Correct (C_HelloReceived (o_nego, Some sentry.session_ake))
      else          
        let o_nego = 
          {n_client_random = ch.ch_client_random;
           n_server_random = sh.sh_server_random;
           n_sessionID = Some.v sh.sh_sessionID;
           n_protocol_version = sh.sh_protocol_version;
           n_cipher_suite = sh.sh_cipher_suite;
           n_compression = Some.v sh.sh_compression;
           n_extensions = next;
           n_resume = false } in
        Correct (C_HelloReceived (o_nego, None))


val prepareServerAke: config -> nego -> log -> result (bytes * ID * eph_s)
let prepareServerAke cfg nego nlog = 
    match nego.n_cipher_suite with
    | CipherSuite Kex_RSA None _ ->
      let calgs = [] in
      (match Cert.for_key_encryption calgs cfg.server_name with
       | None -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Could not find in the store a certificate for RSA encryption")
       | Some(c,sk) -> 
         let cB = certificateBytes ({crt_chain = c}) in 
         let creqB = 
             if cfg.request_client_certificate then
             certificateRequestBytes (
               {cr_cert_types = [];
                cr_sig_hash_algs = Some [];
                cr_distinguished_names = []})
             else empty_bytes in
         let msg = cB @| creqB @| serverHelloDoneBytes in
         Correct (msg,
                  ({id_cert = c; id_sigalg = None}),
                  Some (KEX_S_PRIV_RSA sk)))
         
    | _ -> failwith "unimplemented"  

(*
let process_ake_s cfg nego ml log =
    match nego.n_cipher_suite,ml with
    | CipherSuite RSA None _,
      [ServerCertificate sc;
       ServerCertificateRequest scr;
       ServerHelloDone] ->

    | CipherSuite RSA None _,
      [ServerCertificate sc;
       ServerHelloDone] ->

    | 

*)

assume val prepareClientFinishedFull: config -> nego -> ake -> log -> result (bytes * cVerifyData * log)
assume val processClientFinishedFull: config -> nego -> ake -> log -> list hs_msg -> result (bytes * ri)
assume val processServerFinishedFull: config -> nego -> ake -> cVerifyData -> log -> list hs_msg -> result (ri)

assume val prepareServerFinishedAbbr: config -> nego -> ake -> log -> result (bytes * sVerifyData * log)
assume val processServerFinishedAbbr: config -> nego -> ake -> log -> list hs_msg -> result (bytes * ri)
assume val processClientFinishedAbbr: config -> nego -> ake -> cVerifyData -> log -> list hs_msg -> result (ri)

type hs_msg_bufs = {
     hs_incoming_parsed : list hs_msg;
     hs_incoming: bytes;
     hs_outgoing: bytes;
}

assume val client_get_message: cfg:config -> st:clientState cfg ->
                 buf: hs_msg_bufs ->
                 result(bytes * clientState cfg * hs_msg_bufs)

assume val client_put_message: cfg:config -> st:clientState cfg ->
                 buf: hs_msg_bufs ->
                 result(bytes * clientState cfg * hs_msg_bufs)


assume val server_get_message: cfg:config -> st:clientState cfg ->
                 buf: hs_msg_bufs ->
                 result(bytes * clientState cfg * hs_msg_bufs)

assume val server_put_message: cfg:config -> st:clientState cfg ->
                 buf: hs_msg_bufs ->
                 result(bytes * clientState cfg * hs_msg_bufs)

