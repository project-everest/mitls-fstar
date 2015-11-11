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
     n_client_random: TLSInfo.random;
     n_server_random: TLSInfo.random;
     n_sessionID: sessionID;
     n_protocol_version: ProtocolVersion;
     n_cipher_suite: known_cipher_suite;
     n_compression: Compression;
     n_extensions: negotiatedExtensions;
}                 

type ID = {
     id_cert: Cert.chain;
     id_sigalg: option Sig.alg;
}

type ake_s = {
     ake_s_id: ID;
     ake_s_kex_priv: option KEX_S_PRIV;
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

type clientState (c:config) = 
     | C_Idle of option ri
     | C_NegoSent of option ri * CH * log
     | C_NegoDone of nego * option ake * log
     | C_AkeDone of nego * ake * log  //Ephemeral state; immediately transits to FinishedSent
     | C_FinishedSent of nego * ake * cVerifyData * log
     | C_Complete of nego * ake * ri  //Transits to C_Idle (Some ri) for new epoch 

type serverState (c:config) = 
     | S_Idle of option ri
     | S_NegoDone of nego * option ake * log //Ephemeral state; immediately transits to AkeSent or FinishedSent
     | S_AkeSent  of nego * ake_s * log
     | S_AkeDone of nego * ake * log
     | S_FinishedSent of nego * ake * sVerifyData * log // Only used during resumption
     | S_Complete of nego * ake * ri //Transits to C_Idle (Some ri) for new epoch 


val prepareClientHello: config -> option ri -> option sessionID -> (CH * log)
let prepareClientHello cfg ri sido : CH * log =
  let crand = Nonce.mkHelloRandom() in
  let sid = (match sido with None -> empty_bytes | Some x -> x) in
  let cvd = (match ri with None -> empty_bytes | Some (x,y) -> x) in
  let ci = initConnection Client crand in
  let ext = prepareClientExtensions cfg ci cvd in
  let ch = 
  {ch_protocol_version = cfg.maxVer;
   ch_client_random = crand;
   ch_sessionID = sid;
   ch_cipher_suites = cfg.ciphersuites;
   ch_compressions = cfg.compressions;
   ch_extensions = ext;} in
  (ch,clientHelloBytes ch)

(* Should we gather all negotiation into one giant negotiation function? *)
assume val negotiateVersion: cfg:config -> c:ProtocolVersion -> Tot (Result ProtocolVersion)
assume val negotiateCipherSuite: cfg:config -> pv:ProtocolVersion -> c:known_cipher_suites -> Tot (Result known_cipher_suite)
assume val negotiateCompression: cfg:config -> pv:ProtocolVersion -> c:list Compression -> Tot (Result Compression)
assume val negotiateExtensions: cfg:config -> pv:ProtocolVersion -> option ri -> res:bool -> c:list clientExtension -> Tot (Result (l:list serverExtension{List.length l < 256} * negotiatedExtensions))

assume val getCachedSession: cfg:config -> ch:CH -> option Session

val prepareServerHello: config -> option ri -> CH -> log -> Result (bytes * nego * option ake * log)
let prepareServerHello cfg ri ch i_log =
  let srand = Nonce.mkHelloRandom() in
  match getCachedSession cfg ch with
  | Some sentry -> 
  (match negotiateExtensions cfg sentry.session_nego.n_protocol_version ri true ch.ch_extensions with
   | Error(z) -> Error(z)
   | Correct(sext,next) ->
     let shB = 
         serverHelloBytes (
          {sh_protocol_version = sentry.session_nego.n_protocol_version;
           sh_sessionID = sentry.session_nego.n_sessionID;
           sh_server_random = srand;
           sh_cipher_suite = sentry.session_nego.n_cipher_suite;
           sh_compression = sentry.session_nego.n_compression;
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
  match negotiateExtensions cfg pv ri false ch.ch_extensions with
  | Error(z) -> Error(z)
  | Correct(sext,next) ->
  let sid = Nonce.random 32 in
  let shB = 
    serverHelloBytes (
    {sh_protocol_version = pv;
     sh_sessionID = sid;
     sh_server_random = srand;
     sh_cipher_suite = cs;
     sh_compression = cm;
     sh_extensions = sext}) in
  let nego = 
    {n_client_random = ch.ch_client_random;
     n_server_random = srand;
     n_sessionID = sid;
     n_protocol_version = pv;
     n_cipher_suite = cs;
     n_compression = cm;
     n_extensions = next} in
  let o_log = i_log @| shB in
  Correct (shB,nego,None,o_log))

assume val acceptableVersion: config -> CH -> ProtocolVersion -> Tot bool
assume val acceptableCipherSuite: config -> CH -> ProtocolVersion -> known_cipher_suite -> Tot bool
assume val acceptableCompression: config -> CH -> ProtocolVersion -> Compression -> Tot bool
assume val acceptableExtensions: config -> option ri -> res:bool -> CH -> ProtocolVersion -> list serverExtension -> Tot (Result negotiatedExtensions)

val processServerHello: config -> option ri -> CH -> SH -> bool -> Result (nego * option ake)
let processServerHello cfg ri ch sh res =
    if not (acceptableVersion cfg ch sh.sh_protocol_version) 
    then Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Protocol version negotiation")
    else if not (acceptableCipherSuite cfg ch sh.sh_protocol_version sh.sh_cipher_suite)
    then Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Ciphersuite negotiation")
    else if not (acceptableCompression cfg ch sh.sh_protocol_version sh.sh_compression)
    then Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Compression negotiation") 
    else match (acceptableExtensions cfg ri res ch sh.sh_protocol_version sh.sh_extensions) with 
         | Error(z) -> Error(z)
         | Correct (next) -> 
           if res then
              match getCachedSession cfg ch with
              | None -> Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Resumption disallowed")
              | Some sentry ->
                if (sh.sh_protocol_version <> sentry.session_nego.n_protocol_version ||
                    sh.sh_cipher_suite <> sentry.session_nego.n_cipher_suite ||
                    sh.sh_compression <> sentry.session_nego.n_compression) 
                then Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Resumption params do not match cached session")
                else 
                  let o_nego = {sentry.session_nego with n_extensions = next} in
                  Correct(o_nego, Some sentry.session_ake)
           else          
             let o_nego = 
                 {n_client_random = ch.ch_client_random;
                  n_server_random = sh.sh_server_random;
                  n_sessionID = sh.sh_sessionID;
                  n_protocol_version = sh.sh_protocol_version;
                  n_cipher_suite = sh.sh_cipher_suite;
                  n_compression = sh.sh_compression;
                  n_extensions = next} in 
                  Correct(o_nego,None)


assume val processServerAke: config -> nego -> log -> list (HandshakeType * bytes) -> Result (bytes * ake)
assume val processClientAke: config -> nego -> ake_s -> log -> list (HandshakeType * bytes) -> Result (ake)

val prepareServerAke: config -> nego -> log -> Result (bytes * ake_s)
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
               {scr_cert_types = [];
                scr_sig_hash_algs = Some [];
                scr_distinguished_names = []})
             else empty_bytes in
         let msg = cB @| creqB @| serverHelloDoneBytes in
         Correct (msg,
                  {ake_s_id = ({id_cert = c; id_sigalg = None});
                   ake_s_kex_priv = Some (KEX_S_PRIV_RSA sk)}))
         
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

assume val prepareClientFinishedFull: config -> nego -> ake -> log -> Result (bytes * cVerifyData * log)
assume val processClientFinishedFull: config -> nego -> ake -> log -> list hs_msg -> Result (bytes * ri)
assume val processServerFinishedFull: config -> nego -> ake -> cVerifyData -> log -> list hs_msg -> Result (ri)

assume val prepareServerFinishedAbbr: config -> nego -> ake -> log -> Result (bytes * sVerifyData * log)
assume val processServerFinishedAbbr: config -> nego -> ake -> log -> list hs_msg -> Result (bytes * ri)
assume val processClientFinishedAbbr: config -> nego -> ake -> cVerifyData -> log -> list hs_msg -> Result (ri)

type hs_msg_bufs = {
     hs_incoming_parsed : list hs_msg;
     hs_incoming: bytes;
     hs_outgoing: bytes;
}

assume val client_get_message: cfg:config -> st:clientState cfg ->
                 buf: hs_msg_bufs ->
                 Result(bytes * clientState cfg * hs_msg_bufs)

assume val client_put_message: cfg:config -> st:clientState cfg ->
                 buf: hs_msg_bufs ->
                 Result(bytes * clientState cfg * hs_msg_bufs)


assume val server_get_message: cfg:config -> st:clientState cfg ->
                 buf: hs_msg_bufs ->
                 Result(bytes * clientState cfg * hs_msg_bufs)

assume val server_put_message: cfg:config -> st:clientState cfg ->
                 buf: hs_msg_bufs ->
                 Result(bytes * clientState cfg * hs_msg_bufs)



