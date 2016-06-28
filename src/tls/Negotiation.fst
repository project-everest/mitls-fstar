module Negotiation

open Platform.Error
open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
open HandshakeMessages

//16-05-31 these opens are implementation-only; overall we should open less
open TLSExtensions 
open CoreCrypto

(* Negotiation: HELLO sub-module *)
type ri = cVerifyData * sVerifyData 

type clientOffer = {
  co_protocol_version:protocolVersion;
  co_cipher_suites:(k:valid_cipher_suites{List.Tot.length k < 256});
  co_compressions:(cl:list compression{List.Tot.length cl > 0 /\ List.Tot.length cl < 256});
  co_extensions:option (ce:list extension{List.Tot.length ce < 256});
}

type serverMode = {
     sm_protocol_version: protocolVersion;
     sm_kexAlg: TLSConstants.kexAlg;
     sm_aeAlg: TLSConstants.aeAlg;
     sm_sigAlg: option TLSConstants.sigAlg;
     sm_cipher_suite: cipherSuite;
     sm_dh_group: option namedGroup;
     sm_dh_share: option bytes;
     sm_comp: option compression;
     sm_ext: option negotiatedExtensions;
}

type clientMode = {
     cm_protocol_version: protocolVersion;
     cm_kexAlg: TLSConstants.kexAlg;
     cm_aeAlg: TLSConstants.aeAlg;
     cm_sigAlg: option TLSConstants.sigAlg;
     cm_cipher_suite: cipherSuite;
     cm_dh_group: option namedGroup;
     cm_dh_share: option bytes;
     cm_comp: option compression;
     cm_ext: negotiatedExtensions;
}


type nego = {
     n_resume: bool;
     n_client_random: TLSInfo.random;
     n_server_random: TLSInfo.random;
     n_sessionID: option sessionID;
     n_protocol_version: protocolVersion;
     n_kexAlg: TLSConstants.kexAlg;
     n_aeAlg: TLSConstants.aeAlg;
     n_sigAlg: option TLSConstants.sigAlg;
     n_cipher_suite: cipherSuite;
     n_dh_group: option namedGroup;
     n_compression: option compression;
     n_extensions: negotiatedExtensions;
     n_scsv: list scsv_suite;
     
}                 

type hs_id = {
     id_cert: Cert.chain;
     id_sigalg: option sigHashAlg;
}

type session = {
     session_nego: nego;
}     


// represents the outcome of a successful handshake, 
// providing context for the derived epoch
type handshake = 
  | Fresh of session // was sessionInfo
  | Resumed of session // was abbrInfo * sessionInfo 
// We use SessionInfo as unique session indexes.
// We tried using instead hs, but this creates circularities
// We'll probably need a global log to reason about them.
// We should probably do the same in the session store.

// extracts a transport key identifier from a handshake record
val handshakeId: handshake -> Tot id 
//16-05-31 TODO breaking TC in TLS; was (i:id { is_stream_ae i }) //16-05-19 focus on TLS 1.3

let handshakeId h = noId // Placeholder 

val prepareClientOffer: cfg:config -> ci:connectionInfo -> ri:option (cVerifyData *sVerifyData) -> kp: option keyShare -> Tot clientOffer
let prepareClientOffer cfg ci ri kp =
  let ext = prepareExtensions cfg ci ri kp in
  let co = 
  {co_protocol_version = cfg.maxVer;
   co_cipher_suites = cfg.ciphersuites;
   co_raw_cipher_suites = None;
   co_compressions = [NullCompression];
   co_extensions = Some ext;
   } in
  co

// Checks that the protocol version in the CHELO message is
// within the range of versions supported by the server configuration
// and outputs the negotiated version if true
val negotiateVersion: cfg:config -> c:protocolVersion -> Tot (result protocolVersion)
let negotiateVersion cfg c =
  if geqPV c cfg.minVer && geqPV cfg.maxVer c then Correct c
  else if geqPV c cfg.maxVer then Correct cfg.maxVer
  else Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Protocol version negotiation failed")

// For use in negotiating the ciphersuite, takes two lists and
// outputs the first ciphersuite in list2 that also is in list
// one and is a valid ciphersuite, or [None]
val negotiate:l1:list valid_cipher_suite -> list valid_cipher_suite -> Tot (option (c:valid_cipher_suite{is_CipherSuite c && List.Tot.mem c l1}))
let negotiate l1 l2 =
  List.Tot.find #valid_cipher_suite (fun s -> is_CipherSuite s && List.Tot.mem s l1) l2

// For use in ensuring the result from negotiate is a Correct
// ciphersuite with associated kex, sig and ae algorithms,
// and throws an error if No ciphersuites were supported in both lists
val negotiateCipherSuite: cfg:config -> pv:protocolVersion -> ccs:valid_cipher_suites -> Tot (result (TLSConstants.kexAlg * option TLSConstants.sigAlg * TLSConstants.aeAlg * valid_cipher_suite))
let negotiateCipherSuite cfg pv ccs =
  match negotiate ccs cfg.ciphersuites with
  | Some(CipherSuite kex sa ae) -> Correct(kex,sa,ae,CipherSuite kex sa ae)
  | None -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Cipher suite negotiation failed")

// FIXME: no FFDHE, doesn't check cfg.namedGroups
val negotiateGroupKeyShare: config -> protocolVersion -> kexAlg -> option (list extension) -> Tot (result (namedGroup * option bytes))
let rec negotiateGroupKeyShare cfg pv kex exts =
  match exts with
  | None ->
    begin
    match pv,kex with
    | TLS_1p2, Kex_ECDHE -> Correct (SEC ECC_P256, None)
    | _ -> Error(AD_decode_error, "no supported group or key share extension found")
    end
  | Some exts ->
    begin
    let rec aux: config -> protocolVersion -> kexAlg -> list extension -> Tot (result (namedGroup * option bytes)) = fun cfg pv kex es ->
      match pv,kex,es with
      | TLS_1p3, Kex_ECDHE, E_keyShare (ClientKeyShare ((gn,gxb)::_)) :: _ ->
        Correct (gn,Some gxb)
      | TLS_1p3,_, h::t -> aux cfg pv kex t
      | _ -> Error(AD_decode_error, "no supported group or key share extension found")
    in
    aux cfg pv kex exts
    end

// Determines if the server random value contains a downgrade flag
// AND if there has been a downgrade
// The downgrade flag is a random value set by RFC (6.3.1.1)
val isSentinelRandomValue: protocolVersion -> protocolVersion -> TLSInfo.random -> Tot bool
let isSentinelRandomValue c_pv s_pv s_random =
  geqPV c_pv TLS_1p3 && geqPV TLS_1p2 s_pv && equalBytes (abytes "DOWNGRD\x01") s_random ||
  geqPV c_pv TLS_1p2 && geqPV TLS_1p1 s_pv && equalBytes (abytes "DOWNGRD\x00") s_random

// Confirms that the version negotiated by the server was:
// - within the range specified by client config AND
// - is not an unnecessary downgrade AND
// - is not a newer version than offered by the client 

val acceptableVersion: config -> protocolVersion -> protocolVersion -> TLSInfo.random -> Tot bool
let acceptableVersion cfg cpv spv sr =
  match negotiateVersion cfg cpv with
  | Correct c_pv ->
    geqPV c_pv spv && geqPV spv cfg.minVer &&
    not (isSentinelRandomValue c_pv spv sr)
  | Error _ ->
    false

// Confirms that the ciphersuite negotiated by the server was:
//  - consistent with the client config;
//  - TODO: [s_cs] is supported by the protocol version (e.g. no GCM with
//    TLS<1.2).
// BD: Removed that the ciphersuite is acceptable given CHELO
// given that the clientOffer is prepared with the entire list
// of valid cipher suites in the client config
val acceptableCipherSuite: config -> protocolVersion -> valid_cipher_suite -> Tot bool
let acceptableCipherSuite cfg spv cs =
  List.Tot.existsb (fun x -> x = cs) cfg.ciphersuites &&
  not (isAnonCipherSuite cs) || cfg.allowAnonCipherSuite

// TODO BD: ignoring extensions for the moment
// due to the fact that we require calling the keyschedule
// in between negotiating the named Group and preparing the
// negotiated Extensions
val computeServerMode: cfg:config -> cpv:protocolVersion -> ccs:valid_cipher_suites -> cexts:option (list extension) -> comps: (list compression) -> Tot (result serverMode)
 let computeServerMode cfg cpv ccs cexts comps = 
  (match (negotiateVersion cfg cpv) with 
    | Error(z) -> Error(z)
    | Correct(npv) -> 
  match negotiateCipherSuite cfg npv ccs with
    | Error(z) -> Error(z)
    | Correct(kex,sa,ae,cs) ->
  match negotiateGroupKeyShare cfg npv kex cexts with
    | Error(z) -> Error(z)
    | Correct(gn,gxo) ->
  let comp = match comps with
    | [] -> None
    | _ -> Some NullCompression in
  let mode =
    {sm_protocol_version = npv;
     sm_kexAlg = kex;
     sm_aeAlg = ae;
     sm_sigAlg = sa;
     sm_cipher_suite = cs;
     sm_dh_group = Some gn;
     sm_dh_share = gxo;
     sm_comp = comp;
     sm_ext = None;
    } in
  Correct (mode))

val updateServerMode: cfg:config -> sm:serverMode -> cexts:option (list extension) -> ccs:valid_cipher_suites -> ri:option (cVerifyData *sVerifyData) -> kp: option keyShare -> Tot (result (option (list extension) * negotiatedExtensions * serverMode))
let updateServerMode cfg sm cexts ccs ri kp =
  (match negotiateServerExtensions sm.sm_protocol_version cexts ccs cfg sm.sm_cipher_suite ri kp false with
   | Error(z) -> Error(z)
   | Correct(sext,next) ->
  let mode =
   {sm_protocol_version = sm.sm_protocol_version;
    sm_kexAlg = sm.sm_kexAlg;
    sm_aeAlg = sm.sm_aeAlg;
    sm_sigAlg = sm.sm_sigAlg;
    sm_cipher_suite = sm.sm_cipher_suite;
    sm_dh_group = sm.sm_dh_group;
    sm_dh_share = sm.sm_dh_share;
    sm_comp = sm.sm_comp;
    sm_ext = Some next;
   } in
  Correct (sext, next, mode))



val computeClientMode: cfg:config -> cext:option (list extension) -> cpv:protocolVersion -> spv:protocolVersion -> sr:TLSInfo.random -> cs:valid_cipher_suite -> sext:option (list extension) -> comp:option compression -> option ri -> Tot (result clientMode)
let computeClientMode cfg cext cpv spv sr cs sext comp ri =
  if not (acceptableVersion cfg cpv spv sr) then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Protocol version negotiation")
  else if not (acceptableCipherSuite cfg spv cs) then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Ciphersuite negotiation")
  else
   let resume = false in
   match negotiateClientExtensions spv cfg cext sext cs ri resume with
    | Error(z) -> Error(z)
    | Correct(next) ->
    match cs with
     | CipherSuite kex sa ae ->
      match spv, kex, next.ne_keyShare with
       | TLS_1p3, Kex_DHE, Some (gn, gyb)
       | TLS_1p3, Kex_ECDHE, Some (gn, gyb) ->
         let mode =
         {cm_protocol_version = spv;
          cm_kexAlg = kex;
          cm_aeAlg = ae;
          cm_sigAlg = sa;
          cm_cipher_suite = cs;
          cm_dh_group = Some gn;
          cm_dh_share = Some gyb;
          cm_comp = comp;
          cm_ext = next;
         } in
         Correct(mode)
       | _ ->
         let mode =
         {cm_protocol_version = spv;
          cm_kexAlg = kex;
          cm_aeAlg = ae;
          cm_sigAlg = sa;
          cm_cipher_suite = cs;
          cm_dh_group = None;
          cm_dh_share = None;
          cm_comp = comp;
          cm_ext = next;
         } in
         Correct(mode)
      | _ -> Error (AD_decode_error, "ServerHello ciphersuite is not a real ciphersuite")
