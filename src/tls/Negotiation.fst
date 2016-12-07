module Negotiation

open Platform.Error
open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
open TLSFormats
open HandshakeMessages

//16-05-31 these opens are implementation-only; overall we should open less
open TLSExtensions 
open CoreCrypto

(* A flag for runtime debugging of negotiation data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)
inline_for_extraction let n_debug = false

(* Negotiation: HELLO sub-module *)
type ri = cVerifyData * sVerifyData 

type clientOffer = {
  co_protocol_version:protocolVersion;
  co_cipher_suites:(k:valid_cipher_suites{List.Tot.length k < 256});
  co_compressions:(cl:list compression{List.Tot.length cl > 0 /\ List.Tot.length cl < 256});
  co_namedGroups: list (x:namedGroup{SEC? x \/ FFDHE? x});
  co_sigAlgs: list sigScheme;
  co_safe_resumption: bool;
  co_safe_renegotiation: bool;
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
     sm_ext: negotiatedExtensions;
     
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
     id_cert: chain;
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

val prepareClientOffer: cfg:config -> Tot clientOffer
let prepareClientOffer cfg =
  let co = 
  {co_protocol_version = cfg.maxVer;
   co_cipher_suites = cfg.ciphersuites;
   co_compressions = [NullCompression];
   co_namedGroups = cfg.namedGroups;
   co_sigAlgs = cfg.signatureAlgorithms;
   co_safe_resumption = cfg.safe_resumption;
   co_safe_renegotiation = cfg.safe_renegotiation;
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
val negotiate:l1:list valid_cipher_suite -> list valid_cipher_suite -> Tot (option (c:valid_cipher_suite{CipherSuite? c && List.Tot.mem c l1}))
let negotiate l1 l2 =
  List.Tot.find #valid_cipher_suite (fun s -> CipherSuite? s && List.Tot.mem s l1) l2

// For use in ensuring the result from negotiate is a Correct
// ciphersuite with associated kex, sig and ae algorithms,
// and throws an error if No ciphersuites were supported in both lists
val negotiateCipherSuite: cfg:config -> pv:protocolVersion -> ccs:valid_cipher_suites -> Tot (result (TLSConstants.kexAlg * option TLSConstants.sigAlg * TLSConstants.aeAlg * valid_cipher_suite))
let negotiateCipherSuite cfg pv ccs =
  match negotiate ccs cfg.ciphersuites with
  | Some(CipherSuite kex sa ae) -> Correct(kex,sa,ae,CipherSuite kex sa ae)
  | None -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Cipher suite negotiation failed")

val negotiateGroupKeyShare: config -> protocolVersion -> kexAlg -> option (list extension) -> Tot (result (option namedGroup * option bytes))
let rec negotiateGroupKeyShare cfg pv kex exts =
  match exts with
  | None when (pv = TLS_1p3) -> Error(AD_decode_error, "no supported group or key share extension found")
  | Some exts when (pv = TLS_1p3) ->
    let rec aux: list extension -> Tot (result (option namedGroup * option bytes)) =
      function
      | E_keyShare (ClientKeyShare gl) :: _ ->
        let inConf (gn, gx) =
           (((SEC? gn) && (kex = Kex_ECDHE || kex = Kex_PSK_ECDHE))
            || ((FFDHE? gn) && (kex = Kex_DHE || kex = Kex_PSK_DHE)))
           && List.Tot.mem gn cfg.namedGroups in
        (match List.Tot.filter inConf gl with
        | (gn, gx) :: _ -> Correct (Some gn, Some gx)
        | [] -> Error(AD_decode_error, "no shared group between client and server config"))
      | _ :: t -> aux t
      | [] -> Error(AD_decode_error, "no supported group or key share extension found")
    in aux exts
  | Some exts when (kex = Kex_ECDHE && List.Tot.existsb E_supported_groups? exts) ->
    let Some (E_supported_groups gl) = List.Tot.find E_supported_groups? exts in
    let filter x = SEC? x && List.Tot.mem x cfg.namedGroups in
    (match List.Tot.filter filter gl with
    | gn :: _ -> Correct (Some gn, None)
    | [] -> Error(AD_decode_error, "no shared curve configured"))
  | _ ->
    let filter x =
      (match kex with | Kex_DHE -> FFDHE? x | Kex_ECDHE -> SEC? x | _ -> false) in
    if kex = Kex_DHE || kex = Kex_ECDHE then
      (match List.Tot.filter filter cfg.namedGroups with
      | gn :: _ -> Correct (Some gn, None)
      | [] -> Error(AD_decode_error, "no valid group is configured for the selected cipher suite"))
    else Correct(None, None)

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

// TODO ADL: incorrect as written; CS nego depends on ext nego
//   (e.g. in TLS 1.2 it's incorrect to select an EC cipher suite if
//         EC extensions are missing)
// FIXME ADL
// I have hacked nego to at least not pick a bad CS for the server's cert keytype
// but this REALLY needs to be rewritten properly from scratch by someone who has
// read all TLS RFCs
// FIXME ADL: grossly inefficient; we need to cache the server keytype at startup
// TODO BD: ignoring extensions for the moment
// due to the fact that we require calling the keyschedule
// in between negotiating the named Group and preparing the
// negotiated Extensions
irreducible val computeServerMode: cfg:config -> cpv:protocolVersion -> ccs:valid_cipher_suites -> cexts:option (list extension) -> comps: (list compression) -> ri:option (cVerifyData*sVerifyData) -> Tot (result serverMode)
let computeServerMode cfg cpv ccs cexts comps ri = 
  (match (negotiateVersion cfg cpv) with 
    | Error(z) -> Error(z)
    | Correct(npv) ->
  let nosa = fun (CipherSuite _ sa _) -> None? sa in
  let sigfilter = match Cert.lookup_chain cfg.cert_chain_file with
    | Correct(c) when (Some? (Cert.endpoint_keytype c)) ->
      let kt = Cert.endpoint_keytype c in
      (fun (CipherSuite _ sa _) ->
        match sa,kt with
        | Some sa, Some kt ->
          (match sa, kt with
          | RSASIG, KeyRSA _ | RSAPSS, KeyRSA _
          | ECDSA, KeyECDSA _ | DSA, KeyDSA _ -> true
          | _ -> false)
        | _ -> false)
    | _ ->
       let _ = 
        if n_debug then 
          IO.debug_print_string "WARNING cannot load server cert; restricting to anonymous CS...\n"
        else false in
       nosa in
  let ccs = List.Tot.filter sigfilter ccs in
  match negotiateCipherSuite cfg npv ccs with
    | Error(z) -> Error(z)
    | Correct(kex,sa,ae,cs) ->
  let nego = ne_default in 
  let next = (match cexts with
   | Some cexts -> Correct(List.Tot.fold_left (clientToNegotiatedExtension cfg cs ri false) nego cexts)
//   | None -> ne_default)
   | None -> (match npv with
              | SSL_3p0 ->
                let cre =
                  if contains_TLS_EMPTY_RENEGOTIATION_INFO_SCSV (list_valid_cs_is_list_cs ccs) then
                     {ne_default with ne_secure_renegotiation = RI_Valid}
                  else ne_default 
                in Correct (cre)
             | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Missing extensions in TLS client hello"))) 
  in
  let ng = negotiateGroupKeyShare cfg npv kex cexts in
  match next, ng with
    | Error(z), _ | _, Error(z) -> Error(z)
    | Correct(next), Correct(gn, gxo) ->
      let comp = match comps with
                 | [] -> None
                 | _ -> Some NullCompression in
      let mode = {
        sm_protocol_version = npv;
        sm_kexAlg = kex;
        sm_aeAlg = ae;
        sm_sigAlg = sa;
        sm_cipher_suite = cs;
        sm_dh_group = gn;
        sm_dh_share = gxo;
        sm_comp = comp;
        sm_ext = next;
      } in
      Correct (mode))

irreducible val computeClientMode: cfg:config -> cext:option (list extension) -> cpv:protocolVersion -> spv:protocolVersion -> sr:TLSInfo.random -> cs:valid_cipher_suite -> sext:option (list extension) -> comp:option compression -> option ri -> Tot (result clientMode)
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
