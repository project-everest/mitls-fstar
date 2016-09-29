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
  co_namedGroups: list (x:namedGroup{is_SEC x \/ is_FFDHE x});
  co_sigAlgs: list sigHashAlg;
  co_psk: list PSK.psk_identifier;
  co_point_format: list ECGroup.point_format;
  co_server_name: list serverName;
  co_extended_ms: bool;
  co_secure_renegotiation: bool;
}

(**
  TODO XXX BEWARE
  secure_renegotiation was turned to bool
  we no longer check the value of the SRI when
  doing renego. This MUST be added to handshake
**)

type pre_mode = {
  m_protocol_version: protocolVersion;
  m_kexAlg: TLSConstants.kexAlg;
  m_aeAlg: TLSConstants.aeAlg;
  m_sigAlg: option TLSConstants.sigAlg;
  m_cipher_suite: cipherSuite;
  m_dh_group: option namedGroup;
  m_psk: option PSK.psk_identifier;
  m_server_cert: option Cert.chain;
  m_comp: compression;
  m_extended_ms: bool;
  m_secure_renegotiation: bool;
  m_point_format: option ECGroup.point_format;
  m_server_name: option serverName;
}

let valid_mode (m:pre_mode) = 
  match m.m_protocol_version with
  | TLS_1p3 ->
    is_AEAD m.m_aeAlg
    /\ m.m_comp = NullCompression
    /\ (*Placeholder: only allow 1.3 cipher suites *) True
    /\ (match m.m_kexAlg with
       | Kex_PSK ->
           b2t (is_None m.m_dh_group)
           /\ b2t (is_Some m.m_psk)
       | Kex_PSK_DHE ->
           b2t (is_Some m.m_dh_group)
           /\ b2t (is_FFDHE (Some.v m.m_dh_group))
           /\ b2t (is_Some m.m_psk)
       | Kex_PSK_ECDHE ->
           b2t (is_Some m.m_dh_group)
           /\ b2t (is_SEC (Some.v m.m_dh_group))
           /\ b2t (is_Some m.m_psk)
       | Kex_DHE ->
           b2t (is_Some m.m_sigAlg)
           /\ b2t (is_Some m.m_dh_group)
           /\ b2t (is_FFDHE (Some.v m.m_dh_group))
           /\ b2t (is_None m.m_psk)
       | Kex_ECDHE ->
           b2t (is_Some m.m_sigAlg)
           /\ b2t (is_Some m.m_dh_group)
           /\ b2t (is_SEC (Some.v m.m_dh_group))
           /\ b2t (is_None m.m_psk)
       | _ -> False)
     /\ m.m_extended_ms = false
     /\ m.m_secure_renegotiation = false
     /\ m.m_point_format = None
  | _ -> False (* TODO *)


type mode = m:pre_mode{valid_mode m}


val intersect_lists : l1:list 'a -> l2:list 'a -> result:list 'a {
  List.Tot.for_all (fun a -> List.Tot.mem a l1) result /\
  List.Tot.for_all (fun a -> List.Tot.mem a l2) result /\
  List.Tot.for_all (fun a -> not (List.Tot.mem a l2) || List.Tot.mem a result) l1
}

let intersect_lists l1 l2 =
  l1
  |> List.Tot.filter (fun elem -> List.Tot.mem elem l2)
  
(** this function computes the full cartesian products of server modes compatible 
    with a client offer in precedence order
    *)
    
//val filterClientOffer: serverCfg:config -> co:clientOffer -> list mode 
let filterClientOffer serverCfg co =
  let filtered_ciphersuites = 
    intersect_lists co.co_cipher_suites serverCfg.ciphersuites in

  let filtered_FFDHE_groups =
    intersect_lists (List.Tot.filter is_FFDHE co.co_namedGroups) (List.Tot.filter is_FFDHE serverCfg.namedGroups) in

  let filtered_SEC_groups = List.Tot.filter is_SEC co.co_namedGroups |> intersect_lists (List.Tot.filter is_SEC serverCfg.namedGroups)  in
         
  List.Tot.concatMap (fun cs -> match cs with //kk: remove this match statement if possible 
    | CipherSuite kex sa ae -> 
      match kex with
      | Kex_PSK -> [(cs,None)]
      | Kex_PSK_DHE | Kex_DHE -> List.Tot.map (fun elem -> (cs,Some(elem))) filtered_FFDHE_groups
      | Kex_PSK_ECDHE | Kex_ECDHE -> List.Tot.map (fun elem -> (cs,Some(elem))) filtered_SEC_groups  
      ) filtered_ciphersuites
      

val prepareClientOffer: cfg:config -> Tot clientOffer
let prepareClientOffer cfg =
  let sni_list = 
    if is_Some cfg.peerName then [SNI_DNS (utf8 (Some.v cfg.peerName))] else [] in
  let co = 
  {co_protocol_version = cfg.maxVer;
   co_cipher_suites = cfg.ciphersuites;
   co_compressions = cfg.compressions;
   co_namedGroups = cfg.namedGroups;
   co_sigAlgs = cfg.signatureAlgorithms;
   co_psk = []; // TODO: Actually get the psk from the config.
   co_point_format = cfg.pointFormats;
   co_server_name = sni_list;
   co_extended_ms = cfg.extendedMasterSecret;
   co_secure_renegotiation = cfg.secureRenegotiation;
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

val negotiateGroupKeyShare: config -> protocolVersion -> kexAlg -> list extension -> Tot (result (option namedGroup * option bytes))
let rec negotiateGroupKeyShare cfg pv kex exts =
  match pv with
  | TLS_1p3 ->
    let rec aux: list extension -> Tot (result (option namedGroup * option bytes)) =
      function
      | E_keyShare (ClientKeyShare gl) :: _ ->
        let inConf (gn, gx) =
           (((is_SEC gn) && (kex = Kex_ECDHE || kex = Kex_PSK_ECDHE))
            || ((is_FFDHE gn) && (kex = Kex_DHE || kex = Kex_PSK_DHE)))
           && List.Tot.mem gn cfg.namedGroups in
        (match List.Tot.filter inConf gl with
        | (gn, gx) :: _ -> Correct (Some gn, Some gx)
        | [] -> Error(AD_decode_error, "no shared group between client and server config"))
      | _ :: t -> aux t
      | [] -> Error(AD_decode_error, "no supported group or key share extension found")
    in aux exts

  | _ when (kex = Kex_ECDHE && List.Tot.existsb is_E_supported_groups exts) ->
    let Some (E_supported_groups gl) = List.Tot.find is_E_supported_groups exts in
    let filter x = is_SEC x && List.Tot.mem x cfg.namedGroups in
    (match List.Tot.filter filter gl with
    | gn :: _ -> Correct (Some gn, None)
    | [] -> Error(AD_decode_error, "no shared curve configured"))

  | _ ->
    let filter x =
      (match kex with | Kex_DHE -> is_FFDHE x | Kex_ECDHE -> is_SEC x | _ -> false) in
    if kex = Kex_DHE || kex = Kex_ECDHE then
      (match List.Tot.filter filter cfg.namedGroups with
      | gn :: _ -> Correct (Some gn, None)
      | [] -> Error(AD_decode_error, "no valid group is configured for the selected cipher suite"))
    else Correct(None, None)

(** TODO Move to handshake
 (match sri, ri with
            | FirstConnection, None -> correct ({l with m_secure_renegotiation = RI_Valid})
            | ServerRenegotiationInfo(cvds,svds), Some(cvdc, svdc) ->
                 if equalBytes cvdc cvds && equalBytes svdc svds then
                    correct ({l with m_secure_renegotiation = RI_Valid})
                 else
                    Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Mismatch in contents of renegotiation indication")
*)

(**
 Verify a single extension returned by the server
 given the offered extensions and local config.
*)
val verifyServerExtension: config -> list extension -> bool -> (result mode) -> extension -> Tot (result (mode))
let verifyServerExtension cfg cExtL (resuming:bool) res sExt =
    match res with
    | Error(x,y) -> Error(x,y) (* Propagate errors *)
    | Correct(mode) ->
      (* Ensure that we proposed this extension *)
      if not (List.Tot.existsb (sameExt sExt) cExtL) then
        Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent an extension not present in client hello")
      else match sExt with
        (* Secure Renegotiation Indication *)
        | E_renegotiation_info (sri) ->
          if mode.m_protocol_version = TLS_1p3 then
            Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent the secure renegotiation indication in TLS 1.3")
          else
            Correct ({mode with m_secure_renegotiation = true})
        (* SNI, if provided in cleartext *)
        | E_server_name sni ->
          (* In TLS 1.3, SNI must be encrypted *)
          if mode.m_protocol_version = TLS_1p3 then
            Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent a plaintext SNI in TLS 1.3")
          else if sni <> [] then 
            Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent an SNI acknowledgement with a non-empty name list")
          else Correct mode
        | E_ec_point_format(spf) ->
          if mode.m_protocol_version = TLS_1p3 then
            Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent an EC point format extension in TLS 1.3")
          else if resuming then
            Correct mode
          else
            if List.Tot.existsb (fun x -> not (List.Tot.mem x cfg.pointFormats)) spf then
              Error(AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Server picked a point format that was not offered")
            else
              Correct ({mode with m_point_format = Some (List.Tot.hd spf)}) //Client proposes only ECGroup.ECP_UNCOMPRESSED.
        | E_signatureAlgorithms _ ->
          Error(AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Server sent a signature algorithm extension")
        | E_extended_ms ->
          if mode.m_protocol_version = TLS_1p3 then
            Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent the Extended Master Secret extension in TLS 1.3")
          else Correct ({mode with m_extended_ms = true})
        | _ -> Error (AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Received an unexpected extension from the server")


private val check_dup: sl:list extension -> Tot bool
let rec check_dup = function
  | [] -> true
  | h :: t ->
    if List.Tot.existsb (sameExt h) t then false
    else check_dup t

(**
 Fills in the extension-dependant fields of the mode
 based on the offered and received extensions from the
 server, checking that the server choices are consistent
 with the local client configuration.
*)
val verifyServerExtensions: mode -> config -> list extension -> list extension -> option (cVerifyData * sVerifyData) -> bool -> Tot (result (mode))
let verifyServerExtensions mode cfg cExtL sExtL ri (resuming:bool) =    
  match List.Tot.fold_left (verifyServerExtension cfg cExtL resuming) (correct mode) sExtL with
  | Error(x,y) -> Error(x,y)
  | Correct l ->
     if check_dup sExtL then correct l
     else Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Server sent a duplicated extension")

(**
 This both computes the mode and the server extensions 
 from the offered client extensions and the local server
 configuration
*)
val negotiateExtension: protocolVersion -> config -> option (cVerifyData * sVerifyData) -> bool -> (list extension * pre_mode) -> extension -> Tot (list extension * pre_mode)
let negotiateExtension pv (cfg:config) ri resuming (sExtL, mode) cExt =
  match cExt with
    | E_renegotiation_info (cri) ->
      if mode.m_protocol_version = TLS_1p3 then
        (sExtL, mode) (* Ignore SRI in TLS 1.3 *)
      else
        let rs =
           match cri, ri with
           | FirstConnection, None -> RI_Valid
           | ClientRenegotiationInfo(cvdc), Some (cvds, svds) ->
               if equalBytes cvdc cvds then RI_Valid else RI_Invalid
           | _ -> RI_Invalid in
        let ric =
           match ri with
           | Some t -> ServerRenegotiationInfo t
           | None -> FirstConnection in
        ((E_renegotiation_info ric) :: sExtL,
         {mode with m_secure_renegotiation = rs})
    | E_ec_point_format l ->
      if mode.m_protocol_version = TLS_1p3 then
        (sExtL, mode) (* Ignore SRI in TLS 1.3 *)
      else
        if resuming then (sExtL, mode)
        else
          let nl = List.Tot.filter (fun x -> x = ECGroup.ECP_UNCOMPRESSED) l in
          ((E_ec_point_format [ECGroup.ECP_UNCOMPRESSED]) :: sExtL, {mode with m_point_format = Some (ECGroup.ECP_UNCOMPRESSED)}) //TODO really pick first?
    | E_server_name l ->
      (match List.Tot.tryFind (fun x->match x with | SNI_DNS _ -> true | _ -> false) l with
        | Some name ->
          if pv <> TLS_1p3
          then ((E_server_name []) :: sExtL, {mode with m_server_name = Some name}) 
          else (sExtL, mode) // TODO EncryptedExtensions
        | _ ->  (sExtL, mode))

    | E_extended_ms ->
      if resuming then (sExtL, mode)
      else
        // If EMS is disabled in config, don't negotiate it
	if pv <> TLS_1p3 && cfg.extendedMasterSecret then ((E_extended_ms) :: sExtL, {mode with m_extended_ms = true}) 
        else (sExtL, mode)
        
    | E_signatureAlgorithms sha ->
      if resuming then (sExtL, mode)
      else (sExtL, {mode with m_sigAlg = Some (List.Tot.hd sha)}) //TODO check that there is no server extension
    | _ -> (sExtL, mode)


val clientToServerExtension: protocolVersion -> config -> cipherSuite -> option (cVerifyData * sVerifyData) -> option keyShare -> bool -> extension -> Tot (option extension)
let clientToServerExtension pv (cfg:config) (cs:cipherSuite) ri ks (resuming:bool) (cExt:extension) : (option (extension)) =
    match cExt with
    | E_earlyData b -> None    // JK : TODO
    | E_preSharedKey b -> None // JK : TODO
    | E_keyShare b ->
        (match ks with
        | Some k -> Some (E_keyShare k)
        | None -> None)
    | E_renegotiation_info (_) ->
        let ric =
           match ri with
           | Some t -> ServerRenegotiationInfo t
           | None -> FirstConnection in
        (match pv with
        | TLS_1p3 -> None
        | _ -> Some (E_renegotiation_info ric))
    | E_server_name l ->
        (match List.Tot.tryFind (fun x->match x with | SNI_DNS _ -> true | _ -> false) l with
        | Some _ ->
          if pv <> TLS_1p3
          then Some(E_server_name []) // TODO EncryptedExtensions
          else None
        | _ -> None)
    | E_ec_point_format(l) ->
        if resuming || pv = TLS_1p3 then None
        else Some(E_ec_point_format [ECGroup.ECP_UNCOMPRESSED])
    | E_supported_groups(l) -> None
    | E_extended_ms ->
        if pv <> TLS_1p3 && cfg.extendedMasterSecret then Some(E_extended_ms)
        else None
    | _ -> None


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
  | Error _ -> false

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
irreducible val computeMode: cfg:config -> cpv:protocolVersion -> ccs:valid_cipher_suites -> cexts:list extension -> comps: (list compression) -> ri:option (cVerifyData*sVerifyData) -> Tot (result (mode * option keyShareBytes * list extension * list extension))

let computeMode cfg cpv ccs cexts comps ri = 
  (match (negotiateVersion cfg cpv) with 
    | Error(z) -> Error(z)
    | Correct(npv) ->
  let nosa = fun (CipherSuite _ sa _) -> is_None sa in
  let sigfilter = match Cert.lookup_chain cfg.certChainFile with
    | Correct(c) when (is_Some (Cert.endpoint_keytype c)) ->
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
       let _ = IO.debug_print_string "WARNING cannot load server cert; restricting to anonymous CS...\n" in
       nosa in
  let ccs = List.Tot.filter sigfilter ccs in
  match negotiateCipherSuite cfg npv ccs with
    | Error(z) -> Error(z)
    | Correct(kex,sa,ae,cs) ->
      let comp = match comps with
             | [] -> None
             | _ -> Some NullCompression in
      let mode = {
        m_protocol_version = npv;
        m_kexAlg = kex;
        m_aeAlg = ae;
        m_sigAlg = sa;
        m_cipher_suite = cs;
        m_dh_group = None;
        m_psk = None;
        m_server_cert = None;
        m_comp = comp;
        m_extended_ms = false;
        m_secure_renegotiation = RI_Unsupported;
        m_point_format = None;
        m_server_name = None;
      } in
  let mode = List.Tot.fold_left (negotiateExtension cfg cs ri false) mode cexts in
  let ng = negotiateGroupKeyShare cfg npv kex cexts in
  match ng with
    | Error(z), _ | _, Error(z) -> Error(z)
    | Correct(next), Correct(gn, gxo) ->
      let mode = { mode with
        m_protocol_version = npv;
        m_kexAlg = kex;
        m_aeAlg = ae;
        m_sigAlg = sa;
        m_cipher_suite = cs;
        m_dh_group = gn;
        m_dh_share = gxo;
        m_comp = comp;
        m_ext = next;
      } in
      Correct (mode))

irreducible val verifyMode: cfg:config -> cext:list extension -> cpv:protocolVersion -> spv:protocolVersion -> sr:TLSInfo.random -> cs:valid_cipher_suite -> sext:list extension -> comp:compression -> rio:option ri -> Tot (result mode)

let verifyMode cfg cext cpv spv sr cs sext comp rio =
  if not (acceptableVersion cfg cpv spv sr) then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Protocol version negotiation")
  else
  if not (acceptableCipherSuite cfg spv cs) then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Ciphersuite negotiation")
  else
  if not List.Tot.mem comp cfg.compressions then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Server picked an unoffered compression mode")
  else
  match cs with
  | CipherSuite kex sa ae ->
    let mode = {
      m_protocol_version = spv;
      m_kexAlg = kex;
      m_aeAlg = ae;
      m_sigAlg = sa;
      m_cipher_suite = cs;
      m_dh_group = None;
      m_psk = None;
      m_server_cert = None;
      m_comp = comp;
      m_extended_ms = false;
      m_secure_renegotiation = RI_Unsupported;
      m_point_format = None;
      m_server_name = None;
    } in
    let resume = false in //MK not clear why this is ok
    let mode = verifyServerExtensions mode cfg cext sext rio resume in
    let mode = match sa with
    | Some sigalg ->
      if not List.Tot.mem sigalg cfg.signatureAlgorithms then
        Error (AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Server picked a ciphersuite using an unoffered signature algorithm")
      else mode
    | None -> mode in
    mode
  | _ -> Error (AD_decode_error, "ServerHello ciphersuite is not a real ciphersuite")


(*
  if not (acceptableCipherSuite cfg spv cs) then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Ciphersuite negotiation")
  else
   let resume = false in
   match negotiateClientExtensions spv cfg cext sext cs rio resume with
    | Error(z) -> Error(z)
    | Correct(next) ->
    match cs with
     | CipherSuite kex sa ae ->
      match spv, kex, next.ne_keyShare with
       | TLS_1p3, Kex_DHE, Some (gn, gyb)
       | TLS_1p3, Kex_ECDHE, Some (gn, gyb) ->
         let mode =
         {m_protocol_version = spv;
          m_kexAlg = kex;
          m_aeAlg = ae;
          m_sigAlg = sa;
          m_cipher_suite = cs;
          m_dh_group = Some gn;
          m_dh_share = Some gyb;
          m_comp = comp;
          m_ext = next;
         } in
         Correct(mode)
       | _ ->
         let mode =
         {m_protocol_version = spv;
          m_kexAlg = kex;
          m_aeAlg = ae;
          m_sigAlg = sa;
          m_cipher_suite = cs;
          m_dh_group = None;
          m_dh_share = None;
          m_comp = comp;
          m_ext = next;
         } in
         Correct(mode)
      | _ -> Error (AD_decode_error, "ServerHello ciphersuite is not a real ciphersuite")
*)
