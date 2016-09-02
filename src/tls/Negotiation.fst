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

type pre_mode = {
  m_protocol_version: protocolVersion;
  m_kexAlg: TLSConstants.kexAlg;
  m_aeAlg: TLSConstants.aeAlg;
  m_sigAlg: option TLSConstants.sigAlg;
  m_cipher_suite: cipherSuite;
  m_dh_group: option namedGroup;
  m_dh_share: option bytes;
  m_psk: option PSK.psk_identifier;
  m_server_cert: option Cert.chain;
  m_comp: compression;
  m_extended_ms: bool;
  m_extended_padding: bool;
  m_secure_renegotiation: ri_status;
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
           /\ b2t (is_None m.m_dh_share)
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
     /\ m.m_extended_padding = false
     /\ m.m_secure_renegotiation = RI_Unsupported
     /\ m.m_point_format = None
  | _ -> False (* TODO *)

val intersect_lists : l1:list -> l2:list -> result:list {
  List.Tot.for_all (List.Tot.mem l1) result /\
  List.Tot.for_all (List.Tot.mem l2) result /\
  List.Tot.for_all (fun elem -> List.Tot.mem elem l2 ==> List.Tot.mem elem result) l1
}

let intersect_lists l1 l2 =
  l1
  |> List.Tot.filter (fun elem -> List.Tot.mem elem l2)

val filterClientOffer: serverCfg:config -> co:clientOffer -> list valid_mode 
let filterClientOffer serverCfg co =
  let filtered_ciphersuites = 
      co.co_cipher_suites
      |> intersect_lists serverCfg.ciphersuites in
  let filtered_SEC_groups =
      List.Tot.filter is_SEC co.co_namedGroups
      |> intersect_lists (List.filter is_SEC serverCfg.namedGroups) in
  let filtered_FFDHE_groups =
      List.Tot.filter is_FFDHE co.co_namedGroups
      |> intersect_lists (List.filter is_FFDHE serverCfg.namedGroups) in
  filtered_ciphersuites
  |> List.Tot.concatMap (fun cs -> match cs with //kk: remove this match statement if possible 
    | CipherSuite suite -> 
      match fst suite with
      | Kex_PSK -> [(suite,None)]
      | Kex_PSK_DHE | Kex_DHE -> List.map (fun elem -> (suite,elem)) filtered_FFDHE_groups
      | Kex_PSK_ECDHE | Kex_ECDHE -> List.map (fun elem -> (suite,elem)) filtered_SEC_groups  
      )
      
type mode = m:pre_mode{valid_mode m}

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
   co_psk = []; // TODO: Actually get the psk from the config.
   co_point_format = []; //TODO: Same as co_psk
   co_server_name = cfg.peer_name;
   co_extended_ms = false; //TODO: Add to TLSInfo.config and put here.
   co_secure_renegotiation = cfg.safe_renegotiation; //TODO: Fix name inconsistency.
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

val serverToNegotiatedExtension: config -> list extension -> cipherSuite -> option (cVerifyData * sVerifyData) -> bool -> (result mode) -> extension -> Tot (result (mode))
let serverToNegotiatedExtension cfg cExtL cs ri (resuming:bool) res sExt =
    match res with
    | Error(x,y) -> Error(x,y)
    | Correct(l) ->
      if List.Tot.existsb (sameExt sExt) cExtL then
            match sExt with
            | E_renegotiation_info (sri) ->
              (match sri, ri with
              | FirstConnection, None -> correct ({l with m_secure_renegotiation = RI_Valid})
              | ServerRenegotiationInfo(cvds,svds), Some(cvdc, svdc) ->
                 if equalBytes cvdc cvds && equalBytes svdc svds then
                    correct ({l with m_secure_renegotiation = RI_Valid})
                 else
                    Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Mismatch in contents of renegotiation indication")
              | _ -> Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Detected a renegotiation attack"))
            | E_server_name _ ->
                if List.Tot.existsb (fun x->match x with |E_server_name _ -> true | _ -> false) cExtL then correct(l)
                else Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent an SNI acknowledgement without an SNI provided")
            | E_ec_point_format(spf) ->
                if resuming then
                    correct l
                else
                    correct ({l with m_point_format = Some spf})
(* not allowed for server
            | E_signatureAlgorithms sha ->
                if resuming then correct l
                else correct ({l with n_signature_algorithms = Some (sha)})
*)
            | E_extended_ms ->
                if resuming then
                    correct(l)
                else
                    correct({l with m_extended_ms = true})
            | E_extended_padding ->
                if resuming then
                    Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server provided extended padding in a resuming handshake")
                else
                    if isOnlyMACCipherSuite cs then
                        Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server provided extended padding for a MAC only ciphersuite")
                    else
                        correct({l with m_extended_padding = true})
            | E_keyShare (ServerKeyShare sks) -> correct({l with m_keyShare = Some sks})
            | _ -> Error (AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Unexpected pattern in serverToNegotiatedExtension")
        else
            Error(AD_handshake_failure,perror __SOURCE_FILE__ __LINE__ "Server sent an extension not present in client hello")


val negotiateClientExtensions: protocolVersion -> config -> list extension -> list extension -> cipherSuite -> option (cVerifyData * sVerifyData) -> bool -> Tot (result (negotiatedExtensions))
let negotiateClientExtensions pv cfg cExtL sExtL cs ri (resuming:bool) =
  let nes = ne_default in
  match List.Tot.fold_left (serverToNegotiatedExtension cfg cExtL cs ri resuming) (correct nes) sExtL with
  | Error(x,y) -> Error(x,y)
  | Correct l ->
    if resuming then correct l
    else
      begin
        match List.Tot.tryFind is_E_signatureAlgorithms cExtL with
        | Some (E_signatureAlgorithms shal) ->
          correct({l with ne_signature_algorithms = Some shal})
        | None -> correct l
        | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Unappropriate sig algs in negotiateClientExtensions")
      end

val clientToNegotiatedExtension: config -> cipherSuite -> option (cVerifyData * sVerifyData) -> bool -> negotiatedExtensions -> extension -> Tot negotiatedExtensions
let clientToNegotiatedExtension (cfg:config) cs ri resuming neg cExt =
  match cExt with
    | E_renegotiation_info (cri) ->
        let rs =
           match cri, ri with
           | FirstConnection, None -> RI_Valid
           | ClientRenegotiationInfo(cvdc), Some (cvds, svds) ->
               if equalBytes cvdc cvds then RI_Valid else RI_Invalid
           | _ -> RI_Invalid in
        {neg with ne_secure_renegotiation = rs}
    | E_supported_groups l ->
        if resuming then neg
        else
            let isOK g = List.Tot.existsb (fun (x:namedGroup) -> x = g) (list_valid_ng_is_list_ng cfg.namedGroups) in
            {neg with ne_supported_groups = Some (List.Tot.filter isOK l)}
    | E_ec_point_format l ->
        if resuming then neg
        else
            let nl = List.Tot.filter (fun x -> x = ECGroup.ECP_UNCOMPRESSED) l in
            {neg with ne_supported_point_formats = Some nl}
    | E_server_name l ->
        {neg with ne_server_names = Some l}
    | E_extended_ms ->
        if resuming then
            neg
        else
            // If EMS is disabled in config, don't negotiate it
            {neg with ne_extended_ms = cfg.safe_resumption}
    | E_extended_padding ->
        if resuming then
            neg
        else
            if isOnlyMACCipherSuite cs then
                neg
            else
                {neg with ne_extended_padding = true}
    | E_signatureAlgorithms sha ->
        if resuming then neg
        else {neg with ne_signature_algorithms = Some (sha)}
    | _ -> neg // JK : handle remaining cases


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
        if pv <> TLS_1p3 && cfg.safe_resumption then Some(E_extended_ms)
        else None
    | E_extended_padding ->
        if resuming then
            None
        else
            if isOnlyMACCipherSuite cs then
                None
            else
                Some(E_extended_padding)
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
irreducible val computeMode: cfg:config -> cpv:protocolVersion -> ccs:valid_cipher_suites -> cexts:list extension -> comps: (list compression) -> ri:option (cVerifyData*sVerifyData) -> Tot (result (mode * list extension * list extension))

let computeMode cfg cpv ccs cexts comps ri = 
  (match (negotiateVersion cfg cpv) with 
    | Error(z) -> Error(z)
    | Correct(npv) ->
  let nosa = fun (CipherSuite _ sa _) -> is_None sa in
  let sigfilter = match Cert.lookup_chain cfg.cert_chain_file with
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
  let nego = ne_default in 
  let next = List.Tot.fold_left (clientToNegotiatedExtension cfg cs ri false) nego cexts in
  let ng = negotiateGroupKeyShare cfg npv kex cexts in
  match ng with
    | Error(z), _ | _, Error(z) -> Error(z)
    | Correct(next), Correct(gn, gxo) ->
      let comp = match comps with
                 | [] -> None
                 | _ -> Some NullCompression in
      let mode = {
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

irreducible val verifyMode: cfg:config -> cext:list extension -> cpv:protocolVersion -> spv:protocolVersion -> sr:TLSInfo.random -> cs:valid_cipher_suite -> sext:list extension -> comp:option compression -> option ri -> Tot (result mode)

let verifyMode cfg cext cpv spv sr cs sext comp ri =
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
