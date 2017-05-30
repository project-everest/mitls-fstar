//../../.fstar/bin/fstar.exe --lax --universes --explicit_deps --use_native_int --codegen-lib CoreCrypto --codegen-lib Platform --codegen-lib Classical --codegen-lib Seq.Properties --codegen-lib HyperHeap  --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3rlimit 20 --__temp_no_proj Handshake --__temp_no_proj Connection --verify_module Nego ../../.fstar/ulib/FStar.Ghost.fst ../../.fstar/ulib/FStar.FunctionalExtensionality.fst ../../.fstar/ulib/FStar.Classical.fst ../../.fstar/ulib/FStar.Set.fst ../../.fstar/ulib/FStar.Heap.fst ../../.fstar/ulib/FStar.Map.fst ../../.fstar/ulib/FStar.List.Tot.Base.fst ../../.fstar/ulib/FStar.HyperHeap.fst ../../.fstar/ulib/hyperheap/FStar.ST.fst ../../.fstar/ulib/hyperheap/FStar.All.fst ../../.fstar/ulib/FStar.Monotonic.RRef.fst ../../.fstar/ulib/FStar.Char.fsti ../../.fstar/ulib/FStar.String.fsti ../../.fstar/ulib/FStar.List.Tot.Properties.fst ../../.fstar/ulib/FStar.List.Tot.fst ../../.fstar/ulib/FStar.List.fst ../../.fstar/ulib/FStar.Seq.Base.fst ../../.fstar/ulib/FStar.Seq.Properties.fst ../../.fstar/ulib/FStar.Seq.fst ../../.fstar/ulib/FStar.Float.fsti ../../.fstar/ulib/FStar.IO.fsti ../../.fstar/ulib/FStar.UInt8.fst ../../.fstar/ucontrib/Platform/fst/Platform.Bytes.fst ../../.fstar/ucontrib/Platform/fst/Platform.Date.fst ../../.fstar/ucontrib/Platform/fst/Platform.Error.fst ../../.fstar/ucontrib/Platform/fst/Platform.Tcp.fst ../../.fstar/ucontrib/CoreCrypto/fst/CoreCrypto.fst ../../.fstar/ucontrib/CoreCrypto/fst/DHDB.fst         IdealFlags.fst MonotoneSeq.fst MonotoneMap.fst TLSError.fst TLSConstants.fst Nonce.fst RSAKey.fst DHGroup.fst ECGroup.fst CommonDH.fst PMS.fst HASH.fst HMAC.fst Signature.fst Cert.fst TLSInfo.fst IdNonce.fst TLSExtensions.fst experiments/Nego.fst


module Nego

open Platform.Bytes
open Platform.Date
open Platform.Error
open TLSInfo
open TLSConstants
open TLSExtensions
open TLSError

//config contains the certificate store

type config = {
    (* Supported versions, ciphersuites, groups, signature algorithms *)
    minVer: protocolVersion;
    maxVer: protocolVersion;
    ciphersuites: x:valid_cipher_suites{List.Tot.length x < 256};
    compressions: l:list compression{ List.Tot.length l <= 1 };
    namedGroups: list (x:namedGroup{SEC? x \/ FFDHE? x});
    signatureAlgorithms: list sigHashAlg;

    (* Handshake specific options *)

    (* Client side *)
    honourHelloReq: bool;       // TLS_1p3: continues trying to comply with the server's choice.
    allowAnonCipherSuite: bool; // a safeguard against proposing ciphersuites (not so useful?)
    safe_resumption: bool;      // demands this extension when resuming

    (* Server side *)
    request_client_certificate: bool; // TODO: generalize to CertificateRequest contents: a list of CAs.
    check_client_version_in_pms_for_old_tls: bool;
    cert_chain_file: string;    // TEMPORARY until the proper cert logic described above is implemented
    private_key_file: string;   // TEMPORARY

    (* Common *)
    safe_renegotiation: bool;   // demands this extension when renegotiating
    peer_name: option string;   // The expected name to match against the peer certificate
    ca_file: string;  // openssl certificate store (/etc/ssl/certs/ca-certificates.crt)
                      // on Cygwin /etc/ssl/certs/ca-bundle.crt

    (* Sessions database *)
    sessionDBFileName: string;
    sessionDBExpiry: timeSpan;

    (* DH groups database *)
    dhDBFileName: string;
    dhDefaultGroupFileName: string;
    dhPQMinLength: nat * nat;
}

type cert

//Called to obtain certificate matching negotiated requirements
type negoCert: config -> string (*cert hint*) -> sigAlg -> cipherSuite -> cert

//Called by other party to check that certificate is valid, includes certificate check.
type checkCert: config -> string (*cert hint*) -> sigAlg -> cipherSuite -> cert -> bool

type offers1 = {
  co_protocol_version:protocolVersion;
//  co_client_random:TLSInfo.random;
//  co_sessionID:sessionID;
  co_cipher_suites:(k:valid_cipher_suites{List.Tot.length k < 256});
  co_compressions:(cl:list compression{List.Tot.length cl < 256});
  co_extensions:option (ce:list extension{List.Tot.length ce < 256});
  co_namedGroups: list (x:namedGroup{SEC? x \/ FFDHE? x});
  //MK: instead of extension containing key shares, we return list of named groups
}

type negotiatedExtensions = {
    ne_extended_ms: bool;
    ne_extended_padding: bool;
    ne_secure_renegotiation: ri_status;

    //$ Cedric: these extensions were missing in F7.
    ne_supported_groups: option (list namedGroup);
    ne_supported_point_formats: option (list ECGroup.point_format);
    ne_server_names: option (list serverName);
    ne_signature_algorithms: option (list sigHashAlg);
    ne_keyShare: option serverKeyShare;
}

type mode1 = {
     m_resume: bool;
//     n_client_random: TLSInfo.random;
//     n_server_random: TLSInfo.random;
//     n_sessionID: option sessionID;
     m_protocol_version: protocolVersion;
     m_kexAlg: TLSConstants.kexAlg;
     m_aeAlg: TLSConstants.aeAlg;
     m_sigAlg: option TLSConstants.sigAlg;
     m_cipher_suite: cipherSuite;
     m_dh_group: option namedGroup;
     m_compression: option compression;
     m_extensions: option negotiatedExtensions; //MK option added
     m_scsv: list scsv_suite;
}

type offers2
type mode2

// The extensions sent by the client
// (for the server we negotiate the client extensions)
val prepareExtensions: config // -> connectionInfo -> option (cVerifyData * sVerifyData) -> (option keyShare) 
    -> Tot (l:list extension{List.Tot.length l < 256})
let prepareExtensions (cfg:config) = //(conn:connectionInfo) ri ks =
    (* Always send supported extensions. The configuration options will influence how strict the tests will be *)
//    let cri =
//       match ri with
//       | None -> FirstConnection
//       | Some (cvd, svd) -> ClientRenegotiationInfo cvd in
//    let res = [E_renegotiation_info(cri)] in
//    let res = 
//       match cfg.maxVer,ks with
//       | TLS_1p3,Some ks -> (E_keyShare ks)::res
//       | _,_ -> res in
    let res = [] in
    let res = if cfg.safe_resumption then E_extended_ms :: res else res in
//No extended padding for now
//    let res = E_extended_padding :: res in
    let res = (E_signatureAlgorithms cfg.signatureAlgorithms) :: res in
    let res =
        if List.Tot.existsb (fun x -> isECDHECipherSuite x) cfg.ciphersuites then
          E_ec_point_format([ECGroup.ECP_UNCOMPRESSED]) :: (E_supported_groups cfg.namedGroups) :: res
        else
          let g = List.Tot.filter (function | FFDHE _ -> true | _ -> false) cfg.namedGroups in
          if g = [] then res
          else (E_supported_groups g) :: res in
    res


val clientOffers: config -> offers1
let clientOffers cfg =
// let ci = initConnection Client cr in
 let ext = prepareExtensions cfg in //ci ri kp in
 let co = 
  {co_protocol_version = cfg.maxVer;
//   co_sessionID = sid;
   co_cipher_suites = cfg.ciphersuites;
   co_raw_cipher_suites = None;
   co_compressions = [NullCompression];
   co_extensions = Some ext;
   co_namedGroups = cfg.namedGroups ;} 
   in co

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

val negotiateGroupKeyShare: cfg:config -> protocolVersion -> kexAlg -> exts:option (list extension) -> Tot (result (namedGroup * option bytes))
let rec negotiateGroupKeyShare cfg pv kex exts = 
    match pv,kex,exts with
    | TLS_1p3, Kex_ECDHE, Some (E_keyShare (ClientKeyShare ((gn,gxb)::_)) :: _) ->
      Correct (gn,Some gxb)
    | TLS_1p3,_, Some (h::t) -> negotiateGroupKeyShare cfg pv kex (Some t)
    | TLS_1p2, Kex_ECDHE, _ -> Correct (SEC CoreCrypto.ECC_P256, None) 
    | _ -> Error(AD_decode_error, "no supported group or key share extension found")

val serverMode: config -> offers1 -> result mode1
let serverMode cfg co = 
  match negotiateVersion cfg co.co_protocol_version with
    | Error(z) -> Error(z)
    | Correct(pv) ->
  match negotiateCipherSuite cfg pv co.co_cipher_suites with
    | Error(z) -> Error(z)
    | Correct(kex,sa,ae,cs) ->
  match negotiateGroupKeyShare cfg pv kex co.co_extensions with
    | Error(z) -> Error(z)
    | Correct(gn,gxo) ->
//  let srand = KeySchedule.ks_server_random ks in
//  let ksl =
//    (match pv,gxo with
//     | TLS_1p3,Some gxb -> None
//       let gyb = KeySchedule.ks_server_13_1rtt_init ks co.co_client_random cs gn gxb in
//      (Some (ServerKeyShare (gn,gyb)))
//    | _ -> None) in
//  match negotiateServerExtensions pv co.co_extensions co.co_cipher_suites cfg cs ri ksl false with
//    | Error(z) -> Error(z)
//    | Correct(sext,next) ->
//    let sid = CoreCrypto.random 32 in
    let comp = match co.co_compressions with
      | [] -> None
      | _ -> Some NullCompression in
    let mode = 
      {
//       n_client_random = co.co_client_random;       
//       n_server_random = srand;
//       n_sessionID = Some sid;
       m_protocol_version = pv;
       m_kexAlg = kex;
       m_sigAlg = sa;
       m_aeAlg  = ae;
       m_cipher_suite = cs;
       m_compression = comp;
       m_dh_group = Some gn;
       m_scsv = [];
       m_extensions = None; //next;
       (* [getCachedSession] returned [None], so no session resumption *)
       m_resume = false} in Correct mode

val clientModeCheck: config -> mode1 -> result unit

(*
let clientModeCheck cfg m =

if not (acceptableVersion cfg ch m.protocol_version sh.sh_server_random) then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Protocol version negotiation")
  else  if not (acceptableCipherSuite cfg ch sh.sh_protocol_version sh.sh_cipher_suite) then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Ciphersuite negotiation")
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
            sh.sh_compression <> sentry.session_nego.n_compression
          then
            Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Resumption params do not match cached session")
          else 
            let o_nego = {sentry.session_nego with n_extensions = next} in
            Correct ()
*)

val serverOffers: config -> mode1 -> offers2

val clientMode: config -> offers2 -> mode2

val serverModeCheck: config -> mode2 -> bool
