module TLSInfo

#set-options "--max_fuel 3 --initial_fuel 3 --max_ifuel 1 --initial_ifuel 1"

(* This module gathers the definitions of
   public datatypes, parameters, and predicates for our TLS API.

   Its interface is used by most TLS modules;
   its implementation is typechecked. 
*)

open Platform.Bytes
open Platform.Date
open TLSConstants
//open PMS
open Cert

module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap


(**************** SPECIFYING SAFETY (GENERAL COMMENTS) **************
  In the code of ideal implementations only,
  we use F# functions that characterize the Safe and Auth predicates.

  We need to typecheck ideal code,
  so we write their modules in the style

  #if ideal
    if safe...(...)
      ... GEN ...
    else
  ##endif
  .... COERCE ...

  This requires concrete safe/auth/strong/honest functions,
  used solely for controlling idealization.                        *)


// -------------------------------------------------------------------
// Application configuration
// TODO Consider repackaging separate client and server options

(* discussion about IDs and configurations (Cedric, Antoine, Santiago)

Server Certificates? 

- the client initial parameters...

- the server gets a CertSignQuery, picks its certificate chain from
  the ClientHello/ServerHello contents [new in miTLS 1.0]

- the client decides whether that's acceptable. 

Certificate Request? 

- in its ServerHello flight (or later) the server optionally requests a
  Cert/CertVerify (optionally with a list of CAs). This depends on
  what has been negotiated so far, including prior identities for
  both, and possibly on application data (e.g. ACL-based) [new in miTLS 1.0]

- the client optionally complies (for one of those CAs).
  [We always pass explicit requests to the client, as a CertSignQuery read result.]
  [We could have sign; read for solemnity; or read for simplicity.]

- the server decides whether that's acceptable.
  [We always pass inspection requests, as a CertVerifyQuery read result]
  [We have authorize; read for solemnity; could have read for simplicity.]

(forgetting about 0RTT for now)

type ServerCertificateRequest // something that determines this Handshake message

request_client_certificate: single_assign ServerCertificateRequest // uses this one, or asks the server; by default Some None.

*) 


type config = {
    (* Supported versions, ciphersuites, groups, signature algorithms *)
    minVer: protocolVersion;
    maxVer: protocolVersion;
    ciphersuites: x:valid_cipher_suites{List.Tot.length x < 256};
    compressions: l:list compression{ List.Tot.length l <= 1 };
    namedGroups: list (x:namedGroup{is_SEC x \/ is_FFDHE x});
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
    check_peer_certificate: bool; // To disable certificate validation
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

val sigAlgPref: list sigAlg -> list hashAlg' -> Tot (list sigHashAlg)
let rec sigAlgPref s h =
    match s with
    | [] -> []
    | sa :: r -> List.Tot.append (List.Tot.map (fun u -> (sa,u)) h) (sigAlgPref r h)

val ec_ff_to_ng: list CoreCrypto.ec_curve -> list ffdhe -> Tot (list (n:namedGroup{is_SEC n \/ is_FFDHE n}))
let rec ec_ff_to_ng ecl ffl =
  match ecl with
  | ec::r -> (SEC ec) :: (ec_ff_to_ng r ffl)
  | [] -> (match ffl with
    | ff :: r -> (FFDHE ff) :: (ec_ff_to_ng ecl r)
    | [] -> [])

#set-options "--initial_fuel 10 --max_fuel 10"
val defaultConfig : config
let defaultConfig =
    let sigPref = [CoreCrypto.ECDSA; CoreCrypto.RSAPSS; CoreCrypto.RSASIG] in
    let hashPref = [Hash CoreCrypto.SHA512; Hash CoreCrypto.SHA384;
                    Hash CoreCrypto.SHA256; Hash CoreCrypto.SHA1] in
    let sigAlgPrefs = sigAlgPref sigPref hashPref in
    let l =         [ TLS_RSA_WITH_AES_128_GCM_SHA256;
                      TLS_DHE_RSA_WITH_AES_128_GCM_SHA256;
                      TLS_DHE_DSS_WITH_AES_128_GCM_SHA256;
                      TLS_RSA_WITH_AES_128_CBC_SHA;
                      TLS_DHE_RSA_WITH_AES_128_CBC_SHA;
                      TLS_DHE_DSS_WITH_AES_128_CBC_SHA;
                      TLS_RSA_WITH_3DES_EDE_CBC_SHA;
                    ] in
    let curves = [CoreCrypto.ECC_P521; CoreCrypto.ECC_P384; CoreCrypto.ECC_P256] in
    let ffdh = [FFDHE4096; FFDHE3072] in
    let groups = ec_ff_to_ng curves ffdh in

    cut (List.Tot.length l == 7);//this requires 8 unfoldings
    let csn = cipherSuites_of_nameList l in
    {
    minVer = TLS_1p0;
    maxVer = TLS_1p2;
    ciphersuites = csn;
    compressions = [NullCompression];
    namedGroups = groups;
    signatureAlgorithms = sigAlgPrefs;

    honourHelloReq = true;
    allowAnonCipherSuite = false;

    request_client_certificate = false;
    check_client_version_in_pms_for_old_tls = true;
    cert_chain_file = "server.pem";
    private_key_file = "server.key";

    safe_renegotiation = true;
    safe_resumption = true;
    peer_name = None; // Disables hostname validation
    check_peer_certificate = true;
    ca_file = "CAFile.pem";

    sessionDBFileName = "sessionDBFile.bin";
    sessionDBExpiry = newTimeSpan 1 0 0 0; (*@ one day, as suggested by the RFC *)

    dhDBFileName = DHDB.defaultFileName;
    dhDefaultGroupFileName = "default-dh.pem";
    dhPQMinLength = DHDB.defaultPQMinLength;
    }
#reset-options

// -------------------------------------------------------------------
// Client/Server randomness (implemented in Nonce)

// their first 4 bytes give the local time,
// so that they are locally pairwise-distinct
type random = lbytes 32
type crand = random
type srand = random
type csRands = lbytes 64

type cVerifyData = b:bytes{length b <= 64} (* ClientFinished payload *)
type sVerifyData = b:bytes{length b <= 64} (* ServerFinished payload *)

type sessionHash = bytes

let noCsr:csRands = Nonce.noCsr

// -------------------------------------------------------------------
// We support these extensions, with session scopes
// (defined here because TLSExtension is internal)

type serverName =
| SNI_DNS of b:bytes{repr_bytes (length b) <= 2}
| SNI_UNKNOWN of (n:nat{repr_bytes n <= 1}) * (b:bytes{repr_bytes (length b) <= 2})

type ri_status =
| RI_Unsupported
| RI_Valid
| RI_Invalid

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

let ne_default =
{
    ne_extended_ms = false;
    ne_extended_padding = false;
    ne_secure_renegotiation = RI_Unsupported;
    ne_supported_groups = None;
    ne_supported_point_formats = None;
    ne_server_names = None;
    ne_signature_algorithms = None;
    ne_keyShare = None;
}

// -------------------------------------------------------------------
// Pre Master Secret indexes

// Placeholder for overhaul of 1.2 indexes
type pmsId = PMS.pms
assume val strongKEX: pmsId -> Tot bool

// -------------------------------------------------------------------
// Master Secret indexes and their properties

// CF postv1, move strength predicates --> TLSConstants
// ``kefAlg is a strong randomness extractor, despite all other kefAlgs'', guarding idealization in KEF

assume val strongKEF: kefAlg_t -> Tot bool

// guarding idealizations for KDF and VerifyData (see PRF.fs)
assume val strongKDF: kdfAlg_t -> Tot bool
assume val strongVD: vdAlg_t -> Tot bool

// -------------------------------------------------------------------
// Session information (public immutable data)

type sessionID = b:bytes { length b <= 32 }
// ``An arbitrary byte sequence chosen by the server
// to identify an active or resumable session state.''

type sessionInfo = {
    init_crand: crand;
    init_srand: srand;
    protocol_version: p:protocolVersion; // { p <> TLS_1p3 };
    cipher_suite: cipherSuite;
    compression: compression;
    extensions: negotiatedExtensions;
    pmsId: pmsId;
    session_hash: sessionHash;
    client_auth: bool;
    clientID: Cert.chain;
    clientSigAlg: sigHashAlg;
    serverID: Cert.chain;
    serverSigAlg: sigHashAlg;
    sessionID: sessionID;
    }

type abbrInfo =
    {abbr_crand: crand;
     abbr_srand: srand;
     abbr_session_hash: sessionHash;
     abbr_vd: option (cVerifyData * sVerifyData) }

// for sessionID. we treat empty bytes as the absence of identifier,
// i.e. the session is not resumable.

// for certificates, the empty list represents the absence of identity
// (possibly refusing to present requested certs)

val csrands: sessionInfo -> Tot csRands
let csrands si = si.init_crand @| si.init_srand
//CF subsumes mk_csrands

// Getting algorithms from sessionInfo
//CF subsume mk_kefAlg, mk_kefAlgExtended, mk_kdfAlg
val kefAlg: pv:protocolVersion -> cs:cipherSuite{pv = TLS_1p2 ==> ~(is_NullCipherSuite cs \/ is_SCSV cs) /\ is_Some (prfMacAlg_of_ciphersuite_aux cs)} -> bool -> Tot kefAlg_t
let kefAlg pv cs ems =
  let label = if ems then extended_extract_label else extract_label in
  match pv with
  | SSL_3p0           -> PRF_SSL3_nested
  | TLS_1p0 | TLS_1p1 -> PRF_TLS_1p01 label
  | TLS_1p2           -> PRF_TLS_1p2 label (prfMacAlg_of_ciphersuite cs)
  | TLS_1p3           -> PRF_TLS_1p3 //TBC

val kdfAlg: pv:protocolVersion -> cs:cipherSuite{pv = TLS_1p2 ==> ~(is_NullCipherSuite cs \/ is_SCSV cs) /\ is_Some (prfMacAlg_of_ciphersuite_aux cs)} -> Tot kdfAlg_t
let kdfAlg pv cs =
  match pv with
  | SSL_3p0           -> PRF_SSL3_nested
  | TLS_1p0 | TLS_1p1 -> PRF_TLS_1p01 kdf_label
  | TLS_1p2           -> PRF_TLS_1p2 kdf_label (prfMacAlg_of_ciphersuite cs)
  | TLS_1p3           -> PRF_TLS_1p3 //TBC

let vdAlg si = si.protocol_version, si.cipher_suite

val siAuthEncAlg: si:sessionInfo { si.protocol_version = TLS_1p2 &&
                              pvcs si.protocol_version si.cipher_suite } -> Tot aeAlg
let siAuthEncAlg si = get_aeAlg si.cipher_suite

type msId = // We record the parameters used to derive the master secret;
  | StandardMS : pmsId -> csRands -> kefAlg_t -> msId
            // the pms index, the nonces, and the PMS-PRF algorithm
  | ExtendedMS : pmsId -> sessionHash -> kefAlg_t -> msId
            // the pms index, the hash of the session log, and the PMS-PRF algorithm
            // using the sessionHash instead of randoms prevent MiTM forwarding honest randoms

// ``the MS at this index is abstractly generated and used within PRF''
let honestMS = function
  | StandardMS pmsId csr ka -> PMS.honestPMS pmsId && strongKEF ka
  | ExtendedMS pmsId  sh ka -> PMS.honestPMS pmsId && strongKEF ka


// ADL Keeping these comments from 0.9 temporarily
// We don't rely on noPmsId and noMsId anymore; plaintext
// epochs use a special case in the id type

//CF are we missing a correlation with csr?
//MK we don't allow leak, so every MS derived from an
//MK HonestPMS with strong KEF algorithms is honest?
//MK More uniformally this would go through a definition of SafeCRE.
//val noMsId: i:msId { not (honestMS i) }
//let noMsId = StandardMS noPmsId noCsr PRF_SSL3_nested

// Getting master-secret indexes out of sessionInfo

//CF subsumes both MsI and mk_msid
val msid: si:sessionInfo { is_Some (prfMacAlg_of_ciphersuite_aux (si.cipher_suite)) } -> Tot msId
let msid si =
  let ems = si.extensions.ne_extended_ms in
  let kef = kefAlg si.protocol_version si.cipher_suite ems in
  if ems then ExtendedMS si.pmsId si.session_hash kef
  else StandardMS si.pmsId    (csrands si) kef

// Strengths of Handshake algorithms

// SZ: Not as simple, because the ciphersuite doesn't determine the
// hash algorithm. When using the `signature_algorithms` extension, this is
// even more complicated.
// NS: identifier not found: sigHashAlg_of_cipherSuite
assume val sigHashAlg_of_ciphersuite: cipherSuite -> Tot sigHashAlg

// SZ: To be replaced by Signature.int_cma
//let strongSig si = Sig.strong (sigHashAlg_of_ciphersuite si.cipher_suite)

// ``The algorithms of si are strong for both KDF and VerifyData, despite all others'
// guarding idealization in PRF
val strongPRF: si:sessionInfo{si.protocol_version = TLS_1p2 ==> ~(is_NullCipherSuite si.cipher_suite \/ is_SCSV si.cipher_suite) /\ is_Some (prfMacAlg_of_ciphersuite_aux si.cipher_suite)} -> Tot bool
let strongPRF si = strongKDF(kdfAlg si.protocol_version si.cipher_suite) && strongVD(vdAlg si)
// MK I think having this joint strength predicate
// MK guaranteeing the idealization of the complete module is useful

// Summarizing all assumptions needed for a strong handshake
// CF derived & to be used in the public API only
let strongHS si =
  strongKEX (si.pmsId) &&
  is_Some (prfMacAlg_of_ciphersuite_aux si.cipher_suite) && //NS: needed to add this ...
  strongKEF (kefAlg si.protocol_version si.cipher_suite si.extensions.ne_extended_ms) && //NS: ... to verify this
  strongPRF si
  //strongSig si //SZ: need to state the precise agile INT-CMA assumption, with a designated hash algorithm and a set of hash algorithms allowed in signing queries
  //CF * hashAlg for certs?

// Safety of sessionInfo crypto processing

// Safe handshake for PMS-based extraction
let safeCRE si = honestMS (msid si)

// Safe handshake for MS-based VerifyData
let safeVD si = honestMS (msid si) && strongVD(vdAlg si)
//MK: safeVD is used for idealization even if ciphersuites don't match.
//MK: this is needed to guarantee security of finished message MACs

assume val int_cma: macAlg -> Tot bool
let strongAuthSI si = true //TODO: fix

assume val strongAESI: sessionInfo -> Tot bool

// -------------------------------------------------------------------
// Indexing instances of derived keys for AE etc. 
//
// Index type definitions [1.3]:
//
//  -----<----- rmsId   exportId
// |              |    /
// |  keyId <- expandId  => finishedId
// V   ||     /   |   \
// |  ID13   /    |    \
// |        /     |     \
//  --->  esId -> hsId -> asId
//          \
//           --<-- psk_identifier
//
// Index type definitions [1.2]:
//
//    pmsId -> msId -> ID12
//
// type id = PlaintextID | ID12 msId | ID13 keyId

// Info type carried by hashed log
// The actual log is ghost but the info is carried in the index

// logInfo_CH is ONLY used with 0-RTT
// for the soundness of the *_of_id functions it can only
// be extracted from a log with EarlyDataIndication
type logInfo_CH = {
  li_ch_cr: crand;
  li_ch_psk: PSK.pskInfo;
}

type logInfo_SH = {
  li_sh_cr: crand;
  li_sh_sr: srand;
  li_sh_ae: a:aeAlg{is_AEAD a};
}

type logInfo_SF = logInfo_SH

type logInfo_CF = logInfo_SF

type logInfo =
| LogInfo_CH of logInfo_CH
| LogInfo_SH of logInfo_SH
| LogInfo_SF of logInfo_SF
| LogInfo_CF of logInfo_CF

let logInfo_ae : logInfo -> Tot (a:aeAlg{is_AEAD a}) = function
| LogInfo_CH x -> let pski = x.li_ch_psk in AEAD (PSK.pskInfo_ae pski) (PSK.pskInfo_hash pski)
| LogInfo_SH x
| LogInfo_SF x
| LogInfo_CF x -> x.li_sh_ae

let logInfo_nonce (rw:role) = function
| LogInfo_CH x -> x.li_ch_cr
| LogInfo_SH x
| LogInfo_SF x
| LogInfo_CF x -> if rw = Client then x.li_sh_cr else x.li_sh_sr

// Extensional equality of logInfo
// (we may want to use e.g. equalBytes on some fields)
// injectivity 
let eq_logInfo la lb : Tot bool =
  la = lb // TODO extensionality!

// Length constraint is enfoced in the 2nd definition step after valid
type hashed_log = bytes

// injective functions with extensional equality
type injective (#a:Type) (#b:Type)
  (#eqA:a -> a -> Tot bool) (#eqB:b -> b -> Tot bool)
  (f:a -> Tot b)
  =
  forall (x:a) (y:a).{:pattern (f x); (f y)}
  eqB (f x) (f y) ==> eqA x y

// -------------------------------------------------------------------
// Log <=> logInfo relation works through the following
// commutative diagram:
//
// list hs_msg --serialize--> bytes --hash--> hashed_log
//      |                                          |
//    project                                      |
//      v                                          |
//   logInfo  <-------------------f----------------/

// A predicate on info-carrying logs
// The function f is defined much later in HandshakeLog
// and folds the perfect hashing assumption and log projection
type log_info (li:logInfo) (h:hashed_log) =
  exists (f: hashed_log -> Tot logInfo).{:pattern (f h)}
  injective #hashed_log #logInfo #equalBytes #eq_logInfo f /\ f h = li

type pre_esId : Type0 =
  | ApplicationPSK: info:PSK.pskInfo -> i:PSK.psk_identifier -> pre_esId
  | ResumptionPSK: info:PSK.pskInfo -> i:pre_rmsId -> pre_esId

and pre_hsId =
  | HSID_PSK: pre_esId -> pre_hsId
  | HSID_PSK_DHE: pre_esId -> initiator:CommonDH.share -> responder:CommonDH.share -> pre_hsId
  | HSID_DHE: CoreCrypto.hash_alg -> initiator:CommonDH.share -> responder:CommonDH.share -> pre_hsId

and pre_asId =
  | ASID: pre_hsId -> pre_asId

and pre_rmsId =
  | RMSID: pre_asId -> logInfo -> hashed_log -> pre_rmsId

and pre_exportId =
  | ExportID: pre_asId -> logInfo -> hashed_log -> pre_exportId

and pre_rekeyId =
  | RekeyID: pre_asId -> logInfo -> hashed_log -> nat -> pre_rekeyId

and pre_expandId =
  | EarlySecretID: pre_esId -> pre_expandId
  | HandshakeSecretID: pre_hsId -> pre_expandId
  | ApplicationSecretID: pre_asId -> pre_expandId
  | RekeySecretID: pre_rekeyId -> pre_expandId

and keyTag =
  | EarlyTrafficKey
  | EarlyApplicationDataKey
  | HandshakeKey
  | ApplicationDataKey
  | ApplicationRekey

and pre_keyId =
  | KeyID: pre_expandId -> keyTag -> role -> logInfo -> hashed_log -> pre_keyId

and finishedTag =
  | EarlyFinished
  | HandshakeFinished
  | LateFinished

and pre_finishedId =
  | FinishedID: pre_expandId -> finishedTag -> role -> logInfo -> hashed_log -> pre_finishedId

val esId_hash: pre_esId -> Tot CoreCrypto.hash_alg
val hsId_hash: pre_hsId -> Tot CoreCrypto.hash_alg
val asId_hash: pre_asId -> Tot CoreCrypto.hash_alg
val rmsId_hash: pre_rmsId -> Tot CoreCrypto.hash_alg
val exportId_hash: pre_exportId -> Tot CoreCrypto.hash_alg
val rekeyId_hash: pre_rekeyId -> Tot CoreCrypto.hash_alg
val expandId_hash: pre_expandId -> Tot CoreCrypto.hash_alg
val keyId_hash: pre_keyId -> Tot CoreCrypto.hash_alg
val finishedId_hash: pre_finishedId -> Tot CoreCrypto.hash_alg

let rec esId_hash = function
  | ApplicationPSK ctx _ -> PSK.pskInfo_hash ctx
  | ResumptionPSK _ rmsId -> rmsId_hash rmsId

and hsId_hash = function
  | HSID_PSK i -> esId_hash i
  | HSID_DHE h _ _ -> h
  | HSID_PSK_DHE i _ _ -> esId_hash i

and asId_hash = function
  | ASID i -> hsId_hash i

and rmsId_hash = function
  | RMSID asId _ _ -> asId_hash asId

and exportId_hash = function
  | ExportID asId _ _ -> asId_hash asId

and rekeyId_hash = function
  | RekeyID i _ _ _ -> asId_hash i

and expandId_hash = function
  | EarlySecretID es -> esId_hash es
  | HandshakeSecretID hs -> hsId_hash hs
  | ApplicationSecretID asId -> asId_hash asId
  | RekeySecretID (RekeyID asId _ _ _) -> asId_hash asId

and keyId_hash (KeyID i _ _ _ _) = expandId_hash i

and finishedId_hash (FinishedID i _ _ _ _) = expandId_hash i

type valid_hlen (b:bytes) (h:CoreCrypto.hash_alg) =
  length b = CoreCrypto.hashSize h

val valid_esId: pre_esId -> GTot Type0
val valid_hsId: pre_hsId -> GTot Type0
val valid_asId: pre_asId -> GTot Type0
val valid_rmsId: pre_rmsId -> GTot Type0
val valid_exportId: pre_exportId -> GTot Type0
val valid_rekeyId: pre_rekeyId -> GTot Type0
val valid_expandId: pre_expandId -> GTot Type0
val valid_keyId: pre_keyId -> GTot Type0
val valid_finishedId: pre_finishedId -> GTot Type0

let rec valid_esId = function
  | ApplicationPSK ctx i ->
     MR.witnessed (PSK.valid_app_psk ctx i)
  | ResumptionPSK ctx i ->
     valid_rmsId i // /\ (MR.witnessed (valid_res_psk ctx i))

and valid_hsId = function
  | HSID_PSK i | HSID_PSK_DHE i _ _ -> valid_esId i
  | HSID_DHE _ _ _ -> True

and valid_asId = function
  | ASID i -> valid_hsId i

and valid_rmsId = function
  | RMSID i li log -> valid_asId i
      /\ valid_hlen log (asId_hash i)
      /\ log_info li log

and valid_exportId = function
  | ExportID i li log -> valid_asId i
      /\ valid_hlen log (asId_hash i)
      /\ log_info li log

and valid_rekeyId = function
  | RekeyID i li log _ -> valid_asId i
      /\ valid_hlen log (asId_hash i)
      /\ log_info li log

and valid_expandId = function
  | EarlySecretID i -> valid_esId i
  | HandshakeSecretID i -> valid_hsId i
  | ApplicationSecretID i -> valid_asId i
  | RekeySecretID i -> valid_rekeyId i

and valid_keyId = function
  | KeyID i tag rw li log ->
      ((tag = EarlyTrafficKey \/ tag = EarlyApplicationDataKey) ==> rw = Client)
      /\ valid_hlen log (expandId_hash i)
      /\ log_info li log

and valid_finishedId = function
  | FinishedID i tag rw li log ->
      ((tag = EarlyFinished \/ tag = LateFinished) ==> rw = Client)
      /\ valid_hlen log (expandId_hash i)
      /\ log_info li log

type esId = i:pre_esId{valid_esId i}
type hsId = i:pre_hsId{valid_hsId i}
type asId = i:pre_asId{valid_asId i}
type rmsId = i:pre_rmsId{valid_rmsId i}
type exportId = i:pre_exportId{valid_exportId i}
type rekeyId = i:pre_rekeyId{valid_rekeyId i}
type expandId = i:pre_expandId{valid_expandId i}
type keyId = i:pre_keyId{valid_keyId i}
type finishedId = i:pre_finishedId{valid_finishedId i}

type id =
| PlaintextID: our_rand:random -> id // For IdNonce
| ID13: keyId:keyId -> id
| ID12: pv:protocolVersion{pv <> TLS_1p3} -> msId:msId -> kdfAlg:kdfAlg_t -> aeAlg: aeAlg -> cr:crand -> sr:srand -> writer:role -> id 

let peerId = function
| PlaintextID r -> PlaintextID r
| ID13 (KeyID i tag rw li log) -> 
  let kid = KeyID i tag (dualRole rw) li log in 
  assume (valid_keyId kid);
  ID13 kid
| ID12 pv msid kdf ae cr sr rw -> ID12 pv msid kdf ae cr sr (dualRole rw)

val siId: si:sessionInfo{ 
  is_Some (prfMacAlg_of_ciphersuite_aux (si.cipher_suite)) /\ 
  si.protocol_version = TLS_1p2 /\
  pvcs si.protocol_version si.cipher_suite } -> role -> Tot id

let siId si r =
  let cr, sr = split (csrands si) 32 in
  ID12 si.protocol_version (msid si) (kdfAlg si.protocol_version si.cipher_suite) (siAuthEncAlg si) cr sr r

let pv_of_id (i:id{~(is_PlaintextID i)}) = match i with
  | ID13 _ -> TLS_1p3
  | ID12 pv _ _ _ _ _ _ -> pv

// Returns the local nonce
let nonce_of_id = function
  | PlaintextID r -> r
  | ID12 _ _ _ _ cr sr rw -> if rw = Client then cr else sr
  | ID13 (KeyID _ _ rw li _) -> logInfo_nonce rw li

val kdfAlg_of_id: i:id { is_ID12 i } -> Tot kdfAlg_t
let kdfAlg_of_id = function
  | ID12 pv _ kdf _ _ _ _ -> kdf

val macAlg_of_id: i:id { is_ID12 i /\ ~(is_AEAD (ID12.aeAlg i)) } -> Tot macAlg
let macAlg_of_id = function
  | ID12 pv _ _ ae _ _ _ -> 
    macAlg_of_aeAlg pv ae

val encAlg_of_id: i:id { is_ID12 i /\ is_MtE (ID12.aeAlg i) } -> Tot (encAlg * ivMode)
let encAlg_of_id = function
  | ID12 pv _ _ ae _ _ _ -> encAlg_of_aeAlg pv ae

val aeAlg_of_id: i:id { ~ (is_PlaintextID i) } -> Tot aeAlg
let aeAlg_of_id = function
  | ID13 (KeyID _ _ _ li _) -> logInfo_ae li
  | ID12 pv _ _ ae _ _ _ -> ae

let lemma_MtE (i:id{~(is_PlaintextID i)})
  : Lemma (is_MtE (aeAlg_of_id i) ==> is_ID12 i)
  = ()

let lemma_ID12 (i:id{~(is_PlaintextID i)})
  : Lemma (is_ID12 i ==> pv_of_id i <> TLS_1p3)
  = ()

// Pretty printing
let sinfo_to_string (si:sessionInfo) = "TODO"

// -----------------------------------------------------------------------
// Safety of key derivation depends on matching algorithms (see PRF)


(* ADL commenting until 1.2 stateful idealization is restored

assume logic type keyCommit   : csRands -> protocolVersion -> aeAlg -> negotiatedExtensions -> Type
assume logic type keyGenClient: csRands -> protocolVersion -> aeAlg -> negotiatedExtensions -> Type
assume logic type sentCCS     : role -> sessionInfo -> Type
assume logic type sentCCSAbbr : role -> abbrInfo -> Type

// ``the honest participants of handshake with this csr use matching aeAlgs''
type matches_id (i:id) =
    keyCommit i.csrConn i.pv i.aeAlg i.ext
    /\ keyGenClient i.csrConn i.pv i.aeAlg i.ext

// This index is safe for MS-based key derivation
val safeKDF: i:id -> Tot (b:bool { b=true <==> ((honestMS i.msId && strongKDF i.kdfAlg) /\ matches_id i) })
//defining this as true makes the context inconsitent!
let safeKDF _ = unsafe_coerce false //TODO: THIS IS A PLACEHOLDER

*)

// -----------------------------------------------------------------------
// The two main safety properties for the record layer

//let strongAuthId i = strongAuthAlg i.pv i.aeAlg
//let strongAEId i   = strongAEAlg   i.pv i.aeAlg

// ``We are idealizing integrity/confidentiality for this id''
let authId = function
  | PlaintextID _ -> false
  | ID13 ki -> false // TODO
  | ID12 pv msid kdf ae cr sr rw -> (* safeKDF i && *) strongAuthAlg pv ae

let safeId = function
  | PlaintextID _ -> false
  | ID13 ki -> false // TODO
  | ID12 pv msid kdf ae cr sr rw -> (* safeKDF i && *) strongAEAlg pv ae

