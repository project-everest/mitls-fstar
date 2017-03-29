(*--build-config
options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
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


noeq type config = {
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

val ec_ff_to_ng: list CoreCrypto.ec_curve -> list ffdhe -> Tot (list (n:namedGroup{SEC? n \/ FFDHE? n}))
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
    let hashPref = Hashing.Spec.([Hash SHA512; Hash SHA384; Hash SHA256; Hash SHA1]) in
    let sigAlgPrefs = sigAlgPref sigPref hashPref in
    let l =         [ TLS_RSA_WITH_AES_128_GCM_SHA256;
                      TLS_DHE_RSA_WITH_AES_128_GCM_SHA256;
                      TLS_DHE_DSS_WITH_AES_128_GCM_SHA256;
                      TLS_RSA_WITH_AES_128_CBC_SHA;
                      TLS_DHE_RSA_WITH_AES_128_CBC_SHA;
                      TLS_DHE_DSS_WITH_AES_128_CBC_SHA;
                      TLS_RSA_WITH_3DES_EDE_CBC_SHA;
                    ] in
    let curves = CoreCrypto.([ECC_P521; ECC_P384; ECC_P256]) in
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
    ne_keyShare: option CommonDH.serverKeyShare;
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

noeq type sessionInfo = {
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

type resumeInfo (r:role) =
  o:option sessionID{r=Server ==> o=None} *
  l:list PSK.psk_identifier {r=Server ==> l = []} // assuming we do the PSK lookups locally

// for sessionID. we treat empty bytes as the absence of identifier,
// i.e. the session is not resumable.

// for certificates, the empty list represents the absence of identity
// (possibly refusing to present requested certs)

val csrands: sessionInfo -> Tot csRands
let csrands si = si.init_crand @| si.init_srand
//CF subsumes mk_csrands

// Getting algorithms from sessionInfo
//CF subsume mk_kefAlg, mk_kefAlgExtended, mk_kdfAlg
val kefAlg: pv:protocolVersion -> cs:cipherSuite{pv = TLS_1p2 ==> ~(NullCipherSuite? cs \/ SCSV? cs) /\ Some? (prfMacAlg_of_ciphersuite_aux cs)} -> bool -> Tot kefAlg_t
let kefAlg pv cs ems =
  let label = if ems then extended_extract_label else extract_label in
  match pv with
  | SSL_3p0           -> PRF_SSL3_nested
  | TLS_1p0 | TLS_1p1 -> PRF_TLS_1p01 label
  | TLS_1p2           -> PRF_TLS_1p2 label (prfMacAlg_of_ciphersuite cs)
  | TLS_1p3           -> PRF_TLS_1p3 //TBC

val kdfAlg: pv:protocolVersion -> cs:cipherSuite{pv = TLS_1p2 ==> ~(NullCipherSuite? cs \/ SCSV? cs) /\ Some? (prfMacAlg_of_ciphersuite_aux cs)} -> Tot kdfAlg_t
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
val msid: si:sessionInfo { Some? (prfMacAlg_of_ciphersuite_aux (si.cipher_suite)) } -> Tot msId
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
val strongPRF: si:sessionInfo{si.protocol_version = TLS_1p2 ==> ~(NullCipherSuite? si.cipher_suite \/ SCSV? si.cipher_suite) /\ Some? (prfMacAlg_of_ciphersuite_aux si.cipher_suite)} -> Tot bool
let strongPRF si = strongKDF(kdfAlg si.protocol_version si.cipher_suite) && strongVD(vdAlg si)
// MK I think having this joint strength predicate
// MK guaranteeing the idealization of the complete module is useful

// Summarizing all assumptions needed for a strong handshake
// CF derived & to be used in the public API only
let strongHS si =
  strongKEX (si.pmsId) &&
  Some? (prfMacAlg_of_ciphersuite_aux si.cipher_suite) && //NS: needed to add this ...
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
//  li_ch_ed_psk: PSK.pskid;       // 0-RT PSK
//  li_ch_ed_ae: a:aeAlg{AEAD? a}; // 0-RT AEAD alg
//  li_ch_ed_hash: h:hash_alg;     // 0-RT hash
  li_ch_psk: list PSK.pskid;     // other offered PSKs
}

type logInfo_SH = {
  li_sh_cr: crand;
  li_sh_sr: srand;
  li_sh_ae: a:aeAlg{AEAD? a}; // AEAD alg selected by the server
  li_sh_hash: h:hash_alg;     // Handshake hash selected by the server
  li_sh_psk: option PSK.pskid;// PSK selected by the server
}

type logInfo_SF = {
  li_sf_sh: logInfo_SH;
  li_sf_certificate: option Cert.chain;
}

type logInfo_CF = {
  li_cf_sf: logInfo_SF;
  li_cf_certificate: option Cert.chain;
}

type logInfo =
| LogInfo_CH of logInfo_CH
| LogInfo_SH of logInfo_SH
| LogInfo_SF of logInfo_SF
| LogInfo_CF of logInfo_CF

let logInfo_ae : x:logInfo{~(LogInfo_CH? x)} -> Tot (a:aeAlg{AEAD? a}) = function
| LogInfo_SH x -> x.li_sh_ae
| LogInfo_SF x -> x.li_sf_sh.li_sh_ae
| LogInfo_CF x -> x.li_cf_sf.li_sf_sh.li_sh_ae

let logInfo_nonce (rw:role) = function
| LogInfo_CH x -> x.li_ch_cr
| LogInfo_SH x -> x.li_sh_cr
| LogInfo_SF x -> x.li_sf_sh.li_sh_cr
| LogInfo_CF x -> x.li_cf_sf.li_sf_sh.li_sh_cr

// Extensional equality of logInfo
// (we may want to use e.g. equalBytes on some fields)
// injectivity
let eq_logInfo (la:logInfo) (lb:logInfo) : Tot bool =
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
  | ApplicationPSK: i:PSK.pskid -> ha:hash_alg{PSK.compatible_hash i ha} -> pre_esId
  | ResumptionPSK: i:pre_rmsId -> pre_esId
  | NoPSK: ha:hash_alg -> pre_esId

and pre_hsId =
  | HSID_PSK: pre_saltId -> pre_hsId // KEF_PRF idealized
  | HSID_DHE: pre_saltId -> g:CommonDH.group -> si:CommonDH.share g -> sr:CommonDH.share g -> pre_hsId // KEF_PRF_ODH idealized

and pre_asId =
  | ASID: pre_saltId -> pre_asId

and pre_saltId =
  | EarlySalt: pre_esId -> pre_saltId
  | HandshakeSalt: pre_hsId -> pre_saltId

and pre_secretId =
  | EarlySecretID: pre_esId -> pre_secretId
  | HandshakeSecretID: pre_hsId -> pre_secretId
  | ApplicationSecretID: pre_asId -> pre_secretId

and pre_rmsId =
  | RMSID: pre_asId -> logInfo -> hashed_log -> pre_rmsId

and pre_exportId =
  | ExportID: pre_asId -> logInfo -> hashed_log -> pre_exportId

and expandTag =
  | EarlyTrafficSecret
  | HandshakeTrafficSecret
  | ApplicationTrafficSecret
  | TrafficSecret

and pre_expandId =
  | ExpandedSecret: pre_secretId -> expandTag -> logInfo -> hashed_log -> pre_expandId

and keyTag =
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

val esId_hash: pre_esId -> Tot hash_alg
val hsId_hash: pre_hsId -> Tot hash_alg
val asId_hash: pre_asId -> Tot hash_alg
val saltId_hash: pre_saltId -> Tot hash_alg
val secretId_hash: pre_secretId -> Tot hash_alg
val rmsId_hash: pre_rmsId -> Tot hash_alg
val exportId_hash: pre_exportId -> Tot hash_alg
val expandId_hash: pre_expandId -> Tot hash_alg
val keyId_hash: pre_keyId -> Tot hash_alg
val finishedId_hash: pre_finishedId -> Tot hash_alg

let rec esId_hash = function
  | ApplicationPSK pskid h -> h
  | ResumptionPSK i -> rmsId_hash i
  | NoPSK h -> h

and hsId_hash = function
  | HSID_PSK i -> saltId_hash i
  | HSID_DHE i _ _ _ -> saltId_hash i

and asId_hash = function
  | ASID i -> saltId_hash i

and saltId_hash = function
  | EarlySalt i -> esId_hash i
  | HandshakeSalt i -> hsId_hash i

and secretId_hash = function
  | EarlySecretID i -> esId_hash i
  | HandshakeSecretID i -> hsId_hash i
  | ApplicationSecretID i -> asId_hash i

and rmsId_hash = function
  | RMSID asId _ _ -> asId_hash asId

and exportId_hash = function
  | ExportID asId _ _ -> asId_hash asId

and expandId_hash = function
  | ExpandedSecret i _ _ _ -> secretId_hash i

and keyId_hash = function
  | KeyID i _ _ _ _ -> expandId_hash i

and finishedId_hash = function
  | FinishedID i _ _ _ _ -> expandId_hash i

type valid_hlen (b:bytes) (h:hash_alg) =
  length b = Hashing.Spec.tagLen h

type pre_index =
| I_ES of pre_esId
| I_HS of pre_hsId
| I_AS of pre_asId
| I_SALT of pre_saltId
| I_SECRET of pre_secretId
| I_RMS of pre_rmsId
| I_EXPORT of pre_exportId
| I_EXPAND of pre_expandId
| I_KEY of pre_keyId
| I_FINISHED of pre_finishedId

type honest_index (i:pre_index) = bool

let safe_region:rgn = new_region tls_tables_region
private type i_safety_log = MM.t safe_region pre_index honest_index (fun _ -> True)
private type s_table = (if Flags.ideal_KEF then i_safety_log else unit)

let safety_table : s_table =
  (if Flags.ideal_KEF then
    MM.alloc #safe_region #pre_index #honest_index #(fun _ -> True)
  else ())

type registered (i:pre_index) =
  (if Flags.ideal_KEF then
    let log : i_safety_log = safety_table in
    MR.witnessed (MM.defined log i)
  else True)

type valid (i:pre_index) =
  (match i with
  | I_ES i ->
    (match i with
    | ApplicationPSK i _ -> PSK.registered_psk i
    | ResumptionPSK i -> registered (I_RMS i)
    | NoPSK _ -> True)
  | I_HS i ->
    (match i with
    | HSID_PSK i -> registered (I_SALT i)
    | HSID_DHE i g si sr -> registered (I_SALT i) /\ CommonDH.registered (|g,si|) /\ CommonDH.registered (|g,sr|))
  | I_AS i ->
    (match i with
    | ASID i -> registered (I_SALT i))
  | I_SALT i ->
    (match i with
    | EarlySalt i -> registered (I_ES i)
    | HandshakeSalt i -> registered (I_HS i))
  | I_SECRET i ->
    (match i with
    | EarlySecretID i -> registered (I_ES i)
    | HandshakeSecretID i -> registered (I_HS i)
    | ApplicationSecretID i -> registered (I_AS i))
  | I_RMS i ->
    (match i with
    | RMSID i _ _ -> registered (I_AS i))
  | I_EXPORT i ->
    (match i with
    | ExportID i _ _ -> registered (I_AS i))
  | I_EXPAND i ->
    (match i with
    | ExpandedSecret i _ _ _ -> registered (I_SECRET i))
  | I_KEY i ->
    (match i with
    | KeyID i _ _ _ _ -> registered (I_EXPAND i))
  | I_FINISHED i ->
    (match i with
    | FinishedID i _ _ _ _ -> registered (I_EXPAND i)))

type index = i:pre_index{valid i}

type honest (i:index) =
  (if Flags.ideal_KEF then
    let log : i_safety_log = safety_table in
    MR.witnessed (MM.contains log i true)
  else False)

type dishonest (i:index) =
  (if Flags.ideal_KEF then
    let log : i_safety_log = safety_table in
    MR.witnessed (MM.contains log i false)
  else True)

type esId = i:pre_esId{valid (I_ES i)}
type hsId = i:pre_hsId{valid (I_HS i)}
type asId = i:pre_asId{valid (I_AS i)}
type saltId = i:pre_saltId{valid (I_SALT i)}
type secretId = i:pre_secretId{valid (I_SECRET i)}
type rmsId = i:pre_rmsId{valid (I_RMS i)}
type exportId = i:pre_exportId{valid (I_EXPORT i)}
type expandId = i:pre_expandId{valid (I_EXPAND i)}
type keyId = i:pre_keyId{valid (I_KEY i)}
type finishedId = i:pre_finishedId{valid (I_FINISHED i)}

// Top-level index type for version-agile record keys
type id =
| PlaintextID: our_rand:random -> id // For IdNonce
| ID13: keyId:keyId -> id
| ID12: pv:protocolVersion{pv <> TLS_1p3} -> msId:msId -> kdfAlg:kdfAlg_t -> aeAlg: aeAlg -> cr:crand -> sr:srand -> writer:role -> id

let peerId = function
  | PlaintextID r -> PlaintextID r
  | ID12 pv msid kdf ae cr sr rw -> ID12 pv msid kdf ae cr sr (dualRole rw)
  | ID13 (KeyID i tag rw li log) ->
      let kid = KeyID i tag (dualRole rw) li log in
      assume(valid (I_KEY kid)); // Annoying: registration of keys as pairs
      ID13 kid

val siId: si:sessionInfo{
  Some? (prfMacAlg_of_ciphersuite_aux (si.cipher_suite)) /\
  si.protocol_version = TLS_1p2 /\
  pvcs si.protocol_version si.cipher_suite } -> role -> Tot id

let siId si r =
  let cr, sr = split (csrands si) 32 in
  ID12 si.protocol_version (msid si) (kdfAlg si.protocol_version si.cipher_suite) (siAuthEncAlg si) cr sr r

let pv_of_id (i:id{~(PlaintextID? i)}) = match i with
  | ID13 _ -> TLS_1p3
  | ID12 pv _ _ _ _ _ _ -> pv

// Returns the local nonce
let nonce_of_id = function
  | PlaintextID r -> r
  | ID12 _ _ _ _ cr sr rw -> if rw = Client then cr else sr
  | ID13 (KeyID _ _ rw li _) -> logInfo_nonce rw li

val kdfAlg_of_id: i:id { ID12? i } -> Tot kdfAlg_t
let kdfAlg_of_id = function
  | ID12 pv _ kdf _ _ _ _ -> kdf

val macAlg_of_id: i:id { ID12? i /\ ~(AEAD? (ID12?.aeAlg i)) } -> Tot macAlg
let macAlg_of_id = function
  | ID12 pv _ _ ae _ _ _ ->
    macAlg_of_aeAlg pv ae

val encAlg_of_id: i:id { ID12? i /\ MtE? (ID12?.aeAlg i) } -> Tot (encAlg * ivMode)
let encAlg_of_id = function
  | ID12 pv _ _ ae _ _ _ -> encAlg_of_aeAlg pv ae

val aeAlg_of_id: i:id { ~ (PlaintextID? i) } -> Tot aeAlg
let aeAlg_of_id = function
  | ID13 (KeyID _ _ _ li _) -> logInfo_ae li
  | ID12 pv _ _ ae _ _ _ -> ae

let lemma_MtE (i:id{~(PlaintextID? i)})
  : Lemma (MtE? (aeAlg_of_id i) ==> ID12? i)
  = ()

let lemma_ID13 (i:id)
  : Lemma (ID13? i ==> AEAD? (aeAlg_of_id i))
  = ()

let lemma_ID12 (i:id)
  : Lemma (ID12? i ==> pv_of_id i <> TLS_1p3)
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
abstract let authId = function
  | PlaintextID _ -> false
  | ID13 ki -> false // TODO
  | ID12 pv msid kdf ae cr sr rw -> false // TODO

abstract let safeId = function
  | PlaintextID _ -> false
  | ID13 ki -> false // TODO
  | ID12 pv msid kdf ae cr sr rw -> false // TODO

let plainText_is_not_auth (i:id)
  : Lemma (requires (PlaintextID? i))
          (ensures (not (authId i)))
	  [SMTPat (PlaintextID? i)]
  = ()

let safe_implies_auth (i:id)
  : Lemma (requires (safeId i))
          (ensures (authId i))
	  [SMTPat (authId i)]
  = admit()	   //TODO: need to prove that strongAEAlg implies strongAuthAlg
