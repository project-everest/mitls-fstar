(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module MiTLS.TLSInfo
open MiTLS

#set-options "--max_fuel 3 --initial_fuel 3 --max_ifuel 1 --initial_ifuel 1"

(* This module gathers the definitions of
   public datatypes, parameters, and predicates for our TLS API.

   Its interface is used by most TLS modules;
   its implementation is typechecked.
*)

open MiTLS.Platform.Bytes
open MiTLS.Platform.Date
open MiTLS.TLSConstants
//open PMS
open MiTLS.Cert

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
// Polarity for reading and writing, e.g. for stateful encryption

type rw =
  | Reader
  | Writer

type role =
  | Client
  | Server

let dualRole = function
  | Client -> Server
  | Server -> Client

// -------------------------------------------------------------------
// Application configuration

type helloReqPolicy =
    | HRPIgnore
    | HRPFull
    | HRPResume

type config = {
    (* Supported versions, ciphersuites, and compressions *)
    minVer: protocolVersion;
    maxVer: protocolVersion;
    ciphersuites: x:known_cipher_suites{List.length x < 256};
    compressions: l:list Compression{ List.length l <= 1 };

    (* Handshake specific options *)

    (* Client side *)
    honourHelloReq: helloReqPolicy;
    allowAnonCipherSuite: bool;
    safe_resumption: bool;

    (* Server side *)
    request_client_certificate: bool;
    check_client_version_in_pms_for_old_tls: bool;

    (* Common *)
    safe_renegotiation: bool;
    server_name: UntrustedCert.hint;
    client_name: UntrustedCert.hint;

    (* Sessions database *)
    sessionDBFileName: string;
    sessionDBExpiry: TimeSpan;

    (* DH groups database *)
    dhDBFileName: string;
    dhDefaultGroupFileName: string;
    dhPQMinLength: nat * nat;

    (* ECDH settings *)
    ecdhGroups: list ECGroup.ec_curve;
    }

#set-options "--initial_fuel 10 --max_fuel 10"
let defaultConfig =
    let l =         [ TLS_RSA_WITH_AES_128_GCM_SHA256;
                      TLS_DHE_RSA_WITH_AES_128_GCM_SHA256;
                      TLS_DHE_DSS_WITH_AES_128_GCM_SHA256;
                      TLS_RSA_WITH_AES_128_CBC_SHA;
                      TLS_DHE_RSA_WITH_AES_128_CBC_SHA;
                      TLS_DHE_DSS_WITH_AES_128_CBC_SHA;
                      TLS_RSA_WITH_3DES_EDE_CBC_SHA;
                    ] in
    cut (List.length l == 7);//this requires 8 unfoldings
    let csn = cipherSuites_of_nameList l in
    {
    minVer = SSL_3p0;
    maxVer = TLS_1p2;
    ciphersuites = csn;
    compressions = [ NullCompression ];

    honourHelloReq = HRPResume;
    allowAnonCipherSuite = false;
    request_client_certificate = false;
    check_client_version_in_pms_for_old_tls = true;

    safe_renegotiation = true;
    safe_resumption = false; // Turn to true if it gets standard
    server_name = "mitls.example.org";
    client_name = "client.example.org";

    sessionDBFileName = "sessionDBFile.bin";
    sessionDBExpiry = newTimeSpan 1 0 0 0; (*@ one day, as suggested by the RFC *)

    dhDBFileName = DHDB.defaultFileName;
    dhDefaultGroupFileName = "default-dh.pem";
    dhPQMinLength = DHDB.defaultPQMinLength;

    ecdhGroups = [CoreCrypto.ECC_P256; CoreCrypto.ECC_P384; CoreCrypto.ECC_P521];
    }
#reset-options

// -------------------------------------------------------------------
// Client/Server randomness (implemented in Nonce)

// their first 4 bytes give the local time,
// so that they are locally pairwise-distinct
type random = lbytes 32
type crand = random
type srand = random
type csRands = bytes

type cVerifyData = bytes (* ClientFinished payload *)
type sVerifyData = bytes (* ServerFinished payload *)

type sessionHash = bytes

let noCsr:csRands = Nonce.noCsr

// -------------------------------------------------------------------
// We support these extensions, with session scopes
// (defined here because TLSExtension is internal)

type serverName =
| SNI_DNS of bytes
| SNI_UNKNOWN of int * bytes

type negotiatedExtensions = {
    ne_extended_ms: bool;
    ne_extended_padding:bool;
    ne_renegotiation_info: option (cVerifyData * sVerifyData);

    //$ Cedric: these extensions were missing in F7.
    ne_supported_curves: option (list ECGroup.ec_curve);
    ne_supported_point_formats: option (list ECGroup.point_format);
    ne_server_names: option (list serverName);
}

let ne_default =
{
    ne_extended_ms = false;
    ne_extended_padding = false;
    ne_renegotiation_info = None;
    ne_supported_curves = None;
    ne_supported_point_formats = None;
    ne_server_names = None;
}

// -------------------------------------------------------------------
// Pre Master Secret indexes

type pmsId = (* we use pmsId as an opaque index to pms *)
  | NoPmsId
  | SomePmsId of PMS.pms

let mk_pmsId (pms:PMS.pms) = SomePmsId(pms)

// ``this pms is honestly generated and used only for extraction''
val honestPMS: pmsId -> Tot bool
let honestPMS = function
  | NoPmsId -> false
  | SomePmsId(PMS.RSAPMS(pk, cv, rsapms))   -> PMS.honestRSAPMS pk cv rsapms
  | SomePmsId(PMS.DHPMS(pg, gx, gy, dhpms)) -> false

val noPmsId: i:pmsId { not(honestPMS i) }
let noPmsId = NoPmsId

// Strengths of Handshake algorithms defined on pmsId
// Here we consider the strength of the parameters in pmsId
assume val strongKEX: pmsId -> Tot bool

// -------------------------------------------------------------------
// Master Secret indexes and their properties

// ``kefAlg is a strong randomness extractor, despite all other kefAlgs'', guarding idealization in KEF

assume val strongKEF: kefAlg -> Tot bool

// guarding idealizations for KDF and VerifyData (see PRF.fs)
assume val strongKDF: kdfAlg -> Tot bool
assume val strongVD: vdAlg -> Tot bool

// -------------------------------------------------------------------
// Session information (public immutable data)

type sessionID = b:bytes { length b <= 32 }
// ``An arbitrary byte sequence chosen by the server
// to identify an active or resumable session state.''

type sessionInfo = {
    init_crand: crand;
    init_srand: srand;
    protocol_version: protocolVersion;
    cipher_suite: cipherSuite;
    compression: Compression;
    extensions: negotiatedExtensions;
    pmsId: pmsId;
    session_hash: sessionHash;
    client_auth: bool;
    clientID: Cert.chain;
    clientSigAlg: Sig.alg;
    serverID: Cert.chain;
    serverSigAlg: Sig.alg;
    sessionID: sessionID;
    }

// for sessionID. we treat empty bytes as the absence of identifier,
// i.e. the session is not resumable.

// for certificates, the empty list represents the absence of identity
// (possibly refusing to present requested certs)

val csrands: sessionInfo -> Tot csRands
let csrands si = si.init_crand @| si.init_srand

// Getting algorithms from sessionInfo

val kefAlg: si:sessionInfo { Some? (prfMacAlg_of_ciphersuite_aux si.cipher_suite) } -> Tot kefAlg
let kefAlg si =
  match si.protocol_version with
  | SSL_3p0           -> PRF_SSL3_nested
  | TLS_1p0 | TLS_1p1 -> PRF_TLS_1p01 extract_label
  | TLS_1p2           -> PRF_TLS_1p2 extract_label (prfMacAlg_of_ciphersuite si.cipher_suite)

val kefAlgExtended: si:sessionInfo { Some? (prfMacAlg_of_ciphersuite_aux si.cipher_suite) } -> Tot kefAlg
let kefAlgExtended si =
  match si.protocol_version with
  | SSL_3p0           -> PRF_SSL3_nested
  | TLS_1p0 | TLS_1p1 -> PRF_TLS_1p01 extended_extract_label
  | TLS_1p2           -> PRF_TLS_1p2 extended_extract_label (prfMacAlg_of_ciphersuite si.cipher_suite)

val kdfAlg: si:sessionInfo { Some? (prfMacAlg_of_ciphersuite_aux si.cipher_suite) } -> Tot kdfAlg
let kdfAlg si =
  match si.protocol_version with
  | SSL_3p0           -> PRF_SSL3_nested
  | TLS_1p0 | TLS_1p1 -> PRF_TLS_1p01 kdf_label
  | TLS_1p2           -> PRF_TLS_1p2 kdf_label (prfMacAlg_of_ciphersuite si.cipher_suite)

let vdAlg si = si.protocol_version, si.cipher_suite

val siAuthEncAlg: si:sessionInfo { si.protocol_version = TLS_1p2 &&
                              pvcs si.protocol_version si.cipher_suite } -> Tot aeAlg
let siAuthEncAlg si = get_aeAlg si.cipher_suite

type msId = // We record the parameters used to derive the master secret;
  | StandardMS : pmsId -> csRands -> kefAlg -> msId
            // the pms index, the nonces, and the PMS-PRF algorithm
  | ExtendedMS : pmsId -> sessionHash -> kefAlg -> msId
            // the pms index, the hash of the session log, and the PMS-PRF algorithm
            // using the sessionHash instead of randoms prevent MiTM forwarding honest randoms

// ``the MS at this index is abstractly generated and used within PRF''
let honestMS = function
  | StandardMS pmsId csr ka -> honestPMS pmsId && strongKEF ka
  | ExtendedMS pmsId  sh ka  -> honestPMS pmsId && strongKEF ka

val noMsId: i:msId { not (honestMS i) }
let noMsId = StandardMS noPmsId noCsr PRF_SSL3_nested

// Getting master-secret indexes out of sessionInfo

val msid: si:sessionInfo { Some? (prfMacAlg_of_ciphersuite_aux (si.cipher_suite)) } -> Tot msId
let msid si =
  if si.extensions.ne_extended_ms
  then ExtendedMS si.pmsId si.session_hash (kefAlgExtended si)
  else StandardMS si.pmsId    (csrands si) (kefAlg si)

// Strengths of Handshake algorithms
assume val sigHashAlg_of_ciphersuite: cipherSuite -> Tot sigHashAlg
let strongSig si = Sig.strong (sigHashAlg_of_ciphersuite si.cipher_suite)

// ``The algorithms of si are strong for both KDF and VerifyData, despite all others''
// guarding idealization in PRF
let strongPRF si = strongKDF(kdfAlg si) && strongVD(vdAlg si)

// Summarizing all assumptions needed for a strong handshake

let strongHS si =
  strongKEX (si.pmsId) &&
  strongKEF (kefAlg si) &&
  strongPRF si &&
  strongSig si

// Safety of sessionInfo crypto processing

// Safe handshake for PMS-based extraction
let safeCRE si = honestMS (msid si)

// Safe handshake for MS-based VerifyData
let safeVD si = honestMS (msid si) && strongVD(vdAlg si)

assume val int_cma: macAlg -> Tot bool
let strongAuthSI si = true

assume val strongAESI: sessionInfo -> Tot bool

// -------------------------------------------------------------------
// Epoch descriptors (public immutable data)

type abbrInfo =
    {abbr_crand: crand;
     abbr_srand: srand;
     abbr_session_hash: sessionHash;
     abbr_vd: option (cVerifyData * sVerifyData) }

(* NS: TODO ... migrate these to curried style data constructors *)
type preEpoch =
    | InitEpoch of role
    | FullEpoch : sessionInfo  -> preEpoch -> preEpoch
    | AbbrEpoch : ai:abbrInfo -> resumed:preEpoch -> pred:preEpoch -> preEpoch

(* previously the last two cases were
    | SuccEpoch of crand * srand * si:sessionInfo * pred:preEpoch
 *)

(* we enforce a well-formed invariant to ensure the functions below
   are total; we could also restructure epoch.*)

val validEpoch: preEpoch -> Tot bool
let rec validEpoch = function
  | InitEpoch _ -> true
  | FullEpoch _ pred -> validEpoch pred
  | AbbrEpoch _ (FullEpoch si pred0) pred -> validEpoch pred0 && validEpoch pred
  | AbbrEpoch _ _ _           -> false
type epoch = e:preEpoch { validEpoch e }

//$ removed isInitEpoch etc.
let SuccEpoch? e = FullEpoch? e || AbbrEpoch? e
type succEpoch = e:epoch { SuccEpoch? e }

//$ also replaces function val Pred
val predEpoch: e: succEpoch -> Tot epoch
let predEpoch = function
  | FullEpoch _ pe
  | AbbrEpoch _ _ pe -> pe

//type openEpoch = epoch

// val peer: e:epoch -> Pure epoch (requires true) (ensures (fun r -> FullEpoch? e ==> FullEpoch? r))
val peer: e:epoch -> Tot (r:epoch {FullEpoch? e ==> FullEpoch? r})
let rec peer = function
  | InitEpoch r      -> InitEpoch (dualRole r)
  | FullEpoch si p   -> FullEpoch si (peer p)
  | AbbrEpoch ai r p -> AbbrEpoch ai (peer r) (peer p)

val epochSI: succEpoch -> Tot sessionInfo
let epochSI = function
  | FullEpoch si pe -> si
  | AbbrEpoch ai (FullEpoch si pe1) pe2 -> si

val epochAI: e:epoch { AbbrEpoch? e } -> Tot abbrInfo
let epochAI e = AbbrEpoch?.ai e

val epochSRand: succEpoch -> Tot srand
let epochSRand = function
  | FullEpoch si pe      -> si.init_srand
  | AbbrEpoch ri pe1 pe2 -> ri.abbr_srand

val epochCRand: succEpoch -> Tot crand
let epochCRand = function
  | FullEpoch si pe      -> si.init_crand
  | AbbrEpoch ai pe1 pe2 -> ai.abbr_crand

let epochCSRands e = epochCRand e @| epochSRand e

type pre_connectionInfo = {
    role: role;      // cached, could be retrieved from id_out
    id_rand: random; // our random
    id_in: epoch;
    id_out: epoch}
type connectionInfo = pre_connectionInfo

//$ inline
let connectionRole ci = ci.role

let initConnection role rand =
    let ctos = InitEpoch Client in
    let stoc = InitEpoch Server in
    match role with
    | Client -> {role = Client; id_rand = rand; id_in = stoc; id_out = ctos}
    | Server -> {role = Server; id_rand = rand; id_in = ctos; id_out = stoc}

let fullEpoch epoch si = FullEpoch si epoch
let abbrEpoch epoch1 ai si epoch2 = AbbrEpoch ai (FullEpoch si epoch2) epoch1

val epochWriter: epoch -> Tot role
let rec epochWriter (e:epoch) =
    match e with
    | InitEpoch r     -> r
    | FullEpoch _ e   -> epochWriter e
    | AbbrEpoch _ _ e -> epochWriter e

let strongAuth e = strongAuthSI (epochSI e)
let strongAE e = strongAESI (epochSI e)

// -------------------------------------------------------------------
// indexing instances of AE --- an abstract parameter for StatefulAEAD et al
// we do not use more detailed epochs as their additional contents
// is authenticated only once the handshake completes.

type id = {
  // indexes and algorithms of the session used in the key derivation
  msId   : msId;            // the index of the master secret used for key derivation
  kdfAlg : kdfAlg;          // the KDF algorithm used for key derivation
  pv     : protocolVersion; // should be part of aeAlg
  aeAlg  : aeAlg;           // the authenticated-encryption algorithms
  // epoch-specific parameters
  csrConn: csRands;         // the client-server random of the connection
  ext: negotiatedExtensions; // the extensions negotiated for the current session
  writer : role             // the role of the writer
  }

let swap (i:id) = { i with writer = dualRole i.writer }

val siId: si:sessionInfo{ Some? (prfMacAlg_of_ciphersuite_aux (si.cipher_suite))
			  /\ ((si.protocol_version = TLS_1p2) && (pvcs si.protocol_version si.cipher_suite))} -> role -> Tot id
let siId si r =
  { msId    = msid si;
    kdfAlg  = kdfAlg si;
    pv      = si.protocol_version; // for agility, consider together with aeAlg
    aeAlg   = siAuthEncAlg si;
    csrConn = csrands si;
    ext     = si.extensions;
    writer  = r;  }

 let unAuthIdInv (i:id):epoch = 
     InitEpoch (i.writer)

//$ also replacing MacAlg, EncAlg, PvOfId
val macAlg_of_id: i:id { ~(AEAD? i.aeAlg) } -> Tot macAlg
let macAlg_of_id i = macAlg_of_aeAlg i.pv i.aeAlg

val encAlg_of_id: i:id { MtE? i.aeAlg } -> Tot (encAlg * ivMode)
let encAlg_of_id i = encAlg_of_aeAlg i.pv i.aeAlg

let pv_of_id (i:id) = i.pv
let kdfAlg_of_id (i:id) = i.kdfAlg

// Pretty printing
let sinfo_to_string (si:sessionInfo) = ""

let max_TLSPlaintext_fragment_length = 16384 (*@ 2^14 *)
let max_TLSCompressed_fragment_length = max_TLSPlaintext_fragment_length + 1024
let max_TLSCipher_fragment_length = max_TLSCompressed_fragment_length + 1024
let fragmentLength = max_TLSPlaintext_fragment_length

val cipher_repr: n:nat -> Lemma( n <= max_TLSCipher_fragment_length ==> repr_bytes n <= 2 )
let cipher_repr n = lemma_repr_bytes_values n

// -----------------------------------------------------------------------
// Safety of key derivation depends on matching algorithms (see PRF)

assume logic type keyCommit   : csRands -> protocolVersion -> aeAlg -> negotiatedExtensions -> Type
assume logic type keyGenClient: csRands -> protocolVersion -> aeAlg -> negotiatedExtensions -> Type
assume logic type sentCCS     : role -> sessionInfo -> Type
assume logic type sentCCSAbbr : role -> abbrInfo -> Type

// ``the honest participants of handshake with this csr use matching aeAlgs''
type matches_id (i:id) =
    keyCommit i.csrConn i.pv i.aeAlg i.ext
    /\ keyGenClient i.csrConn i.pv i.aeAlg i.ext

// This index is safe for MS-based key derivation
assume val safeKDF: i:id -> Tot (b:bool { b=true <==> ((honestMS i.msId && strongKDF i.kdfAlg) /\ matches_id i) })

// -----------------------------------------------------------------------
// The two main safety properties for the record layer

let strongAuthId i = strongAuthAlg i.pv i.aeAlg
let strongAEId i   = strongAEAlg   i.pv i.aeAlg

// ``We are idealizing integrity/confidentiality for this id''
let authId (i:id) = safeKDF i && strongAuthId i
let safeId (i:id) = safeKDF i && strongAEId i

// -------------------------------------------------------------------------
// Re-indexing from epochs to ids

val noId: i:id { ~(authId i) }
let noId = {
  msId    = noMsId;
  kdfAlg  = PRF_SSL3_nested;
  pv      = SSL_3p0;
  aeAlg   = null_aeAlg;
  csrConn = noCsr;
  ext     = ne_default;
  writer  = Client }

val mk_id: e:epoch{ (not (InitEpoch? e)) ==> CipherSuite? ((epochSI e).cipher_suite) } -> Tot id
let mk_id e =
  if InitEpoch? e then noId
  else
    let si     = epochSI e in
    let cs     = si.cipher_suite in
    { msId     = msid si;
      kdfAlg   = kdfAlg si;
      pv       = si.protocol_version;
      aeAlg    = get_aeAlg cs;
      csrConn  = epochCSRands e ;
      ext      = si.extensions;
      writer   = epochWriter e }

// -------------------------------------------------------------------------
// Global safety properties

// Safety for handshakes depends on having an 'idealized' mastersecret,
// and performing both strong session key generation & finished message verification

// Safe handshake for this sessioninfo
type SafeHS_SI (si:sessionInfo) = ((Some? (prfMacAlg_of_ciphersuite_aux (si.cipher_suite))) /\ (((si.protocol_version) = TLS_1p2) && (pvcs (si.protocol_version) (si.cipher_suite)))) /\ (honestPMS si.pmsId && strongHS si) /\ (exists r. matches_id(siId si r))

// Safety for epochs relies only on sessionInfo.
// This would change if we introduced a finer model of compromise
// e.g. if we allowed the attacker to compromise specific epochs

type SafeHS (e:epoch) = SuccEpoch? e /\ SafeHS_SI(epochSI e)
assume val safeHS: e:epoch -> b:bool { b = true <==> SafeHS e }

// Predicates specifying the security of TLS connections

// ``The handshake is complete''
type Open (e:epoch) = ( exists (r:role).
  (FullEpoch? e /\ sentCCS r     (epochSI e) /\ sentCCS    (dualRole r) (epochSI e)) \/
  (AbbrEpoch? e /\ sentCCSAbbr r (epochAI e) /\ sentCCSAbbr(dualRole r) (epochAI e)))

type OpenState (e:epoch) = ( exists (r:role).
  (((FullEpoch? e /\ Some? (prfMacAlg_of_ciphersuite_aux (epochSI e).cipher_suite) /\  sentCCS r     (epochSI e) /\ safeVD (epochSI e)) ==> sentCCS    (dualRole r) (epochSI e))) \/
  (((AbbrEpoch? e /\ sentCCSAbbr r (epochAI e) /\ safeVD (epochSI e)) ==> sentCCSAbbr(dualRole r) (epochAI e))))

// The epoch parameters yield privacy & integrity
type Safe (e:epoch) =  (not (InitEpoch? e)) ==> CipherSuite? ((epochSI e).cipher_suite) /\ safeId (mk_id e) /\ OpenState e
assume val safe: e:epoch -> b:bool { b = true <==> Safe e }

// The epoch parameters yield integrity (not necessarily privacy)
type Auth (e:epoch) = (not (InitEpoch? e)) ==> CipherSuite? ((epochSI e).cipher_suite) /\ ((MtE? (mk_id e).aeAlg) \/ (MACOnly? (mk_id e).aeAlg /\ SSL_3p0? ((mk_id e).pv))) /\ authId (mk_id e) /\ OpenState e
assume val auth: e:epoch -> b:bool { b = true <==> Auth e }
