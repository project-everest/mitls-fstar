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

noeq type pmsId = (* we use pmsId as an opaque index to pms *)
  | NoPmsId
  | SomePmsId of PMS.pms

let mk_pmsId (pms:PMS.pms) = SomePmsId(pms)

(* MK:
We could and probably should have:

    type pms' = i:index * (;i)pms

For example 'type index=int'.

When we generate a pms we choose a unique index i. Then pmsId could be defined as:

    type pmsId =
        | NoPmsId
        | SomePmsId of index

    let pmsId (i,pms) = SomePmsId(i)

What we have below is only possible because F7 allows comparison of
values with an abstract type because of an implementation error.
*)

// ``this pms is honestly generated and used only for extraction''
val honestPMS: pmsId -> Tot bool
let honestPMS = function
  | NoPmsId -> false
  | SomePmsId(PMS.RSAPMS(pk, cv, rsapms))   -> PMS.honestRSAPMS pk cv rsapms
  | SomePmsId(PMS.DHPMS(pg, gx, gy, dhpms)) -> false
                                               // todo, once we fix CommonDH vs DHGroup
                                               // PMS.honestDHPMS pg gx gy dhpms

val noPmsId: i:pmsId { not(honestPMS i) }
let noPmsId = NoPmsId

// Strengths of Handshake algorithms defined on pmsId
// Here we consider the strength of the parameters in pmsId
assume val strongKEX: pmsId -> Tot bool
(* todo, once we fix CommonDH vs DHGroup:
let strongKEX = function
  | NoPmsId -> false
  | SomePmsId(PMS.RSAPMS(pk,cv,rsapms))     -> RSAKey.strong cv
  | SomePmsId(PMS.DHPMS(pg, gx, gy, dhpms)) -> DHGroup.goodPP pg
 *)

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

noeq type msId = // We record the parameters used to derive the master secret;
  | StandardMS : pmsId -> csRands -> kefAlg_t -> msId
            // the pms index, the nonces, and the PMS-PRF algorithm
  | ExtendedMS : pmsId -> sessionHash -> kefAlg_t -> msId
            // the pms index, the hash of the session log, and the PMS-PRF algorithm
            // using the sessionHash instead of randoms prevent MiTM forwarding honest randoms

// ``the MS at this index is abstractly generated and used within PRF''
let honestMS = function
  | StandardMS pmsId csr ka -> honestPMS pmsId && strongKEF ka
  | ExtendedMS pmsId  sh ka -> honestPMS pmsId && strongKEF ka

//CF are we missing a correlation with csr?
//MK we don't allow leak, so every MS derived from an
//MK HonestPMS with strong KEF algorithms is honest?
//MK More uniformally this would go through a definition of SafeCRE.

val noMsId: i:msId { not (honestMS i) }
let noMsId = StandardMS noPmsId noCsr PRF_SSL3_nested

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
// Epoch descriptors (public immutable data)

type abbrInfo =
    {abbr_crand: crand;
     abbr_srand: srand;
     abbr_session_hash: sessionHash;
     abbr_vd: option (cVerifyData * sVerifyData) }

noeq type preEpoch =
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
let is_SuccEpoch e = is_FullEpoch e || is_AbbrEpoch e
type succEpoch = e:epoch { is_SuccEpoch e }

//$ also replaces function val Pred
val predEpoch: e: succEpoch -> Tot epoch
let predEpoch = function
  | FullEpoch _ pe
  | AbbrEpoch _ _ pe -> pe

//type openEpoch = epoch

// val peer: e:epoch -> Pure epoch (requires true) (ensures (fun r -> is_FullEpoch e ==> is_FullEpoch r))
val peer: e:epoch -> Tot (r:epoch {is_FullEpoch e ==> is_FullEpoch r})
let rec peer = function
  | InitEpoch r      -> InitEpoch (dualRole r)
  | FullEpoch si p   -> FullEpoch si (peer p)
  | AbbrEpoch ai r p -> AbbrEpoch ai (peer r) (peer p)

val epochSI: succEpoch -> Tot sessionInfo
let epochSI = function
  | FullEpoch si pe -> si
  | AbbrEpoch ai (FullEpoch si pe1) pe2 -> si

val epochAI: e:epoch { is_AbbrEpoch e } -> Tot abbrInfo
let epochAI e = AbbrEpoch.ai e

val epochSRand: succEpoch -> Tot srand
let epochSRand = function
  | FullEpoch si pe      -> si.init_srand
  | AbbrEpoch ri pe1 pe2 -> ri.abbr_srand

val epochCRand: succEpoch -> Tot crand
let epochCRand = function
  | FullEpoch si pe      -> si.init_crand
  | AbbrEpoch ai pe1 pe2 -> ai.abbr_crand

val epochCSRands: preEpoch -> Tot bytes
let epochCSRands e =
  let e' : succEpoch = unsafe_coerce e in //TODO: THIS FAILS CURRENTLY! FIXME
  epochCRand e' @| epochSRand e'

noeq type pre_connectionInfo = {
    role: role;      // cached, could be retrieved from id_out
    id_rand: random; // our random
    id_in: epoch;
    id_out: epoch}
type connectionInfo = pre_connectionInfo

//$ inline
let connectionRole ci = ci.role

val initConnection: role -> random -> Tot connectionInfo
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
// Indexing instances of derived keys for AE etc. 
//
// Intuitively, this is an abstract parameter for StatefulLHAE and
// StreamAE, used to control their idealization. 
// To this end, the index value should determine the concrete 
// initial state (key, IV) of the keyed functionality.

noeq type id = {
  // indexes and algorithms of the session used in the key derivation
  msId   : msId;            // the index of the master secret used for key derivation
  kdfAlg : kdfAlg_t;          // the KDF algorithm used for key derivation
  pv     : protocolVersion; // should be part of aeAlg
  aeAlg  : aeAlg;           // the authenticated-encryption algorithms
  // epoch-specific parameters
  csrConn: csRands;         // the client-server random of the connection
  ext: negotiatedExtensions;// the extensions negotiated for the current session
  writer : role             // the role of the writer
  }

let peerId (i:id) = { i with writer = dualRole i.writer }

//16-05-12 deprecated: let swap = peerId

val siId: si:sessionInfo{ 
  is_Some (prfMacAlg_of_ciphersuite_aux (si.cipher_suite)) /\ 
  si.protocol_version = TLS_1p2 /\
  pvcs si.protocol_version si.cipher_suite } -> role -> Tot id

let siId si r =
  { msId    = msid si;
    kdfAlg  = kdfAlg si.protocol_version si.cipher_suite;
    pv      = si.protocol_version; // for agility, consider together with aeAlg
    aeAlg   = siAuthEncAlg si;
    csrConn = csrands si;
    ext     = si.extensions;
    writer  = r;  }

 let unAuthIdInv (i:id):epoch = //NS: Remove this use of the pre-processor, please
 (*#if verify
     failwith "only creates epochs for bad ids"
 #else*)
     InitEpoch (i.writer)
 (*##endif*)

let pv_of_id (i:id) = i.pv //TODO MK fix

//$ also replacing MacAlg, EncAlg, PvOfId
val macAlg_of_id: i:id { pv_of_id i <> TLS_1p3 /\ ~(is_AEAD i.aeAlg) } -> Tot macAlg
let macAlg_of_id i = macAlg_of_aeAlg i.pv i.aeAlg

val encAlg_of_id: i:id { is_MtE i.aeAlg } -> Tot (encAlg * ivMode)
let encAlg_of_id i = encAlg_of_aeAlg i.pv i.aeAlg

let kdfAlg_of_id (i:id) = i.kdfAlg

// Pretty printing
let sinfo_to_string (si:sessionInfo) = ""
(*
#if 1 //TODO: This should be verify
#else
    let sb = new System.Text.StringBuilder() in
    let sb = sb.AppendLine("Session Information:") in
    let sb = sb.AppendLine(Printf.sprintf "Protocol Version: %A" si.protocol_version) in
    let sb = sb.AppendLine(Printf.sprintf "Ciphersuite: %A" (
                            match name_of_cipherSuite si.cipher_suite with
                            | Platform.Error.Error(_) -> failwith "Unknown ciphersuite"
                            | Platform.Error.Correct(c) -> c)) in
    let sb = sb.AppendLine(Printf.sprintf "Session ID: %s" (hexString si.sessionID)) in
    let sb = sb.AppendLine(Printf.sprintf "Session Hash: %s" (hexString si.session_hash)) in
    let sb = sb.AppendLine(Printf.sprintf "Server Identity: %s" (
                            match Cert.get_hint si.serverID with
                            | None -> "None"
                            | Some(c) -> c)) in
    let sb = sb.AppendLine(Printf.sprintf "Client Identity: %s" (
                            match Cert.get_hint si.clientID with
                            | None -> "None"
                            | Some(c) -> c)) in
    let sb = sb.AppendLine(Printf.sprintf "Extensions: %A" si.extensions) in
    sb.ToString()
##endif
 *)


// -----------------------------------------------------------------------
// record-layer length constants [5.2.1]
// note that TLS 1.3 lowers a bit the upper bound of cipher lengths (Ok in principle)
// but still enables padding beyond plausible plaintext lengths.

// API and protocol-level fragments are in [0..2^14]
let max_TLSPlaintext_fragment_length = 16384 

// the rest should be internal

// In TLS 1.2, compression and encryption may add stuff
let max_TLSCompressed_fragment_length = max_TLSPlaintext_fragment_length + 1024
let max_TLSCiphertext_fragment_length = max_TLSPlaintext_fragment_length + 2048

// The length of what's AE'ed, after adding the CT byte and padding
// in TLS 1.3, CT adds 1 byte, and AE adds up to 255 bytes
let max_TLSCiphertext_fragment_length_13 = max_TLSPlaintext_fragment_length + 256

val cipher_repr: n:nat -> Lemma( n <= max_TLSCiphertext_fragment_length ==> repr_bytes n <= 2 )
let cipher_repr n = lemma_repr_bytes_values n

// -----------------------------------------------------------------------
// Safety of key derivation depends on matching algorithms (see PRF)

//$ could be turnd into stateful logs; see F7 assumptions we made about them

assume logic type keyCommit   : csRands -> protocolVersion -> aeAlg -> negotiatedExtensions -> Type
assume logic type keyGenClient: csRands -> protocolVersion -> aeAlg -> negotiatedExtensions -> Type
assume logic type sentCCS     : role -> sessionInfo -> Type
assume logic type sentCCSAbbr : role -> abbrInfo -> Type

// ``the honest participants of handshake with this csr use matching aeAlgs''
type matches_id (i:id) =
    keyCommit i.csrConn i.pv i.aeAlg i.ext
    /\ keyGenClient i.csrConn i.pv i.aeAlg i.ext

//$ recode?
// This index is safe for MS-based key derivation
val safeKDF: i:id -> Tot (b:bool { b=true <==> ((honestMS i.msId && strongKDF i.kdfAlg) /\ matches_id i) })
//defining this as true makes the context inconsitent!
let safeKDF _ = unsafe_coerce false //TODO: THIS IS A PLACEHOLDER

// Needed for typechecking of PRF
// ask !i1,i2. i2 = Swap(i1) /\ not(SafeKDF(i1)) => not(SafeKDF(i2))

// HonestMS(msi) conditions both idealizations in PRF.
// ask !si:sessionInfo. not HonestMS(MsI(si)) => not SafeVD(si)
// ask !i:id. not HonestMS(i.msId) => not SafeKDF(i)

// -----------------------------------------------------------------------
// The two main safety properties for the record layer

let strongAuthId i = strongAuthAlg i.pv i.aeAlg
let strongAEId i   = strongAEAlg   i.pv i.aeAlg

// ``We are idealizing integrity/confidentiality for this id''
let authId (i:id) = safeKDF i && strongAuthId i
let safeId (i:id) = safeKDF i && strongAEId i

(* // ask !i.     SafeId(i) => AuthId(i) *)
(* // ask !i,mac. i.aeAlg  = MACOnly(mac) => not SafeId(i) *)
(* // ask !i:id. AuthId(i) => matches_id(i) // sanity check; just by definition *)
(* // ask !i:id. AuthId(i) => SafeKDF(i) *)
(* // ask !i:id. AuthId(i) => StrongAuthId(i) *)
(* // ask !i:id. AuthId(i) => INT_CMA_M(MacAlg(i)) *)
(* // ask !si,r:Role. StrongAuthSI(si) => StrongAuthId(siId si r) *)
(* // ask !i:id,e,m. StrongAuthId(i) => INT_CMA_M(MacAlg(i)) *)

// -------------------------------------------------------------------------
// Re-indexing from epochs to ids

val noId: i:id { ~(authId i) /\ ~(safeId i) }
let noId = {
  msId    = noMsId;
  kdfAlg  = PRF_SSL3_nested;
  pv      = SSL_3p0;
  aeAlg   = null_aeAlg;
  csrConn = noCsr;
  ext     = ne_default;
  writer  = Client }


val mk_id: e:epoch{ (not (is_InitEpoch e)) ==> is_CipherSuite ((epochSI e).cipher_suite) } -> Tot id
let mk_id e =
  if is_InitEpoch e then noId
  else
    let si     = epochSI e in
    let cs     = si.cipher_suite in
    { msId     = msid si;
      kdfAlg   = kdfAlg si.protocol_version si.cipher_suite;
      pv       = si.protocol_version;
      aeAlg    = get_aeAlg cs;
      csrConn  = epochCSRands e ;
      ext      = si.extensions;
      writer   = epochWriter e }

//ask !e. IsInitEpoch(e) => Id(e) = noId
//ask !e. IsInitEpoch(e) => not AuthId(Id(e))

// KB maybe we don't need this, but it helps in AppFragment for now
// val unAuthIdInv: i:id{not (authId i)} -> e:epoch {Id e = i}

// -------------------------------------------------------------------------
// Global safety properties

// Safety for handshakes depends on having an 'idealized' mastersecret,
// and performing both strong session key generation & finished message verification

// Safe handshake for this sessioninfo
let si_safeHS (si:sessionInfo) = 
  is_Some (prfMacAlg_of_ciphersuite_aux si.cipher_suite) /\ 
  si.protocol_version = TLS_1p2 /\
  pvcs si.protocol_version si.cipher_suite /\ 
  honestPMS si.pmsId /\
  strongHS si /\ 
  (exists r. matches_id (siId si r))

// Safety for epochs relies only on sessionInfo.
// This would change if we introduced a finer model of compromise
// e.g. if we allowed the attacker to compromise specific epochs

let epoch_safeHS (e:epoch) = is_SuccEpoch e /\ si_safeHS (epochSI e)
assume val safeHS: e:epoch -> b:bool { b = true <==> epoch_safeHS e }

// Predicates specifying the security of TLS connections

// ``The handshake is complete''
let epoch_open (e:epoch) = exists (r:role).
  (is_FullEpoch e /\ sentCCS r     (epochSI e) /\ sentCCS    (dualRole r) (epochSI e)) \/
  (is_AbbrEpoch e /\ sentCCSAbbr r (epochAI e) /\ sentCCSAbbr(dualRole r) (epochAI e))

let epoch_open_state (e:epoch) = exists (r:role).
  (((is_FullEpoch e /\ is_Some (prfMacAlg_of_ciphersuite_aux (epochSI e).cipher_suite) /\  sentCCS r     (epochSI e) /\ safeVD (epochSI e)) ==> sentCCS    (dualRole r) (epochSI e))) \/
  (((is_AbbrEpoch e /\ sentCCSAbbr r (epochAI e) /\ safeVD (epochSI e)) ==> sentCCSAbbr(dualRole r) (epochAI e)))

// The epoch parameters yield privacy & integrity
let epoch_safe (e:epoch) =  (not (is_InitEpoch e)) ==> is_CipherSuite ((epochSI e).cipher_suite) /\ safeId (mk_id e) /\ epoch_open_state e
assume val safe: e:epoch -> b:bool { b = true <==> epoch_safe e }

// The epoch parameters yield integrity (not necessarily privacy)
let epoch_auth (e:epoch) = (not (is_InitEpoch e)) ==> is_CipherSuite ((epochSI e).cipher_suite) /\ ((is_MtE (mk_id e).aeAlg) \/ (is_MACOnly (mk_id e).aeAlg /\ is_SSL_3p0 ((mk_id e).pv))) /\ authId (mk_id e) /\ epoch_open_state e
assume val auth: e:epoch -> b:bool { b = true <==> epoch_auth e }

//ask !e. Safe(e) => Auth(e)
//ask !e. not(Auth(e)) => not(Safe(e))

// so that TLS can exchange any traffic on the initial null connection
//ask !e. IsInitEpoch(e) => not Auth(e)

//ask !e. epoch_open_state(e) => (AuthId(Id(e)) => Auth(e))
//ask !e. epoch_open_state(e) => (SafeId(Id(e)) => Safe(e))
//ask !e. Auth(e) => epoch_open_state(e)


(*
  KB The following is only true with Reneg indication, but is difficult to remove.
  KB It is an artifact of the way we treat epochs that we cannot just authenticate the current epoch, we need to always authenticate the full chain
  KB Maybe a refactor for v2 would be to separate our the current epoch and an optional predecessor
  KB Also this needs to account for sentCCSResume
  
private theorem !r,r',e,e'. sentCCS(r,EpochSI(e)) /\
	                    sentCCS(r',EpochSI(e')) /\
  			    Id(e) = Id(e') => e = e'
theorem !e,e'. epoch_open_state(e) /\ epoch_open_state(e') /\ Id(e) = Id(e') => e = e'
 *)

(*
#if ideal
// These functions are used only for specifying ideal implementations
let safeHS (e:epoch) = failwith "spec only": bool
let safeHS_SI (e:sessionInfo) = failwith "spec only": bool
let safeCRE (e:sessionInfo) = failwith "spec only": bool
let safeVD (e:sessionInfo) = failwith "spec only": bool
let auth (e:epoch) = failwith "spec only": bool
let safe (e:epoch) = failwith "spec only" : bool //CF Define in terms of strength and honesty
let safeKDF (i:id) = failwith "spec only": bool
let authId (i:id) = failwith "spec only":bool
let safeId  (i:id) = failwith "spec only":bool
##endif
*)
