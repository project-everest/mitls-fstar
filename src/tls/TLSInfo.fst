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
// TODO Consider repackaging separate client and server options

type helloReqPolicy =
    | HRPIgnore
    | HRPFull
    | HRPResume

type config = {
    (* Supported versions, ciphersuites, and compressions *)
    minVer: ProtocolVersion;
    maxVer: ProtocolVersion;
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
type CsRands = bytes

type cVerifyData = bytes (* ClientFinished payload *)
type sVerifyData = bytes (* ServerFinished payload *)

type sessionHash = bytes

let noCsr:CsRands = Nonce.noCsr

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

assume val strongKEF: KefAlg -> Tot bool

// guarding idealizations for KDF and VerifyData (see PRF.fs)
assume val strongKDF: KdfAlg -> Tot bool
assume val strongVD: VdAlg -> Tot bool

// -------------------------------------------------------------------
// Session information (public immutable data)

type sessionID = b:bytes { length b <= 32 }
// ``An arbitrary byte sequence chosen by the server
// to identify an active or resumable session state.''

type SessionInfo = {
    init_crand: crand;
    init_srand: srand;
    protocol_version: ProtocolVersion;
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

val csrands: SessionInfo -> Tot CsRands
let csrands si = si.init_crand @| si.init_srand
//CF subsumes mk_csrands

// Getting algorithms from SessionInfo
//CF subsume mk_kefAlg, mk_kefAlgExtended, mk_kdfAlg
val kefAlg: si:SessionInfo { is_Some (prfMacAlg_of_ciphersuite_aux si.cipher_suite) } -> Tot KefAlg
let kefAlg si =
  match si.protocol_version with
  | SSL_3p0           -> PRF_SSL3_nested
  | TLS_1p0 | TLS_1p1 -> PRF_TLS_1p01 extract_label
  | TLS_1p2           -> PRF_TLS_1p2 extract_label (prfMacAlg_of_ciphersuite si.cipher_suite)

val kefAlgExtended: si:SessionInfo { is_Some (prfMacAlg_of_ciphersuite_aux si.cipher_suite) } -> Tot KefAlg
let kefAlgExtended si =
  match si.protocol_version with
  | SSL_3p0           -> PRF_SSL3_nested
  | TLS_1p0 | TLS_1p1 -> PRF_TLS_1p01 extended_extract_label
  | TLS_1p2           -> PRF_TLS_1p2 extended_extract_label (prfMacAlg_of_ciphersuite si.cipher_suite)

val kdfAlg: si:SessionInfo { is_Some (prfMacAlg_of_ciphersuite_aux si.cipher_suite) } -> Tot KdfAlg
let kdfAlg si =
  match si.protocol_version with
  | SSL_3p0           -> PRF_SSL3_nested
  | TLS_1p0 | TLS_1p1 -> PRF_TLS_1p01 kdf_label
  | TLS_1p2           -> PRF_TLS_1p2 kdf_label (prfMacAlg_of_ciphersuite si.cipher_suite)

let vdAlg si = si.protocol_version, si.cipher_suite

val siAuthEncAlg: si:SessionInfo { si.protocol_version = TLS_1p2 &&
                              pvcs si.protocol_version si.cipher_suite } -> Tot aeAlg
let siAuthEncAlg si = get_aeAlg si.cipher_suite

type msId = // We record the parameters used to derive the master secret;
  | StandardMS : pmsId -> CsRands -> KefAlg -> msId
            // the pms index, the nonces, and the PMS-PRF algorithm
  | ExtendedMS : pmsId -> sessionHash -> KefAlg -> msId
            // the pms index, the hash of the session log, and the PMS-PRF algorithm
            // using the sessionHash instead of randoms prevent MiTM forwarding honest randoms

// ``the MS at this index is abstractly generated and used within PRF''
let honestMS = function
  | StandardMS pmsId csr ka -> honestPMS pmsId && strongKEF ka
  | ExtendedMS pmsId  sh ka  -> honestPMS pmsId && strongKEF ka

//CF are we missing a correlation with csr?
//MK we don't allow leak, so every MS derived from an
//MK HonestPMS with strong KEF algorithms is honest?
//MK More uniformally this would go through a definition of SafeCRE.

val noMsId: i:msId { not (honestMS i) }
let noMsId = StandardMS noPmsId noCsr PRF_SSL3_nested

// Getting master-secret indexes out of SessionInfo

//CF subsumes both MsI and mk_msid
val msid: si:SessionInfo { is_Some (prfMacAlg_of_ciphersuite_aux (si.cipher_suite)) } -> Tot msId
let msid si =
  if si.extensions.ne_extended_ms
  then ExtendedMS si.pmsId si.session_hash (kefAlgExtended si)
  else StandardMS si.pmsId    (csrands si) (kefAlg si)

// Strengths of Handshake algorithms
// NS: identifier not found: sigHashAlg_of_cipherSuite
assume val sigHashAlg_of_ciphersuite: cipherSuite -> Tot sigHashAlg
let strongSig si = Sig.strong (sigHashAlg_of_ciphersuite si.cipher_suite)

// ``The algorithms of si are strong for both KDF and VerifyData, despite all others''
// guarding idealization in PRF
let strongPRF si = strongKDF(kdfAlg si) && strongVD(vdAlg si)
// MK I think having this joint strength predicate
// MK guaranteeing the idealization of the complete module is useful

// Summarizing all assumptions needed for a strong handshake
// CF derived & to be used in the public API only
let strongHS si =
  strongKEX (si.pmsId) &&
  strongKEF (kefAlg si) &&
  strongPRF si &&
  strongSig si  //CF * hashAlg for certs?

// Safety of SessionInfo crypto processing

// Safe handshake for PMS-based extraction
let safeCRE si = honestMS (msid si)

// Safe handshake for MS-based VerifyData
let safeVD si = honestMS (msid si) && strongVD(vdAlg si)
//MK: safeVD is used for idealization even if ciphersuites don't match.
//MK: this is needed to guarantee security of finished message MACs

assume val int_cma: macAlg -> Tot bool
let strongAuthSI si = true //TODO: fix

assume val strongAESI: SessionInfo -> Tot bool

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
    | FullEpoch : SessionInfo  -> preEpoch -> preEpoch
    | AbbrEpoch : ai:abbrInfo -> resumed:preEpoch -> pred:preEpoch -> preEpoch

(* previously the last two cases were
    | SuccEpoch of crand * srand * si:SessionInfo * pred:preEpoch
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

val epochSI: succEpoch -> Tot SessionInfo
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

let epochCSRands e = epochCRand e @| epochSRand e

type preConnectionInfo = {
    role: role;      // cached, could be retrieved from id_out
    id_rand: random; // our random
    id_in: epoch;
    id_out: epoch}
type ConnectionInfo = preConnectionInfo

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

//NS:Verifies up to here
let strongAuth e = strongAuthSI (epochSI e)
let strongAE e = strongAESI (epochSI e)

// -------------------------------------------------------------------
// indexing instances of AE --- an abstract parameter for StatefulAEAD et al
// we do not use more detailed epochs as their additional contents
// is authenticated only once the handshake completes.

type id = {
  // indexes and algorithms of the session used in the key derivation
  msId   : msId;            // the index of the master secret used for key derivation
  kdfAlg : KdfAlg;          // the KDF algorithm used for key derivation
  pv     : ProtocolVersion; // should be part of aeAlg
  aeAlg  : aeAlg;           // the authenticated-encryption algorithms
  // epoch-specific parameters
  csrConn: CsRands;         // the client-server random of the connection
  ext: negotiatedExtensions; // the extensions negotiated for the current session
  writer : role             // the role of the writer
  }

let swap (i:id) = { i with writer = dualRole i.writer }

val siId: si:SessionInfo{ is_Some (prfMacAlg_of_ciphersuite_aux (si.cipher_suite))
			  /\ ((si.protocol_version = TLS_1p2) && (pvcs si.protocol_version si.cipher_suite))} -> role -> Tot id
let siId si r =
  { msId    = msid si;
    kdfAlg  = kdfAlg si;
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

//$ also replacing MacAlg, EncAlg, PvOfId
val macAlg_of_id: i:id { ~(is_AEAD i.aeAlg) } -> Tot macAlg
let macAlg_of_id i = macAlg_of_aeAlg i.pv i.aeAlg

val encAlg_of_id: i:id { is_MtE i.aeAlg } -> Tot (encAlg * ivMode)
let encAlg_of_id i = encAlg_of_aeAlg i.pv i.aeAlg

let pv_of_id (i:id) = i.pv //TODO MK fix
let kdfAlg_of_id (i:id) = i.kdfAlg

// Pretty printing
let sinfo_to_string (si:SessionInfo) = ""
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

// SZ: Why is this not rather in TLSConstants?
let max_TLSPlaintext_fragment_length = 16384 (*@ 2^14 *)
let max_TLSCompressed_fragment_length = max_TLSPlaintext_fragment_length + 1024
let max_TLSCipher_fragment_length = max_TLSCompressed_fragment_length + 1024
let fragmentLength = max_TLSPlaintext_fragment_length

val cipher_repr: n:nat -> Lemma( n <= max_TLSCipher_fragment_length ==> repr_bytes n <= 2 )
let cipher_repr n = lemma_repr_bytes_values n

// -----------------------------------------------------------------------
// Safety of key derivation depends on matching algorithms (see PRF)

//$ could be turnd into stateful logs; see F7 assumptions we made about them

assume logic type KeyCommit   : CsRands -> ProtocolVersion -> aeAlg -> negotiatedExtensions -> Type
assume logic type KeyGenClient: CsRands -> ProtocolVersion -> aeAlg -> negotiatedExtensions -> Type
assume logic type SentCCS     : role -> SessionInfo -> Type
assume logic type SentCCSAbbr : role -> abbrInfo -> Type

// ``the honest participants of handshake with this csr use matching aeAlgs''
type Match (i:id) =
    KeyCommit i.csrConn i.pv i.aeAlg i.ext
    /\ KeyGenClient i.csrConn i.pv i.aeAlg i.ext

//$ recode?
// This index is safe for MS-based key derivation
assume val safeKDF: i:id -> Tot (b:bool { b=true <==> ((honestMS i.msId && strongKDF i.kdfAlg) /\ Match i) })

// Needed for typechecking of PRF
// ask !i1,i2. i2 = Swap(i1) /\ not(SafeKDF(i1)) => not(SafeKDF(i2))

// HonestMS(msi) conditions both idealizations in PRF.
// ask !si:SessionInfo. not HonestMS(MsI(si)) => not SafeVD(si)
// ask !i:id. not HonestMS(i.msId) => not SafeKDF(i)

// -----------------------------------------------------------------------
// The two main safety properties for the record layer

let strongAuthId i = strongAuthAlg i.pv i.aeAlg
let strongAEId i   = strongAEAlg   i.pv i.aeAlg

// ``We are idealizing integrity/confidentiality for this id''
let authId (i:id) = safeKDF i && strongAuthId i
let safeId (i:id) = safeKDF i && strongAEId i

// ask !i.     SafeId(i) => AuthId(i)
// ask !i,mac. i.aeAlg  = MACOnly(mac) => not SafeId(i)
// ask !i:id. AuthId(i) => Match(i) // sanity check; just by definition
// ask !i:id. AuthId(i) => SafeKDF(i)
// ask !i:id. AuthId(i) => StrongAuthId(i)
// ask !i:id. AuthId(i) => INT_CMA_M(MacAlg(i))
// ask !si,r:Role. StrongAuthSI(si) => StrongAuthId(siId si r)
// ask !i:id,e,m. StrongAuthId(i) => INT_CMA_M(MacAlg(i))

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


val mk_id: e:epoch{ (not (is_InitEpoch e)) ==> is_CipherSuite ((epochSI e).cipher_suite) } -> Tot id
let mk_id e =
  if is_InitEpoch e then noId
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

//ask !e. IsInitEpoch(e) => Id(e) = noId
//ask !e. IsInitEpoch(e) => not AuthId(Id(e))

// KB maybe we don't need this, but it helps in AppFragment for now
// val unAuthIdInv: i:id{not (authId i)} -> e:epoch {Id e = i}

// -------------------------------------------------------------------------
// Global safety properties

// Safety for handshakes depends on having an 'idealized' mastersecret,
// and performing both strong session key generation & finished message verification

// Safe handshake for this sessioninfo
type SafeHS_SI (si:SessionInfo) = ((is_Some (prfMacAlg_of_ciphersuite_aux (si.cipher_suite))) /\ (((si.protocol_version) = TLS_1p2) && (pvcs (si.protocol_version) (si.cipher_suite)))) /\ (honestPMS si.pmsId && strongHS si) /\ (exists r. Match(siId si r))

// Safety for epochs relies only on SessionInfo.
// This would change if we introduced a finer model of compromise
// e.g. if we allowed the attacker to compromise specific epochs

type SafeHS (e:epoch) = is_SuccEpoch e /\ SafeHS_SI(epochSI e)
assume val safeHS: e:epoch -> b:bool { b = true <==> SafeHS e }

// Predicates specifying the security of TLS connections

// ``The handshake is complete''
type Open (e:epoch) = ( exists (r:role).
  (is_FullEpoch e /\ SentCCS r     (epochSI e) /\ SentCCS    (dualRole r) (epochSI e)) \/
  (is_AbbrEpoch e /\ SentCCSAbbr r (epochAI e) /\ SentCCSAbbr(dualRole r) (epochAI e)))

type OpenState (e:epoch) = ( exists (r:role).
  (((is_FullEpoch e /\ is_Some (prfMacAlg_of_ciphersuite_aux (epochSI e).cipher_suite) /\  SentCCS r     (epochSI e) /\ safeVD (epochSI e)) ==> SentCCS    (dualRole r) (epochSI e))) \/
  (((is_AbbrEpoch e /\ SentCCSAbbr r (epochAI e) /\ safeVD (epochSI e)) ==> SentCCSAbbr(dualRole r) (epochAI e))))

// The epoch parameters yield privacy & integrity
type Safe (e:epoch) =  (not (is_InitEpoch e)) ==> is_CipherSuite ((epochSI e).cipher_suite) /\ safeId (mk_id e) /\ OpenState e
assume val safe: e:epoch -> b:bool { b = true <==> Safe e }

// The epoch parameters yield integrity (not necessarily privacy)
type Auth (e:epoch) = (not (is_InitEpoch e)) ==> is_CipherSuite ((epochSI e).cipher_suite) /\ ((is_MtE (mk_id e).aeAlg) \/ (is_MACOnly (mk_id e).aeAlg /\ is_SSL_3p0 ((mk_id e).pv))) /\ authId (mk_id e) /\ OpenState e
assume val auth: e:epoch -> b:bool { b = true <==> Auth e }

//ask !e. Safe(e) => Auth(e)
//ask !e. not(Auth(e)) => not(Safe(e))

// so that TLS can exchange any traffic on the initial null connection
//ask !e. IsInitEpoch(e) => not Auth(e)

//ask !e. OpenState(e) => (AuthId(Id(e)) => Auth(e))
//ask !e. OpenState(e) => (SafeId(Id(e)) => Safe(e))
//ask !e. Auth(e) => OpenState(e)


(*
  KB The following is only true with Reneg indication, but is difficult to remove.
  KB It is an artifact of the way we treat epochs that we cannot just authenticate the current epoch, we need to always authenticate the full chain
  KB Maybe a refactor for v2 would be to separate our the current epoch and an optional predecessor
  KB Also this needs to account for SentCCSResume  
  
private theorem !r,r',e,e'. SentCCS(r,EpochSI(e)) /\
	                    SentCCS(r',EpochSI(e')) /\
  			    Id(e) = Id(e') => e = e'
theorem !e,e'. OpenState(e) /\ OpenState(e') /\ Id(e) = Id(e') => e = e'
 *)

(*
#if ideal
// These functions are used only for specifying ideal implementations
let safeHS (e:epoch) = failwith "spec only": bool
let safeHS_SI (e:SessionInfo) = failwith "spec only": bool
let safeCRE (e:SessionInfo) = failwith "spec only": bool
let safeVD (e:SessionInfo) = failwith "spec only": bool
let auth (e:epoch) = failwith "spec only": bool
let safe (e:epoch) = failwith "spec only" : bool //CF Define in terms of strength and honesty
let safeKDF (i:id) = failwith "spec only": bool
let authId (i:id) = failwith "spec only":bool
let safeId  (i:id) = failwith "spec only":bool
##endif
*)
