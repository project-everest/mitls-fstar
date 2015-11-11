(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module TLSInfo

open Bytes
open Date
open TLSConstants
open PMS
//open Seq

type rw =
    | Reader
    | Writer

type sessionID = bytes
type preRole =
    | Client
    | Server
type Role = preRole

// Client/Server randomness
type random = bytes
type crand = random
type srand = random
type csrands = bytes

type cVerifyData = bytes (* ClientFinished payload *)
type sVerifyData = bytes (* ServerFinished payload *)

type sessionHash = bytes

type serverName =
| SNI_DNS of bytes
| SNI_UNKNOWN of int * bytes 

// Defined here to not depend on TLSExtension

type negotiatedExtensions = {
    ne_extended_ms: bool;
    ne_extended_padding:bool;
    ne_renegotiation_info:  (cVerifyData * sVerifyData) option;
    ne_supported_curves:  (ECGroup.ec_curve list) option;
    ne_supported_point_formats:  (ECGroup.point_format list) option;
    ne_server_names:  (serverName list) option;
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

let noCsr:csrands = Nonce.random 64 //TODO should be Nonce.noCsr but this does not tc.

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
type pmsId = 
  | NoPmsId 
  | SomePmsId of PMS.pms
let mk_pmsId (pms:PMS.pms) = SomePmsId(pms)
let noPmsId = NoPmsId


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
    clientID: list<Cert.cert>;
    clientSigAlg: Sig.alg;
    serverID: list<Cert.cert>;
    serverSigAlg: Sig.alg;
    sessionID: sessionID;
    }

type msId = 
   | StandardMS of pmsId * csrands * kefAlg
   | ExtendedMS of pmsId * sessionHash * kefAlg

let noMsId = StandardMS (noPmsId, noCsr, PRF_SSL3_nested)    


let mk_csrands sinfo = 
    sinfo.init_crand @| sinfo.init_srand


let mk_kefAlg (si:SessionInfo) =
  match si.protocol_version with
  | SSL_3p0           -> PRF_SSL3_nested 
  | TLS_1p0 | TLS_1p1 -> let x = PRF_TLS_1p01(extract_label) in x
  | TLS_1p2           -> let ma = prfMacAlg_of_ciphersuite si.cipher_suite in
                         PRF_TLS_1p2(extract_label,ma)

let mk_kdfAlg (si:SessionInfo) =
  match si.protocol_version with
  | SSL_3p0           -> PRF_SSL3_nested 
  | TLS_1p0 | TLS_1p1 -> let x = PRF_TLS_1p01(kdf_label) in x
  | TLS_1p2           -> let ma = prfMacAlg_of_ciphersuite si.cipher_suite in
                         PRF_TLS_1p2(kdf_label,ma)

let mk_kefAlg_extended (si:SessionInfo) =
  match si.protocol_version with
  | SSL_3p0           -> PRF_SSL3_nested 
  | TLS_1p0 | TLS_1p1 -> let x = PRF_TLS_1p01(extended_extract_label) in x
  | TLS_1p2           -> let ma = prfMacAlg_of_ciphersuite si.cipher_suite in
                         PRF_TLS_1p2(extended_extract_label,ma) 

let mk_vdAlg (si:SessionInfo) = 
  si.protocol_version, si.cipher_suite


let mk_msid (si:SessionInfo) = 
  let ext = si.extensions in
  if ext.ne_extended_ms = false then
    let csr = mk_csrands si in
    let ca = mk_kefAlg si in
    StandardMS (si.pmsId, csr, ca) 
  else 
    let ca = mk_kefAlg_extended si in
    ExtendedMS (si.pmsId,si.session_hash,ca)

type abbrInfo = 
    {abbr_crand: crand;
     abbr_srand: srand;
     abbr_session_hash: sessionHash;
     abbr_vd:  (cVerifyData * sVerifyData) option;}

type preEpoch =
    | InitEpoch of Role
    | FullEpoch of SessionInfo * preEpoch
    | AbbrEpoch of abbrInfo * preEpoch * preEpoch

type epoch = preEpoch
type succEpoch = preEpoch
type openEpoch = preEpoch

let isInitEpoch e = 
    match e with
    | InitEpoch (_) -> true
    | FullEpoch (_,_) -> false
    | AbbrEpoch (_,_,_) -> false

let epochSI e =
    match e with
    | InitEpoch (d) -> Error.unexpected "[epochSI] invoked on initial epoch."
    | FullEpoch (si,pe) -> si
    | AbbrEpoch (ai,FullEpoch(si,pe1),pe2) -> si
    | AbbrEpoch (ai,pe1,pe2) -> Error.unexpected "[epochSI] given a AbbrEpoch that is not linked to a FullEpoch."

let epochAI e =
    match e with
    | InitEpoch (d) -> Error.unexpected "[epochAI] invoked on initial epoch."
    | FullEpoch (si,pe) -> Error.unexpected "[epochAI] invoked on full epoch."
    | AbbrEpoch (ai,pe1,pe2) -> ai


let epochSRand e =
    match e with
    | InitEpoch (d) -> Error.unexpected "[epochSRand] invoked on initial epoch."
    | FullEpoch (si,pe) -> si.init_srand
    | AbbrEpoch (ri,pe1,pe2) -> ri.abbr_srand

let epochCRand e =
    match e with
    | InitEpoch (d) -> Error.unexpected "[epochCRand] invoked on initial epoch."
    | FullEpoch (si,pe) -> si.init_crand
    | AbbrEpoch (ai,pe1,pe2) -> ai.abbr_crand

let epochCSRands e =
    epochCRand e @| epochSRand e

type preConnectionInfo = {
    role: Role; // cached, could be retrieved from id_out
    id_rand: random; // our random
    id_in: epoch;
    id_out: epoch}
type ConnectionInfo = preConnectionInfo

let connectionRole ci = ci.role

let initConnection role rand =
    let ctos = InitEpoch Client in
    let stoc = InitEpoch Server in
    match role with
    | Client -> {role = Client; id_rand = rand; id_in = stoc; id_out = ctos}
    | Server -> {role = Server; id_rand = rand; id_in = ctos; id_out = stoc}

let fullEpoch epoch si =
    FullEpoch (si, epoch )

let abbrEpoch epoch1 ai si epoch2 = 
    AbbrEpoch (ai,FullEpoch(si,epoch2),epoch1)

let predEpoch (e:epoch) = 
    match e with
    | FullEpoch(_, e') -> e'
    | AbbrEpoch(_,_,e') -> e'
    | InitEpoch(r) -> Error.unexpected "[predEpoch] invoked on initial epoch."

let rec epochWriter (e:epoch) =
    match e with
    | InitEpoch(r) -> r
    | FullEpoch(_,e) -> epochWriter e
    | AbbrEpoch(_,_,e) -> epochWriter e

// the tight index we use as an abstract parameter for StatefulAEAD et al
type id = { 
  msId   : msId;    
  kdfAlg : kdfAlg; 
  pv: ProtocolVersion; //Should be part of aeAlg 
  aeAlg  : aeAlg; 
  csrConn: csrands;
  ext: negotiatedExtensions;
  writer : Role }

let unAuthIdInv (i:id):epoch = 
#if verify
    failwith "only creates epochs for bad ids"
#else
    InitEpoch (i.writer)
#endif

let macAlg_of_id id = macAlg_of_aeAlg id.aeAlg
let encAlg_of_id id = encAlg_of_aeAlg id.aeAlg
let pv_of_id (id:id) =  id.pv //TODO MK fix
let kdfAlg_of_id (id:id) = id.kdfAlg

type event =
  | KeyCommit of    csrands * ProtocolVersion * aeAlg * negotiatedExtensions
  | KeyGenClient of csrands * ProtocolVersion * aeAlg * negotiatedExtensions
  | SentCCS of Role * SessionInfo
  | SentCCSAbbr of Role * abbrInfo 


let noId: id = { 
  msId = noMsId; 
  kdfAlg=PRF_SSL3_nested; 
  pv=SSL_3p0; 
  aeAlg= MACOnly(MA_SSLKHASH(NULL)); 
  csrConn = noCsr;
  ext = ne_default;
  writer=Client }

let mk_id e = 
  if isInitEpoch e 
  then noId 
  else
    let si     = epochSI e in
    let cs     = si.cipher_suite in
    let pv     = si.protocol_version in
    let msi    = mk_msid si in
    let kdfAlg = mk_kdfAlg si in
    let aeAlg  = mk_aeAlg cs pv in
    let csr    = epochCSRands e in
    let ext    = si.extensions in
    let wr     = epochWriter e in
    { msId = msi; 
      kdfAlg = kdfAlg; 
      pv = pv; 
      aeAlg = aeAlg; 
      csrConn = csr;
      ext = ext;
      writer = wr }

// Pretty printing
let sinfo_to_string (si:SessionInfo) =
#if true //TODO: This should be verify ; JK : "#if 1" not recognized by F#
    ""
#else
    let sb = new System.Text.StringBuilder() in
    let sb = sb.AppendLine("Session Information:") in
    let sb = sb.AppendLine(Printf.sprintf "Protocol Version: %A" si.protocol_version) in
    let sb = sb.AppendLine(Printf.sprintf "Ciphersuite: %A" (
                            match name_of_cipherSuite si.cipher_suite with
                            | Error.Error(_) -> failwith "Unknown ciphersuite"
                            | Error.Correct(c) -> c)) in
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
#endif

// Application configuration
type helloReqPolicy =
    | HRPIgnore
    | HRPFull
    | HRPResume

type config = {
    minVer: ProtocolVersion;
    maxVer: ProtocolVersion;
    ciphersuites: cipherSuites;
    compressions: list<Compression>;

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
    server_name: Cert.hint;
    client_name: Cert.hint;
            
    (* Sessions database *)
    sessionDBFileName: string;
    sessionDBExpiry: TimeSpan;

    (* DH groups database *)
    dhDBFileName: string;
    dhDefaultGroupFileName: string;
    dhPQMinLength: nat * nat;

    (* ECDH settings *)
    ecdhGroups: ECGroup.ec_curve list;
    }

let defaultConfig ={
    minVer = SSL_3p0;
    maxVer = TLS_1p2;
    ciphersuites = cipherSuites_of_nameList
                    [ TLS_RSA_WITH_AES_128_GCM_SHA256;
                      TLS_DHE_RSA_WITH_AES_128_GCM_SHA256;
                      TLS_DHE_DSS_WITH_AES_128_GCM_SHA256;
                      TLS_RSA_WITH_AES_128_CBC_SHA;
                      TLS_DHE_RSA_WITH_AES_128_CBC_SHA;
                      TLS_DHE_DSS_WITH_AES_128_CBC_SHA;
                      TLS_RSA_WITH_3DES_EDE_CBC_SHA;
                    ];
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
    dhPQMinLength = CoreDH.defaultPQMinLength;

    ecdhGroups = [ECGroup.ECC_P256; ECGroup.ECC_P384; ECGroup.ECC_P521];
    }

let max_TLSPlaintext_fragment_length = 16384 (*@ 2^14 *)
let max_TLSCompressed_fragment_length = max_TLSPlaintext_fragment_length + 1024
let max_TLSCipher_fragment_length = max_TLSCompressed_fragment_length + 1024
let fragmentLength = max_TLSPlaintext_fragment_length (*CF use e.g. 1 for testing *)

#if ideal

let honestPMS (pi:pmsId) : bool =
    match pi with
    | SomePmsId(PMS.RSAPMS(pk,cv,rsapms))   -> PMS.honestRSAPMS pk cv rsapms 
    | SomePmsId(PMS.DHPMS(p,g,gx,gy,dhpms)) -> PMS.honestDHPMS p g gx gy dhpms 
    | _ -> false

let strongKEF (ca:kefAlg) = failwith "spec only": bool

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
#endif
