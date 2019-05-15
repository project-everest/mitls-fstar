(**
This file implements type representations and parsing functions
for the different values negotiated during the TLS
handshake. For instance protocol version, key exchange mechanism,
hash algorithm etc.

@summary Module for main constants
*)
module TLSConstants

/// 18-09-08 contents & triage (beware of scopes)
/// - crypto ==> EverCrypt
/// - datatypes ==> QD
///    7% for signatures
///   53% for ciphersuites!
///   10% for certificates
/// - prf details ==> KeySchedule
/// - parsed extension contents ==> Extensions
/// - split Config (defaults are defined much later); align to EverCrypt


//18-02-27 not a reasonable default?
//#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1"

open FStar.Seq
open FStar.UInt32
open FStar.Bytes
open FStar.Error
open TLSError

open Mem
open Parse
//include Parse

(* Relocate? *)
let rec fold_string (#a:Type)
                    (f: a -> string)
                    (accum:string)
                    (sep:string)
                    (al:list a) : Tot string (decreases al) =
    match al with
    | [] -> accum
    | a::al -> let accum = accum ^ sep ^ f a in
             fold_string f accum sep al

/// HIGH-LEVEL DECLARATIONS

(** Role of the connection endpoints *)
type role =
  | Client
  | Server
let dualRole = function
  | Client -> Server
  | Server -> Client

(** Polarity for reading and writing on a connection *)
type rw =
  | Reader
  | Writer

/// PROTOCOL VERSION

include Parsers.ProtocolVersion // for TLS_1p3, etc.

inline_for_extraction
type protocolVersion' = Parsers.ProtocolVersion.protocolVersion
inline_for_extraction
type protocolVersion = (p: protocolVersion' { not (Unknown_protocolVersion? p) } )

// aka TLS_1p3
let is_pv_13 = function
  | TLS_1p3 -> true
  | _       -> false

(** Serializing function for the protocol version *)
let versionBytes : protocolVersion' -> Tot (lbytes 2) =
  LowParseWrappers.wrap_serializer32_constant_length protocolVersion_serializer32 2 ()

inline_for_extraction
let parse_protocolVersion_error_msg : string =
  FStar.Error.perror __SOURCE_FILE__ __LINE__ ""

val parseVersion: pinverse_t versionBytes
let parseVersion x =
  LowParseWrappers.wrap_parser32_constant_length protocolVersion_serializer32 2 () protocolVersion_parser32 parse_protocolVersion_error_msg x

// 19-01-18 where is it defined?
let uint16_min (x y: UInt16.t) = if FStar.UInt16.(x <=^ y) then x else y 

(** Determine the oldest protocol versions for TLS *)
let minPV (a b: Parsers.ProtocolVersion.protocolVersion) =
  match a,b with
  | SSL_3p0, _  | _, SSL_3p0 -> SSL_3p0
  | TLS_1p0, _  | _, TLS_1p0 -> TLS_1p0
  | TLS_1p1, _  | _, TLS_1p1 -> TLS_1p1
  | TLS_1p2, _  | _, TLS_1p2 -> TLS_1p2
  | TLS_1p3, _  | _, TLS_1p3 -> TLS_1p3
  | Unknown_protocolVersion x, 
    Unknown_protocolVersion y -> Unknown_protocolVersion (uint16_min x y)

let leqPV a b = (a = minPV a b)
let geqPV a b = (b = minPV a b)

// TODO, remove alias
inline_for_extraction noextract let string_of_pv = string_of_protocolVersion 

/// CIPHER SUITES

include CipherSuite

let aeAlg_hash = function
  | MACOnly ha -> ha
  | MtE _ ha -> ha
  | AEAD _ ha -> ha

#set-options "--z3rlimit 100"
(** Determine if this algorithm provide padding support with TLS 1.2 *)
let lhae = function
  | MtE (Block _) _                         -> true
  | MACOnly _ | AEAD _ _ | MtE (Stream _) _ -> false

(** Sequence numbers for StreamAE/StatefulLHAE *)
let is_seqn (n:nat) = repr_bytes n <= 8
type seqn_t = n:nat { is_seqn n }

(** Predicates for Strong Authentication *)
// MtE: ``The AE algorithms are CPA and INT-CTXT''
// MtE: ``The MAC algorithm of id is INT-CMA.''

assume val strongAuthAlg: protocolVersion -> aeAlg -> Tot bool
//  | MtE _ m | MACOnly m   -> int_cma (macAlg_of_id i)
//  | AEAD e m -> strongAEADalg

val strongAEAlg: protocolVersion -> aeAlg -> Tot bool
let strongAEAlg _ _ = false
// let strongAEAlg pv ae = match ae with
//    | AEAD e m -> true
//    | MtE _ -> false

assume val strongAuthAE: pv:protocolVersion -> ae:aeAlg -> Lemma(strongAEAlg pv ae ==> strongAuthAlg pv ae)

// we leave these functions abstract for verification purposes
// we may need to be more negative on weak algorithms (so that we don't try to verify their use)
// and more precise/positive on algorithms we implement (so that we reflect lower assumptions)

(** Encryption key sizes *)
let encKeySize = function
  | Stream EverCrypt.RC4_128 -> 16
  | Block a                  -> UInt32.v (EverCrypt.block_cipher_keyLen a)

(** AEAD salt sizes *)
let aeadSaltSize =
  let open EverCrypt in function // TLS 1.3 IV salt.
  | AES128_GCM       -> 4
  | AES256_GCM       -> 4
  | CHACHA20_POLY1305 -> 12
  | _                 -> 4 //recheck

(** AEAD *)
let aeadRecordIVSize =
  let open EverCrypt in function // TLS 1.2 explicit IVs
  | AES128_GCM       -> 8
  | AES256_GCM       -> 8
  | CHACHA20_POLY1305 -> 0
  | _                 -> 8 //recheck


// -----------------------------------------------------------------------
// record-layer length constants [5.2.1]
// note that TLS 1.3 lowers a bit the upper bound of cipher lengths (Ok in principle)
// but still enables padding beyond plausible plaintext lengths.

(** Constants for API and protocol-level fragments are in [0..2^14] *)
let max_TLSPlaintext_fragment_length     = 16384
let max_TLSCompressed_fragment_length    = max_TLSPlaintext_fragment_length + 1024
let max_TLSCiphertext_fragment_length    = max_TLSPlaintext_fragment_length + 2048
let max_TLSCiphertext_fragment_length_13 = max_TLSPlaintext_fragment_length + 256

/// SIGNATURE SCHEME
 
// signatureScheme enum
include Parsers.SignatureScheme

let is_handshake13_signatureScheme = function
  | Ecdsa_secp256r1_sha256
  | Ecdsa_secp384r1_sha384
  | Ecdsa_secp521r1_sha512
  | Ed25519
  | Ed448
  | Rsa_pss_rsae_sha256
  | Rsa_pss_rsae_sha384
  | Rsa_pss_rsae_sha512
  | Rsa_pss_pss_sha256
  | Rsa_pss_pss_sha384
  | Rsa_pss_pss_sha512 -> true
  | _ -> false

let is_supported_signatureScheme = function
  | Rsa_pkcs1_sha1
  | Ecdsa_sha1
  | Rsa_pkcs1_sha256
  | Rsa_pkcs1_sha384
  | Rsa_pkcs1_sha512
  | Ecdsa_secp256r1_sha256
  | Ecdsa_secp384r1_sha384
  | Ecdsa_secp521r1_sha512
  | Rsa_pss_rsae_sha256
  | Rsa_pss_rsae_sha384
  | Rsa_pss_rsae_sha512
  | Rsa_pss_pss_sha256
  | Rsa_pss_pss_sha384
  | Rsa_pss_pss_sha512 -> true
  | _ -> false

type supported_signatureScheme = s:signatureScheme{is_supported_signatureScheme s}

let sigHashAlg_of_signatureScheme (s:supported_signatureScheme) : (sigAlg * hashAlg) =
  let open Hashing.Spec in
  match s with
  | Rsa_pkcs1_sha1 -> (RSASIG, Hash SHA1)
  | Ecdsa_sha1 -> (ECDSA, Hash SHA1)
  | Rsa_pkcs1_sha256 -> (RSASIG, Hash SHA2_256)
  | Rsa_pkcs1_sha384 -> (RSASIG, Hash SHA2_384)
  | Rsa_pkcs1_sha512 -> (RSASIG, Hash SHA2_512)
  | Ecdsa_secp256r1_sha256 -> (ECDSA, Hash SHA2_256)
  | Ecdsa_secp384r1_sha384 -> (ECDSA, Hash SHA2_384)
  | Ecdsa_secp521r1_sha512 -> (ECDSA, Hash SHA2_512)
  | Rsa_pss_rsae_sha256 -> (RSAPSS, Hash SHA2_256)
  | Rsa_pss_rsae_sha384 -> (RSAPSS, Hash SHA2_384)
  | Rsa_pss_rsae_sha512 -> (RSAPSS, Hash SHA2_512)
  | Rsa_pss_pss_sha256 -> (RSAPSS, Hash SHA2_256)
  | Rsa_pss_pss_sha384 -> (RSAPSS, Hash SHA2_384)
  | Rsa_pss_pss_sha512 -> (RSAPSS, Hash SHA2_512)

val signatureScheme_of_sigHashAlg: sigAlg -> hashAlg -> signatureScheme
let signatureScheme_of_sigHashAlg sa ha =
  let open Hashing.Spec in
  match sa, ha with
  | (RSASIG, Hash MD5) -> Rsa_pkcs1_md5
  | (RSASIG, Hash SHA1) -> Rsa_pkcs1_sha1
  | (RSASIG, Hash SHA2_256) -> Rsa_pkcs1_sha256
  | (RSASIG, Hash SHA2_384) -> Rsa_pkcs1_sha384
  | (RSASIG, Hash SHA2_512) -> Rsa_pkcs1_sha512
  | (ECDSA,  Hash MD5) -> Ecdsa_md5
  | (ECDSA,  Hash SHA1) -> Ecdsa_sha1
  | (ECDSA,  Hash SHA2_256) -> Ecdsa_secp256r1_sha256
  | (ECDSA,  Hash SHA2_384) -> Ecdsa_secp384r1_sha384
  | (ECDSA,  Hash SHA2_512) -> Ecdsa_secp521r1_sha512
  | (RSAPSS, Hash SHA2_256) -> Rsa_pss_rsae_sha256
  | (RSAPSS, Hash SHA2_384) -> Rsa_pss_rsae_sha384
  | (RSAPSS, Hash SHA2_512) -> Rsa_pss_rsae_sha512
  | _ -> Unknown_signatureScheme 0us

include Parsers.SignatureSchemeList

val signatureSchemeListBytes: algs:signatureSchemeList
  -> Tot (b:bytes{4 <= length b /\ length b < 65538})
let signatureSchemeListBytes algs =
  signatureSchemeList_serializer32 algs

val parseSignatureSchemeList: pinverse_t signatureSchemeListBytes
let parseSignatureSchemeList b =
  let emsg = perror __SOURCE_FILE__ __LINE__ "Failed to parse signature scheme list" in
  LowParseWrappers.wrap_parser32 signatureSchemeList_parser32 emsg b

/// COMPRESSION (LARGELY DEPRECATED IN TLS 1.3)

(** Compression definition *)

include Parsers.CompressionMethod // for NullCompression

inline_for_extraction
type compression = compressionMethod

(** Serializing function for compression algorithms *)
val compressionBytes: compression -> Tot (lbytes 1)
let compressionBytes =
  LowParseWrappers.wrap_serializer32_constant_length compressionMethod_serializer32 1 ()

// Not pinverse_t compressionBytes, because it never fails.

(** Parsing function for compression algorithm *)
val parseCompression: b:lbytes 1
  -> Tot (cm:compression{compressionBytes cm == b})
let parseCompression =
  LowParseWrappers.wrap_parser32_total_constant_length compressionMethod_serializer32 compressionMethod_parser32 1 ()

// We ignore compression methods we don't understand. This is a departure
// from usual parsing, where we fail on unknown values, but that's how TLS
// handles compression method lists.

type compressions = cms: list compression {List.length cms <= 254}

#reset-options "--using_facts_from '* -LowParse.Spec.Base'"

(** Parsing function for compression algorithm lists *)
val parseCompressions:
  b:bytes {length b <= 254} ->
  Tot (cms: compressions {List.length cms = length b}) (decreases (length b))
let rec parseCompressions b =
  if length b = 0
  then
    let cms: list compression = [] in
    assert_norm (List.length cms = 0); //libraries?
    cms
  else (
    let cmB,b' = split b 1ul in
    let cm = parseCompression cmB in
    let cms' = parseCompressions b' in
    let cms = cm :: cms' in
    assert_norm(List.length cms = 1 + List.length cms'); //library?
    cms )

//#set-options "--max_fuel 1 --initial_fuel 1 --max_ifuel 1 --initial_ifuel 1"

(** Serializing function for lists of compression algorithms *)
val compressionMethodsBytes:
  cms: compressions -> Tot (lbytes (List.Tot.length cms))
let rec compressionMethodsBytes cms =
  match cms with
  | c::cs -> compressionBytes c @| compressionMethodsBytes cs
  | []   -> empty_bytes

#reset-options

#reset-options "--admit_smt_queries true"

// Some of these could be hidden in Handshake.Secret

(** Definition for the PRF label type *)
type prflabel = bytes

(** Key schedule labels *)
let extract_label          = utf8_encode "master secret"
let extended_extract_label = utf8_encode "extended master secret"
let kdf_label              = utf8_encode "key expansion"

(** PRF definitions based on the protocol version *)
type prePrfAlg =
  | PRF_SSL3_nested         // MD5(SHA1(...)) for extraction and keygen
  | PRF_SSL3_concat         // MD5 @| SHA1    for VerifyData tags
  | PRF_TLS_1p01 of prflabel                       // MD5 xor SHA1
  | PRF_TLS_1p2 : prflabel -> macAlg -> prePrfAlg  // typically SHA2_256 but may depend on CS
  | PRF_TLS_1p3 // TBC

(** PRF associations *)
//BB.TODO: Documentation ?
type kefAlg_t = prePrfAlg
type kdfAlg_t = prePrfAlg
type vdAlg_t = protocolVersion * cipherSuite

// Only to be invoked with TLS 1.2 (hardcoded in previous versions)
// BB.TODO: Documentation ? Confirm that it is used with TLS 1.3 ! CF: no, for TLS 1.3 use tagLen a, e.g. 32 or 64
// let verifyDataLen_of_ciphersuite (cs:cipherSuite) = 12

// Only to be invoked with TLS 1.2 (hardcoded in previous versions)
val prfMacAlg_of_ciphersuite_aux: cipherSuite -> Tot (option macAlg)
let prfMacAlg_of_ciphersuite_aux =
  let open Hashing.Spec in function
  | CipherSuite  _ _  (MtE  _ _ )   -> Some SHA2_256
  | CipherSuite  _ _  (AEAD _ hAlg) -> Some hAlg
  | CipherSuite  _ _  (MACOnly _)   -> Some SHA2_256 //MK was (MACOnly hAlg) should it also be be (HMAC hAlg)?
  | _                               -> None

(** Determine if the tuple PV and CS is the correct association with PRF *)
let pvcs (pv:Parsers.ProtocolVersion.protocolVersion) (cs:cipherSuite) =
  match pv, cs with
  | TLS_1p3, CipherSuite13 _ _ -> true
  | TLS_1p3, CipherSuite _ _ _ -> false
  | pv, CipherSuite _ _ _ -> Some? (prfMacAlg_of_ciphersuite_aux cs)
  | _                 -> false

unfold type require_some (#a:Type) (#b:Type) ($f:(a -> Tot (option b))) =
  x:a{Some? (f x)} -> Tot b

let prfMacAlg_of_ciphersuite : require_some prfMacAlg_of_ciphersuite_aux =
  fun x -> Some?.v (prfMacAlg_of_ciphersuite_aux x)

// PRF and verifyData hash algorithms are potentially independent in TLS 1.2,
// so we use two distinct functions. However, all currently defined ciphersuites
// use the same hash algorithm, so the current implementation of the two functions
// is the same.

// Only to be invoked with TLS 1.2 (hardcoded in previous versions
// BB.TODO: Documentation ? Confirm that it is used with TLS 1.3 !
private
let verifyDataHashAlg_of_ciphersuite_aux =
  let open Hashing.Spec in function
  | CipherSuite _ _ (MtE  _ _) -> Some SHA2_256
  | CipherSuite _ _ (AEAD _ hAlg) -> Some hAlg
  | CipherSuite _ _ (MACOnly hAlg) -> Some SHA2_256
  | CipherSuite13 _ hAlg -> Some hAlg
  | _ -> None

// BB.TODO: Documentation ?
let verifyDataHashAlg_of_ciphersuite : require_some verifyDataHashAlg_of_ciphersuite_aux =
  fun x -> Some?.v (verifyDataHashAlg_of_ciphersuite_aux x)

let verifyDataHashAlg_of_ciphersuitename (n: cipherSuiteName) =
  match cipherSuite_of_name n with
  | None -> None
  | Some c -> verifyDataHashAlg_of_ciphersuite_aux c

(** Determine which session hash algorithm is to be used with the protocol version and ciphersuite *)
val sessionHashAlg: pv:protocolVersion -> cs:cipherSuite{pvcs pv cs} -> Tot hashAlg
let sessionHashAlg pv cs =
  let open Hashing.Spec in
  match pv with
  | TLS_1p3 -> let CipherSuite13 _ h = cs in Hash h
  | SSL_3p0 | TLS_1p0 | TLS_1p1 -> MD5SHA1 // FIXME: DSA uses only SHA1
  | TLS_1p2 -> Hash (verifyDataHashAlg_of_ciphersuite cs)

// TODO recheck this is the right hash for HKDF
// SZ: Right. The TLS 1.3 draft says "Where HMAC [RFC2104] uses
// the Hash algorithm for the handshake"

(** Determine the Authenticated Encryption algorithm associated with a ciphersuite *)
val get_aeAlg: cs:cipherSuite{ CipherSuite? cs \/ CipherSuite13? cs } -> Tot aeAlg
let get_aeAlg cs =
  match cs with
  | CipherSuite _ _ ae -> ae
  | CipherSuite13 a h -> AEAD a h

//(** Define the null authenticated encryption algorithm *)
// BB: Why does this default to MD5 ?
//let null_aeAlg = MACOnly MD5

(** Determine Encryption type to be used with a chosen PV and AE algorithm *)
val encAlg_of_aeAlg: (pv:protocolVersion) -> (a:aeAlg { MtE? a }) -> Tot (encAlg * ivMode)
let encAlg_of_aeAlg  pv ae =
  match pv,ae with
  | SSL_3p0, MtE (Block e) m -> (Block e),Stale
  | TLS_1p0, MtE (Block e) m -> (Block e),Stale
  | _, MtE e m -> e,Fresh

val macAlg_of_aeAlg: (pv:protocolVersion) -> (a:aeAlg { pv <> TLS_1p3 /\ ~(AEAD? a) }) -> Tot macAlg
let macAlg_of_aeAlg pv ae =
  match pv,ae with
  // 17-02-02 dropping support for weak ciphersuites. To be discussed!
  //  | SSL_3p0,MACOnly alg -> SSLKHash alg (* dropped pattern on the left to simplify refinements *)
  //  | SSL_3p0,MtE _ alg   -> SSLKHash alg
  //  | _      ,MACOnly alg -> SSLKHash alg
  | _      ,MACOnly alg
  | _      ,MtE _ alg   -> alg



/// 18-02-22 QD fodder
///
(** Certificate type definition *)
type certType =
  | RSA_sign
  | DSA_sign
  | RSA_fixed_dh
  | DSA_fixed_dh

(** Serializing function for the certificate type *)
val certTypeBytes: certType -> Tot (lbytes 1)
let certTypeBytes ct =
  match ct with
  | RSA_sign     -> abyte 1z
  | DSA_sign     -> abyte 2z
  | RSA_fixed_dh -> abyte 3z
  | DSA_fixed_dh -> abyte 4z

(** Parsing function for the certificate type *)
val parseCertType: pinverse_t certTypeBytes
let parseCertType b =
  match b.[0ul] with
  | 1z -> Correct RSA_sign
  | 2z -> Correct DSA_sign
  | 3z -> Correct RSA_fixed_dh
  | 4z -> Correct DSA_fixed_dh
  | _ -> fatal Decode_error (perror __SOURCE_FILE__ __LINE__ "")

(** Lemmas associated to serializing/parsing of certificate types *)
val inverse_certType: x:_ -> Lemma
  (requires True)
  (ensures lemma_inverse_g_f certTypeBytes parseCertType x)
  [SMTPat (parseCertType (certTypeBytes x))]
let inverse_certType x = admit()

val pinverse_certType: x:_ -> Lemma
  (requires True)
  (ensures (lemma_pinverse_f_g Bytes.equal certTypeBytes parseCertType x))
  [SMTPat (certTypeBytes (Correct?._0 (parseCertType x)))]
let pinverse_certType x = admit()

#set-options "--max_fuel 1 --initial_fuel 1"

(** Serializing function for lists of certificate types *)
val certificateTypeListBytes: ctl:list certType {List.length ctl <= 256} -> Tot (lbytes (List.Tot.length ctl))
let rec certificateTypeListBytes ctl =
  match ctl with
  | [] -> empty_bytes
  | h::t ->
    let ct = certTypeBytes h in
    ct @| certificateTypeListBytes t

(** Parsing function for lists of certificate types *)
val parseCertificateTypeList: data:bytes -> Tot (list certType) (decreases (length data))
let rec parseCertificateTypeList data =
  if length data = 0 then []
  else
    let (thisByte,data) = split data 1ul in
    match parseCertType thisByte with
    | Error z -> // we skip this one
      parseCertificateTypeList data
    | Correct ct ->
      let rem = parseCertificateTypeList data in
      ct :: rem

#set-options "--max_ifuel 4 --initial_ifuel 1 --max_fuel 4 --initial_fuel 1"

(** Determine the certificate signature algorithm from the ciphersuite *)
val defaultCertTypes: bool -> cipherSuite -> result certType
let defaultCertTypes sign cs =
  match sigAlg_of_ciphersuite cs with 
  | Error z -> Error z 
  | Correct alg -> 
    match alg with
    | RSASIG -> Correct(if sign then RSA_sign else RSA_fixed_dh)
    | DSA    -> Correct(if sign then DSA_sign else DSA_fixed_dh)
    | _      -> fatal Internal_error "[defaultCertTypes] invoked on an invalid ciphersuite"



#set-options "--max_ifuel 2 --initial_ifuel 2 --max_fuel 1 --initial_fuel 1"

(** Type definition of the Distinguished Name of a certificate *)
type dn = s:string{
  String.length s < 256 /\
  String.length s < pow2 30 /\ //18-02-23 improve precondition of [utf8_encode]?
  length(utf8_encode s) < 256}

(** Serializing function for a list of Distinguished Names of certificates *)
val distinguishedNameListBytes:
  names: list dn {List.length names <= 1024} -> // arbitrary bound
  b:bytes{length b <= op_Multiply 258 (List.Tot.length names)}
let rec distinguishedNameListBytes names =
  match names with
  | [] -> empty_bytes
  | h::t -> vlbytes2 (utf8_encode h) @| distinguishedNameListBytes t

(** Parsing function for a list of Distinguished Names of certificates *)
val parseDistinguishedNameList:
  data:bytes -> res:list dn -> Tot (result (list dn)) (decreases (length data))
//(* 18-02-24 I don't understand this error in pattern matching
let rec parseDistinguishedNameList data res =
  if length data = 0 then
    Correct res
  else
    if length data < 2 then
      fatal Decode_error (perror __SOURCE_FILE__ __LINE__ "")
    else
      match vlsplit 2 data with
      | Error z -> Error z
      | Correct (nameBytes,data) ->
        begin
          match iutf8_opt nameBytes with
          | None -> fatal Decode_error (perror __SOURCE_FILE__ __LINE__ "")
          | Some name ->
            if length (utf8_encode name) < 256 then
              let res = name :: res in
              parseDistinguishedNameList data res
            else fatal Decode_error (perror __SOURCE_FILE__ __LINE__ "")
        end

// TODO: move all the definitions below to a separate file / figure out whether
// they belong here ?
//
// TODO: all occurrences of [pinverse] from there on have been replaced by calls
// to [pinverse_t]; we should write corresponding inversion lemmas.









// Moved here because it's used in both Extensions and TLSInfo and Extensions
// and Extensions cannot depend on TLSInfo
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

type alpn = Parsers.ClientHelloExtension.clientHelloExtension_CHE_application_layer_protocol_negotiation


(*
noeq type miniconfig0: Type0 = {
    is_quic: bool; 
    cipher_suites: Parsers.CipherSuites.ciphersuites;
}

noeq type miniconfig: Type0 = { 
    is_quic: bool; 
    cipher_suites: ptr_len; // with len refinement  
}

let miniconfig_valid h0 (cfg0: erased spec) (cfg:from client) = 
  "cipher_suites contains exactly a valid Parsers.CipherSuites.ciphersuites"

create's precondition

  live h0 cipher_suites /\ 

scanning ensures valid ptr_len Parsers.CipherSuites.ciphersuites

*)  


open TLS.Callbacks 
noeq type config : Type0 = {
    // supported versions, implicitly preferring the latest versions
    //QD: we could instead pass a [Parsers.SupportedVersions.supportedversions]
    min_version: protocolVersion; 
    max_version: protocolVersion;

    // use QUIC labels for key derivations
    is_quic: bool; 

    // supported parameters, ordered by decreasing preference. 
    //QD: we could instead pass a [Parsers.CipherSuites.ciphersuites]
    cipher_suites: x:valid_cipher_suites{List.Tot.length x < 256};

    //19-01-22 carried by CH,EE,SH...; was CommonDH.supportedNamedGroups, overly restrictive. 
    named_groups: Parsers.ClientHelloExtension.clientHelloExtension_CHE_supported_groups;
    signature_algorithms: signatureSchemeList;

    (* Client side *)

    // honor hello retry requests from the server
    //19-05-04  not used? 
    hello_retry: bool;          

    // propose share from these groups (it should it be a subset of [named_groups]).
    //19-05-04 only makes sense with TLS 1.3; but must be non-empty? 
    //QD: use instead [Parsers.NamedGroupList]
    offer_shares: CommonDH.supportedNamedGroups;

    //QD: see new [TaggedUnknownExtension]. We will use a
    // manually-written coercion in [Extensions] but we still need to
    // prove that the two parsers coincide. 
    custom_extensions: custom_extensions;

    // propose these tickets 
    
    //QD: for now we decrypt them and pass resumeInfo as an extra
    // parameter. One low-level approach might be to decrypt them
    // in-place. Or we could decrypt before passing the config to the
    // new connection.
    use_tickets: list (psk_identifier * ticket_seal);

    (* Server side *)
    
    send_ticket: option bytes; // contents??
    check_client_version_in_pms_for_old_tls: bool;
    request_client_certificate: bool; // TODO: generalize to CertificateRequest contents: a list of CAs.

    (* Common *)
    
    non_blocking_read: bool;
    max_early_data: option UInt32.t;   // 0-RTT offer (client) and support (server), and data limit
    safe_renegotiation: bool;     // demands this extension when renegotiating
    extended_master_secret: bool; // turn on RFC 7627 extended master secret support
    enable_tickets: bool;         // Client: offer ticket support; server: emit and accept tickets

    (* Callbacks *)
    
    // Ticket callback, called when issuing or receiving a new ticket
    ticket_callback: ticket_cb;  
    // Callback to decide stateless retry and negotiate extra extensions
    nego_callback: nego_cb;
    // Certificate callbacks, called on all PKI-related operations
    cert_callbacks: cert_cb;

    // ALPN offers (for client) or preferences (for server)
    // we use the wire-format type, structurally shared between clients and servers. 
    //QD: pass [clientHelloExtension_CHE_application_layer_protocol_negotiation] instead. No need for an option. 
    alpn: option alpn;
    peer_name: option (n:Parsers.HostName.hostName{Bytes.length n <= 65535 - 5}); // The expected name to match against the peer certificate
    // 19-01-19 Hoisted parser refinements for, to be propagated. 
  }

type cVerifyData = b:bytes{length b <= 64} (* ClientFinished payload *)
type sVerifyData = b:bytes{length b <= 64} (* ServerFinished payload *)
