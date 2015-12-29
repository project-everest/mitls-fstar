(* This file implements type representations and parsing functions
   for the different values negotiated during the TLS
   handshake. For instance protocol version, key exchange mechanism,
   hash algorithm etc. *)
module TLSConstants

(* SMT solver parameters *)
#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1"

open Platform.Bytes
open Platform.Error
open TLSError
open CoreCrypto
open FStar.SeqProperties

(* Type representations for TLS negotiated values *)
type ProtocolVersion =
    | SSL_3p0 // supported, with no security guarantees
    | TLS_1p0
    | TLS_1p1
    | TLS_1p2
    | TLS_1p3

(* Key exchange algorithms *)
type kexAlg =
    | Kex_RSA
    | Kex_DH
    | Kex_DHE
    | Kex_ECDHE

(* We retrieve cryptographic primitives from the CoreCrypto library *)
type blockCipher = block_cipher
type streamCipher = CoreCrypto.stream_cipher
type aeadAlg = CoreCrypto.aead_cipher

type ivMode =
    | Fresh
    | Stale

type encAlg =
    | Block of blockCipher
    | Stream of streamCipher

type hashAlg =
    | NULL
    | MD5SHA1
    | Hash of hash_alg (* Defined in the CoreCrypto library *)

type macAlg =
    | HMAC of hash_alg
    | SSLKHASH of hash_alg

type aeAlg =
    | MACOnly of hash_alg
    | MtE   : encAlg -> hash_alg -> aeAlg
    | AEAD  : aeadAlg -> hash_alg -> aeAlg

// MtE: ``The AE algorithms are CPA and INT-CTXT''
// MtE: ``The MAC algorithm of id is INT-CMA.''

assume val strongAuthAlg: ProtocolVersion -> aeAlg -> Tot bool
//  | MtE _ m | MACOnly m   -> int_cma (macAlg_of_id i)
//  | AEAD e m -> strongAEADalg

assume val strongAEAlg: ProtocolVersion -> aeAlg -> Tot bool
// let strongAEAlg pv ae = match ae with
//    | AEAD e m -> true
//    | MtE _ -> false

assume val strongAuthAE: pv:ProtocolVersion -> ae:aeAlg -> Lemma(strongAEAlg pv ae ==> strongAuthAlg pv ae)

//CF we leave these functions abstract for verification purposes
//CF we may need to be more negative on weak algorithms (so that we don't try to verify their use)
//CF and more precise/positive on algorithms we implement (so that we reflect lower assumptions)

type sigAlg = CoreCrypto.sig_alg

type sigHashAlg = sigAlg * hashAlg

(* Serializing function for signature algorithms *)
val sigAlgBytes: sigAlg -> Tot (lbytes 1)
let sigAlgBytes sa =
    match sa with
    | CoreCrypto.RSASIG -> abyte 1uy
    | CoreCrypto.DSA    -> abyte 2uy
    | CoreCrypto.ECDSA  -> abyte 3uy
    | CoreCrypto.RSAPSS -> abyte 4uy

type pinverse_t (#a:Type) (#b:Type) (=f:(a -> Tot b)) = 
    (y:b -> Tot (Result a))
 
(* Parsing function associated to sigAlgBytes *)
val parseSigAlg: pinverse_t sigAlgBytes
let parseSigAlg b =
    match cbyte b with
    | 1uy -> Correct CoreCrypto.RSASIG
    | 2uy -> Correct CoreCrypto.DSA
    | 3uy -> Correct CoreCrypto.ECDSA
    | 4uy -> Correct CoreCrypto.RSAPSS
    | _ -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

type lemma_inverse_g_f (#a:Type) (#b:Type) (=f:(a -> Tot b)) (=g:(b -> Tot (Result a))) (x:a) = 
  g (f x) = Correct x

type lemma_pinverse_f_g (#a:Type) (#b:Type) (r:b -> b -> Type) (=f:(a -> Tot b)) (=g:(b -> Tot (Result a))) (y:b) =
  is_Correct (g y) ==> r (f (Correct._0 (g y))) y
 
val inverse_sigAlg: x:_ -> Lemma
  (requires (True)) 
  (ensures lemma_inverse_g_f sigAlgBytes parseSigAlg x)
  [SMTPat (parseSigAlg (sigAlgBytes x))]
let inverse_sigAlg x = ()

val pinverse_sigAlg: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.Eq sigAlgBytes parseSigAlg x))
  [SMTPat (sigAlgBytes (Correct._0 (parseSigAlg x)))]
let pinverse_sigAlg x = ()

type hashAlg' = h:hashAlg{h <> NULL && h <> MD5SHA1 && h <> Hash SHA512}
 
val hashAlgBytes : hashAlg' -> Tot (lbytes 1)
let hashAlgBytes ha =
    match ha with
    | Hash MD5     -> abyte 1uy
    | Hash SHA1     -> abyte 2uy
    | Hash SHA224  -> abyte 3uy
    | Hash SHA256  -> abyte 4uy
    | Hash SHA384  -> abyte 5uy

val parseHashAlg: pinverse_t hashAlgBytes
let parseHashAlg b =
    match cbyte b with
    | (1uy) -> Correct (Hash MD5)
    | (2uy) -> Correct (Hash SHA1)
    | (3uy) -> Correct (Hash SHA224)
    | (4uy) -> Correct (Hash SHA256)
    | (5uy) -> Correct (Hash SHA384)
    | _ -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val inverse_hashAlg: x:_ -> Lemma
  (requires (True)) 
  (ensures lemma_inverse_g_f hashAlgBytes parseHashAlg x)
  [SMTPat (parseHashAlg (hashAlgBytes x))]
let inverse_hashAlg x = ()

val pinverse_hashAlg: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.Eq hashAlgBytes parseHashAlg x))
  [SMTPat (hashAlgBytes (Correct._0 (parseHashAlg x)))]
let pinverse_hashAlg x = ()

let encKeySize = function
  | Stream RC4_128      -> 16
  | Block TDES_EDE_CBC  -> 24
  | Block AES_128_CBC   -> 16
  | Block AES_256_CBC   -> 32
  | Block TDES_EDE_CBC  -> 24
  | Block AES_128_CBC   -> 16
  | Block AES_256_CBC   -> 32

// TODO: renamed from aeadIVSize to avoid clash with CoreCrypto
let aeadSaltSize = function
  | AES_128_GCM -> 4
  | AES_256_GCM -> 4

let aeadRecordIVSize = function
  | AES_128_GCM -> 8
  | AES_256_GCM -> 8

val hashSize: h:hashAlg{h<>NULL} -> Tot nat
let hashSize = function
  | Hash h  -> CoreCrypto.hashSize h
  | MD5SHA1 -> 16 + 20

let macKeySize = function
  | HMAC alg
  | SSLKHASH alg -> hashSize (Hash alg)

let macSize = function
  | HMAC alg
  | SSLKHASH alg -> hashSize (Hash alg)

type SCSVsuite =
    | TLS_EMPTY_RENEGOTIATION_INFO_SCSV

type cipherSuite =
    | NullCipherSuite    : cipherSuite
    | CipherSuite        : kexAlg -> option sig_alg -> aeAlg -> cipherSuite
    | SCSV               : SCSVsuite -> cipherSuite

type cipherSuites = list cipherSuite

type PreCompression =
    | NullCompression
type Compression = PreCompression

val parseCompression: b:bytes{Seq.length b > 0} -> Result Compression
let parseCompression b =
    match cbyte b with
    | 0uy -> Correct NullCompression
    | _   -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

// We ignore compression methods we don't understand. This is a departure
// from usual parsing, where we fail on unknown values, but that's how TLS
// handles compression method lists.
val parseCompressions: bytes -> list Compression
let rec parseCompressions b =
    let l = length b in
    if l > 0
    then
        let (cmB,b) = Platform.Bytes.split b 1 in
        match parseCompression cmB with
        | Error(z) -> // We skip this one
            parseCompressions b
        | Correct(cm) -> cm :: parseCompressions b
    else []

val compressionBytes: Compression -> Tot (lbytes 1)
let compressionBytes (comp:Compression) =
    match comp with
    | NullCompression -> abyte 0uy

#set-options "--max_ifuel 4 --initial_ifuel 2 --max_fuel 2 --initial_fuel 2"

val compressionMethodsBytes : cms:list Compression -> Tot (lbytes (List.length cms))
let rec compressionMethodsBytes cms =
   match cms with
   | c::cs -> compressionBytes c @| compressionMethodsBytes cs
   | []    -> empty_bytes

#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1"

val versionBytes : ProtocolVersion -> Tot (lbytes 2)
let versionBytes pv =
    match pv with
    | SSL_3p0 -> abyte2 ( 3uy, 0uy)
    | TLS_1p0 -> abyte2 ( 3uy, 1uy)
    | TLS_1p1 -> abyte2 ( 3uy, 2uy )
    | TLS_1p2 -> abyte2 ( 3uy, 3uy )
    | TLS_1p3 -> abyte2 ( 3uy, 4uy )

val parseVersion: pinverse_t versionBytes
let parseVersion v =
    match cbyte2 v with
    | ( 3uy, 0uy ) -> Correct(SSL_3p0)
    | ( 3uy, 1uy ) -> Correct(TLS_1p0)
    | ( 3uy, 2uy ) -> Correct(TLS_1p1)
    | ( 3uy, 3uy ) -> Correct(TLS_1p2)
    | ( 3uy, 4uy ) -> Correct(TLS_1p3)
    | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val inverse_version: x:_ -> Lemma
  (requires (True)) 
  (ensures lemma_inverse_g_f versionBytes parseVersion x)
  [SMTPat (parseVersion (versionBytes x))]
let inverse_version x = ()

val pinverse_version: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.Eq versionBytes parseVersion x))
  [SMTPat (versionBytes (Correct._0 (parseVersion x)))]
let pinverse_version x = ()

let minPV (a:ProtocolVersion) (b:ProtocolVersion) =
  match (a,b) with
  | SSL_3p0, _  | _, SSL_3p0 -> SSL_3p0
  | TLS_1p0, _  | _, TLS_1p0 -> TLS_1p0
  | TLS_1p1, _  | _, TLS_1p1 -> TLS_1p1
  | TLS_1p2, _  | _, TLS_1p2 -> TLS_1p2
  | TLS_1p3, _  | _, TLS_1p3 -> TLS_1p3

let somePV (a:ProtocolVersion) = Some a
let geqPV a b = (b = minPV a b)


let nullCipherSuite = NullCipherSuite

let isNullCipherSuite cs = (cs = NullCipherSuite)

val cipherSuiteBytesOpt: cipherSuite -> Tot (option (lbytes 2))
let cipherSuiteBytesOpt cs =
  let abyte2 b : option (lbytes 2) = Some (abyte2 b) in
    match cs with
    | NullCipherSuite                                 -> abyte2 ( 0x00uy, 0x00uy )

    | CipherSuite Kex_RSA None (MACOnly MD5)                       -> abyte2 ( 0x00uy, 0x01uy )
    | CipherSuite Kex_RSA None (MACOnly SHA1)                      -> abyte2 ( 0x00uy, 0x02uy )
    | CipherSuite Kex_RSA None (MACOnly SHA256)                    -> abyte2 ( 0x00uy, 0x3Buy )
    | CipherSuite Kex_RSA None(MtE (Stream RC4_128) MD5)           -> abyte2 ( 0x00uy, 0x04uy )
    | CipherSuite Kex_RSA None(MtE (Stream RC4_128) SHA1)          -> abyte2 ( 0x00uy, 0x05uy )

    | CipherSuite Kex_RSA None(MtE (Block TDES_EDE_CBC) SHA1)      -> abyte2 ( 0x00uy, 0x0Auy )
    | CipherSuite Kex_RSA None(MtE (Block AES_128_CBC) SHA1)       -> abyte2 ( 0x00uy, 0x2Fuy )
    | CipherSuite Kex_RSA None(MtE (Block AES_256_CBC) SHA1)       -> abyte2 ( 0x00uy, 0x35uy )
    | CipherSuite Kex_RSA None(MtE (Block AES_128_CBC) SHA256)     -> abyte2 ( 0x00uy, 0x3Cuy )
    | CipherSuite Kex_RSA None(MtE (Block AES_256_CBC) SHA256)     -> abyte2 ( 0x00uy, 0x3Duy )

    (**************************************************************************)
    | CipherSuite Kex_DH (Some DSA)     (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0x00uy, 0x0Duy )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0x00uy, 0x10uy )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0x00uy, 0x13uy )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0x00uy, 0x16uy )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0x00uy, 0x30uy )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0x00uy, 0x31uy )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0x00uy, 0x32uy )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0x00uy, 0x33uy )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0x00uy, 0x36uy )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0x00uy, 0x37uy )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0x00uy, 0x38uy )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0x00uy, 0x39uy )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0x00uy, 0x3Euy )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0x00uy, 0x3Fuy )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0x00uy, 0x40uy )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0x00uy, 0x67uy )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_256_CBC) SHA256)  -> abyte2 ( 0x00uy, 0x68uy )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_256_CBC) SHA256)  -> abyte2 ( 0x00uy, 0x69uy )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_256_CBC) SHA256)  -> abyte2 ( 0x00uy, 0x6Auy )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA256)  -> abyte2 ( 0x00uy, 0x6Buy )

    (**************************************************************************)
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1)       -> abyte2 ( 0xc0uy, 0x11uy )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0xc0uy, 0x12uy )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0xc0uy, 0x13uy )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0xc0uy, 0x14uy )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0xc0uy, 0x27uy )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA384)  -> abyte2 ( 0xc0uy, 0x28uy )

    | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_128_GCM SHA256) -> abyte2 ( 0xc0uy, 0x2fuy )
    | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_256_GCM SHA384) -> abyte2 ( 0xc0uy, 0x30uy )

    (**************************************************************************)
    | CipherSuite Kex_DHE None   (MtE (Stream RC4_128) MD5)         -> abyte2 ( 0x00uy, 0x18uy )
    | CipherSuite Kex_DHE None   (MtE (Block TDES_EDE_CBC) SHA1)    -> abyte2 ( 0x00uy, 0x1Buy )
    | CipherSuite Kex_DHE None   (MtE (Block AES_128_CBC) SHA1)     -> abyte2 ( 0x00uy, 0x34uy )
    | CipherSuite Kex_DHE None   (MtE (Block AES_256_CBC) SHA1)     -> abyte2 ( 0x00uy, 0x3Auy )
    | CipherSuite Kex_DHE None   (MtE (Block AES_128_CBC) SHA256)   -> abyte2 ( 0x00uy, 0x6Cuy )
    | CipherSuite Kex_DHE None   (MtE (Block AES_256_CBC) SHA256)   -> abyte2 ( 0x00uy, 0x6Duy )

    (**************************************************************************)
    | CipherSuite Kex_RSA None     (AEAD AES_128_GCM SHA256) -> abyte2( 0x00uy, 0x9Cuy )
    | CipherSuite Kex_RSA None     (AEAD AES_256_GCM SHA384) -> abyte2( 0x00uy, 0x9Duy )

    | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_128_GCM SHA256) -> abyte2( 0x00uy, 0x9Euy )
    | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_256_GCM SHA384) -> abyte2( 0x00uy, 0x9Fuy )
    | CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_128_GCM SHA256) -> abyte2( 0x00uy, 0xA0uy )
    | CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_256_GCM SHA384) -> abyte2( 0x00uy, 0xA1uy )

    | CipherSuite Kex_DHE (Some DSA) (AEAD AES_128_GCM SHA256) -> abyte2( 0x00uy, 0xA2uy )
    | CipherSuite Kex_DHE (Some DSA) (AEAD AES_256_GCM SHA384) -> abyte2( 0x00uy, 0xA3uy )
    | CipherSuite Kex_DH (Some DSA)  (AEAD AES_128_GCM SHA256) -> abyte2( 0x00uy, 0xA4uy )
    | CipherSuite Kex_DH (Some DSA)  (AEAD AES_256_GCM SHA384) -> abyte2( 0x00uy, 0xA5uy )

    | CipherSuite Kex_DHE None (AEAD AES_128_GCM SHA256) -> abyte2( 0x00uy, 0xA6uy )
    | CipherSuite Kex_DHE None (AEAD AES_256_GCM SHA384) -> abyte2( 0x00uy, 0xA7uy )

    | SCSV (TLS_EMPTY_RENEGOTIATION_INFO_SCSV)         -> abyte2 ( 0x00uy, 0xFFuy )

    | _ -> None

let knownCipherSuite (c:cipherSuite) = is_Some (cipherSuiteBytesOpt c)
type known_cipher_suite = c:cipherSuite{knownCipherSuite c}
type known_cipher_suites = list known_cipher_suite

val cipherSuiteBytes: known_cipher_suite -> Tot (lbytes 2)
let cipherSuiteBytes c = Some.v (cipherSuiteBytesOpt c)

val parseCipherSuiteAux : lbytes 2 -> Tot (Result cipherSuite)
let parseCipherSuiteAux b =
    match cbyte2 b with
    | ( 0x00uy, 0x00uy ) -> Correct(NullCipherSuite)

    | ( 0x00uy, 0x01uy ) -> Correct(CipherSuite Kex_RSA None (MACOnly MD5))
    | ( 0x00uy, 0x02uy ) -> Correct(CipherSuite Kex_RSA None (MACOnly SHA1))
    | ( 0x00uy, 0x3Buy ) -> Correct(CipherSuite Kex_RSA None (MACOnly SHA256))
    | ( 0x00uy, 0x04uy ) -> Correct(CipherSuite Kex_RSA None (MtE (Stream RC4_128) MD5))
    | ( 0x00uy, 0x05uy ) -> Correct(CipherSuite Kex_RSA None (MtE (Stream RC4_128) SHA1))

    | ( 0x00uy, 0x0Auy ) -> Correct(CipherSuite Kex_RSA None (MtE (Block TDES_EDE_CBC) SHA1))
    | ( 0x00uy, 0x2Fuy ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES_128_CBC) SHA1))
    | ( 0x00uy, 0x35uy ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES_256_CBC) SHA1))
    | ( 0x00uy, 0x3Cuy ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES_128_CBC) SHA256))
    | ( 0x00uy, 0x3Duy ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES_256_CBC) SHA256))

    (**************************************************************************)
    | ( 0x00uy, 0x0Duy ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block TDES_EDE_CBC) SHA1))
    | ( 0x00uy, 0x10uy ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1))
    | ( 0x00uy, 0x13uy ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block TDES_EDE_CBC) SHA1))
    | ( 0x00uy, 0x16uy ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1))

    | ( 0x00uy, 0x30uy ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES_128_CBC) SHA1))
    | ( 0x00uy, 0x31uy ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES_128_CBC) SHA1))
    | ( 0x00uy, 0x32uy ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_128_CBC) SHA1))
    | ( 0x00uy, 0x33uy ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1))

    | ( 0x00uy, 0x36uy ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES_256_CBC) SHA1))
    | ( 0x00uy, 0x37uy ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES_256_CBC) SHA1))
    | ( 0x00uy, 0x38uy ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_256_CBC) SHA1))
    | ( 0x00uy, 0x39uy ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1))

    | ( 0x00uy, 0x3Euy ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES_128_CBC) SHA256))
    | ( 0x00uy, 0x3Fuy ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES_128_CBC) SHA256))
    | ( 0x00uy, 0x40uy ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_128_CBC) SHA256))
    | ( 0x00uy, 0x67uy ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256))

    | ( 0x00uy, 0x68uy ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES_256_CBC) SHA256))
    | ( 0x00uy, 0x69uy ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES_256_CBC) SHA256))
    | ( 0x00uy, 0x6Auy ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_256_CBC) SHA256))
    | ( 0x00uy, 0x6Buy ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA256))

    (**************************************************************************)
    | ( 0xc0uy, 0x11uy ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1))
    | ( 0xc0uy, 0x12uy ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1))
    | ( 0xc0uy, 0x13uy ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1))
    | ( 0xc0uy, 0x14uy ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1))
    | ( 0xc0uy, 0x27uy ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256))
    | ( 0xc0uy, 0x28uy ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA384))

    | ( 0xc0uy, 0x2fuy ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_128_GCM SHA256))
    | ( 0xc0uy, 0x30uy ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_256_GCM SHA384))

    (**************************************************************************)
    | ( 0x00uy, 0x18uy ) -> Correct(CipherSuite Kex_DHE None (MtE (Stream RC4_128) MD5))
    | ( 0x00uy, 0x1Buy ) -> Correct(CipherSuite Kex_DHE None (MtE (Block TDES_EDE_CBC) SHA1))
    | ( 0x00uy, 0x34uy ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES_128_CBC) SHA1))
    | ( 0x00uy, 0x3Auy ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES_256_CBC) SHA1))
    | ( 0x00uy, 0x6Cuy ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES_128_CBC) SHA256))
    | ( 0x00uy, 0x6Duy ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES_256_CBC) SHA256))

    (**************************************************************************)
    | ( 0x00uy, 0x9Cuy ) -> Correct(CipherSuite Kex_RSA None     (AEAD AES_128_GCM SHA256))
    | ( 0x00uy, 0x9Duy ) -> Correct(CipherSuite Kex_RSA None     (AEAD AES_256_GCM SHA384))

    | ( 0x00uy, 0x9Euy ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_128_GCM SHA256))
    | ( 0x00uy, 0x9Fuy ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_256_GCM SHA384))
    | ( 0x00uy, 0xA0uy ) -> Correct(CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_128_GCM SHA256))
    | ( 0x00uy, 0xA1uy ) -> Correct(CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_256_GCM SHA384))

    | ( 0x00uy, 0xA2uy ) -> Correct(CipherSuite Kex_DHE (Some DSA) (AEAD AES_128_GCM SHA256))
    | ( 0x00uy, 0xA3uy ) -> Correct(CipherSuite Kex_DHE (Some DSA) (AEAD AES_256_GCM SHA384))
    | ( 0x00uy, 0xA4uy ) -> Correct(CipherSuite Kex_DH (Some DSA)  (AEAD AES_128_GCM SHA256))
    | ( 0x00uy, 0xA5uy ) -> Correct(CipherSuite Kex_DH (Some DSA)  (AEAD AES_256_GCM SHA384))

    | ( 0x00uy, 0xA6uy ) -> Correct(CipherSuite Kex_DHE None (AEAD AES_128_GCM SHA256))
    | ( 0x00uy, 0xA7uy ) -> Correct(CipherSuite Kex_DHE None (AEAD AES_256_GCM SHA384))

    | ( 0x00uy, 0xFFuy ) -> Correct(SCSV (TLS_EMPTY_RENEGOTIATION_INFO_SCSV))

    | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val parseCipherSuite : pinverse_t cipherSuiteBytes
let parseCipherSuite b =
  match parseCipherSuiteAux b with
  | Correct c -> Correct c
  | Error z -> Error z


#set-options "--max_ifuel 6 --initial_ifuel 6 --max_fuel 1 --initial_fuel 1"
val inverse_cipherSuite: x:cipherSuite -> Lemma
   (requires (True)) 
   (ensures (let y = cipherSuiteBytesOpt x in
		(is_Some y ==> parseCipherSuiteAux (Some.v y) = Correct x)))
   [SMTPat (parseCipherSuiteAux (Some.v (cipherSuiteBytesOpt x)))]
let inverse_cipherSuite x = ()

val pinverse_cipherSuite : x:lbytes 2 -> Lemma
  (requires (True))
  (ensures (let y = parseCipherSuiteAux x in
	    (is_Correct y ==> (is_Some (cipherSuiteBytesOpt (Correct._0 y)) 
			       /\ Seq.Eq x (Some.v (cipherSuiteBytesOpt (Correct._0 y)))))))
  [SMTPat (cipherSuiteBytesOpt (Correct._0 (parseCipherSuiteAux x)))]
let pinverse_cipherSuite x = ()

#reset-options
#set-options "--max_ifuel 1 --initial_ifuel 1 --max_fuel 1 --initial_fuel 1"


(* Called by the server handshake; *)
(* ciphersuites that we do not understand are parsed, *)
(* but not added to the list, and thus will be ignored by the server *)
opaque val parseCipherSuites: b:bytes -> Tot (Result known_cipher_suites) (decreases (length b))
let rec parseCipherSuites b : Result known_cipher_suites =
     if length b > 1 then
       let (b0,b1) = Platform.Bytes.split b 2 in
       match parseCipherSuites b1 with
         | Correct(css) ->
           (match parseCipherSuite b0 with
             | Error(z) ->    Correct css      (* ignore this cs *)
             | Correct(cs) -> Correct(cs::css))
         | Error(z) -> Error(z)
     else if length b = 0 then Correct []
     else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val cipherSuitesBytes: css:known_cipher_suites -> Tot (lbytes (2 * List.length css))
let rec cipherSuitesBytes css =
   match css with
     | [] -> empty_bytes
     | cs::css -> (cipherSuiteBytes cs) @| (cipherSuitesBytes css)

let isAnonCipherSuite cs =
    match cs with
    | CipherSuite Kex_DHE None _    -> true
    | _ -> false

let isDHECipherSuite cs =
    match cs with
    | CipherSuite Kex_DHE (Some DSA) _      -> true
    | CipherSuite Kex_DHE (Some RSASIG) _   -> true
    | CipherSuite Kex_ECDHE (Some ECDSA) _  -> true
    | CipherSuite Kex_ECDHE (Some RSASIG) _ -> true
    | _ -> false

let isECDHECipherSuite cs =
    match cs with
    | CipherSuite Kex_ECDHE (Some ECDSA) _  -> true
    | CipherSuite Kex_ECDHE (Some RSASIG) _ -> true
    | _ -> false

let isDHCipherSuite cs =
    match cs with
    | CipherSuite Kex_DH (Some DSA) _    -> true
    | CipherSuite Kex_DH (Some RSASIG) _ -> true
    | _ -> false

let isRSACipherSuite cs =
    match cs with
    | CipherSuite Kex_RSA None _ -> true
    | _ -> false

let isOnlyMACCipherSuite cs =
    match cs with
    | CipherSuite _ _ (MACOnly _) -> true
    | _ -> false

let sigAlg_of_ciphersuite cs =
    match cs with
    | CipherSuite Kex_RSA None _
    | CipherSuite Kex_ECDHE (Some RSASIG) _
    | CipherSuite Kex_DHE (Some RSASIG) _
    | CipherSuite Kex_DH (Some RSASIG) _   -> RSASIG
    | CipherSuite Kex_DHE (Some DSA) _
    | CipherSuite Kex_DH (Some DSA) _      -> DSA
    | CipherSuite Kex_ECDHE (Some ECDSA) _ -> ECDSA
    | _ -> unexpected "[sigAlg_of_ciphersuite] invoked on a wrong ciphersuite"

type prflabel = bytes
let extract_label = utf8 "master secret"
let extended_extract_label = utf8 "extended master secret"
let kdf_label     = utf8 "key expansion"

type prePrfAlg =
  | PRF_SSL3_nested         // MD5(SHA1(...)) for extraction and keygen
  | PRF_SSL3_concat         // MD5 @| SHA1    for VerifyData tags
  | PRF_TLS_1p01 of prflabel                       // MD5 xor SHA1
  | PRF_TLS_1p2 : prflabel -> macAlg -> prePrfAlg  // typically SHA256 but may depend on CS

type KefAlg = prePrfAlg
type KdfAlg = prePrfAlg
type VdAlg = ProtocolVersion * cipherSuite

(* Only to be invoked with TLS 1.2 (hardcoded in previous versions *)
let verifyDataLen_of_ciphersuite (cs:cipherSuite) = 12

(* Only to be invoked with TLS 1.2 (hardcoded in previous versions *)
val prfMacAlg_of_ciphersuite_aux: cipherSuite -> Tot (option macAlg)
let prfMacAlg_of_ciphersuite_aux = function
    | CipherSuite  _ _  (MtE  _ _ )   -> Some (HMAC SHA256)
    | CipherSuite  _ _  (AEAD _ hAlg) -> Some (HMAC hAlg)
    | CipherSuite  _ _  (MACOnly _)  -> Some (HMAC SHA256) //MK was (MACOnly hAlg) should it also be be (HMAC hAlg)?
    | _                                -> None

let pvcs (pv:ProtocolVersion) (cs:cipherSuite) =
  match pv with
  | TLS_1p2 | TLS_1p3 -> is_Some (prfMacAlg_of_ciphersuite_aux cs)
  | _                 -> true

logic type require_some : #a:Type -> #b:Type -> =f:(a -> Tot (option b)) -> Type =
   fun (a:Type) (b:Type) (f: (a -> Tot (option b))) -> (x:a{is_Some (f x)} -> Tot b)

let prfMacAlg_of_ciphersuite : require_some prfMacAlg_of_ciphersuite_aux =
  fun x -> Some.v (prfMacAlg_of_ciphersuite_aux x)

(* PRF and verifyData hash algorithms are potentially independent in TLS 1.2, *)
(* so we use two distinct functions. However, all currently defined ciphersuites *)
(* use the same hash algorithm, so the current implementation of the two functions *)
(* is the same. *)
(* Only to be invoked with TLS 1.2 (hardcoded in previous versions *)
let verifyDataHashAlg_of_ciphersuite_aux = function
  | CipherSuite _ _ (MtE  _ _)    -> Some SHA256
  | CipherSuite _ _ (AEAD _ hAlg) -> Some hAlg
  | CipherSuite _ _ (MACOnly hAlg) -> Some SHA256
  | _                               -> None
let verifyDataHashAlg_of_ciphersuite : require_some verifyDataHashAlg_of_ciphersuite_aux =
  fun x -> Some.v (verifyDataHashAlg_of_ciphersuite_aux x)

val sessionHashAlg: pv:ProtocolVersion -> cs:cipherSuite{pvcs pv cs} -> Tot hashAlg
let sessionHashAlg pv cs =
    match pv with
    | SSL_3p0 | TLS_1p0 | TLS_1p1 -> MD5SHA1
    | TLS_1p2 | TLS_1p3           -> Hash (verifyDataHashAlg_of_ciphersuite cs)
// TODO recheck this is the right hash for HKDF

val get_aeAlg: cs:cipherSuite{ is_CipherSuite cs } -> Tot aeAlg
let get_aeAlg cs =
    match cs with
    | CipherSuite _ _ ae -> ae

let null_aeAlg  = MACOnly MD5

val encAlg_of_aeAlg: (pv:ProtocolVersion) -> (a:aeAlg { is_MtE a }) -> Tot (encAlg * ivMode)
let encAlg_of_aeAlg  pv ae =
    match pv,ae with
    | SSL_3p0, MtE (Block e) m -> (Block e),Stale
    | TLS_1p0, MtE (Block e) m -> (Block e),Stale
    | _, MtE e m -> e,Fresh

val macAlg_of_aeAlg: (pv:ProtocolVersion) -> (a:aeAlg { ~(is_AEAD a) }) -> Tot macAlg
let macAlg_of_aeAlg pv ae =
    match pv,ae with
//  | SSL_3p0,MACOnly alg -> SSLKHASH alg (* dropped pattern on the left to simplify refinements *)
    | _      ,MACOnly alg -> SSLKHASH alg 
    | SSL_3p0,MtE _ alg   -> SSLKHASH alg
    | _      ,MtE _ alg   -> HMAC alg

type cipherSuiteName =
    | TLS_NULL_WITH_NULL_NULL

    | TLS_RSA_WITH_NULL_MD5
    | TLS_RSA_WITH_NULL_SHA
    | TLS_RSA_WITH_NULL_SHA256
    | TLS_RSA_WITH_RC4_128_MD5
    | TLS_RSA_WITH_RC4_128_SHA
    | TLS_RSA_WITH_3DES_EDE_CBC_SHA
    | TLS_RSA_WITH_AES_128_CBC_SHA
    | TLS_RSA_WITH_AES_256_CBC_SHA
    | TLS_RSA_WITH_AES_128_CBC_SHA256
    | TLS_RSA_WITH_AES_256_CBC_SHA256

    | TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA
    | TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA
    | TLS_DHE_DSS_WITH_AES_128_CBC_SHA
    | TLS_DHE_RSA_WITH_AES_128_CBC_SHA
    | TLS_DHE_DSS_WITH_AES_256_CBC_SHA
    | TLS_DHE_RSA_WITH_AES_256_CBC_SHA
    | TLS_DHE_DSS_WITH_AES_128_CBC_SHA256
    | TLS_DHE_RSA_WITH_AES_128_CBC_SHA256
    | TLS_DHE_DSS_WITH_AES_256_CBC_SHA256
    | TLS_DHE_RSA_WITH_AES_256_CBC_SHA256

    | TLS_ECDHE_RSA_WITH_RC4_128_SHA
    | TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA
    | TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
    | TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
    | TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
    | TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384

    | TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
    | TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384

    | TLS_DH_anon_WITH_RC4_128_MD5
    | TLS_DH_anon_WITH_3DES_EDE_CBC_SHA
    | TLS_DH_anon_WITH_AES_128_CBC_SHA
    | TLS_DH_anon_WITH_AES_256_CBC_SHA
    | TLS_DH_anon_WITH_AES_128_CBC_SHA256
    | TLS_DH_anon_WITH_AES_256_CBC_SHA256

    | TLS_RSA_WITH_AES_128_GCM_SHA256
    | TLS_RSA_WITH_AES_256_GCM_SHA384
    | TLS_DHE_RSA_WITH_AES_128_GCM_SHA256
    | TLS_DHE_RSA_WITH_AES_256_GCM_SHA384
    | TLS_DH_RSA_WITH_AES_128_GCM_SHA256
    | TLS_DH_RSA_WITH_AES_256_GCM_SHA384
    | TLS_DHE_DSS_WITH_AES_128_GCM_SHA256
    | TLS_DHE_DSS_WITH_AES_256_GCM_SHA384
    | TLS_DH_DSS_WITH_AES_128_GCM_SHA256
    | TLS_DH_DSS_WITH_AES_256_GCM_SHA384
    | TLS_DH_anon_WITH_AES_128_GCM_SHA256
    | TLS_DH_anon_WITH_AES_256_GCM_SHA384

type cipherSuiteNames = list cipherSuiteName

#set-options "--max_ifuel 5 --initial_ifuel 5 --max_fuel 1 --initial_fuel 1"
val cipherSuite_of_name: cipherSuiteName -> Tot known_cipher_suite
let cipherSuite_of_name = function
    | TLS_NULL_WITH_NULL_NULL                -> NullCipherSuite

    | TLS_RSA_WITH_NULL_MD5                  -> CipherSuite Kex_RSA None (MACOnly MD5)
    | TLS_RSA_WITH_NULL_SHA                  -> CipherSuite Kex_RSA None (MACOnly SHA1)
    | TLS_RSA_WITH_NULL_SHA256               -> CipherSuite Kex_RSA None (MACOnly SHA256)
    | TLS_RSA_WITH_RC4_128_MD5               -> CipherSuite Kex_RSA None (MtE (Stream RC4_128) MD5)
    | TLS_RSA_WITH_RC4_128_SHA               -> CipherSuite Kex_RSA None (MtE (Stream RC4_128) SHA1)
    | TLS_RSA_WITH_3DES_EDE_CBC_SHA          -> CipherSuite Kex_RSA None (MtE (Block TDES_EDE_CBC) SHA1)
    | TLS_RSA_WITH_AES_128_CBC_SHA           -> CipherSuite Kex_RSA None (MtE (Block AES_128_CBC) SHA1)
    | TLS_RSA_WITH_AES_256_CBC_SHA           -> CipherSuite Kex_RSA None (MtE (Block AES_256_CBC) SHA1)
    | TLS_RSA_WITH_AES_128_CBC_SHA256        -> CipherSuite Kex_RSA None (MtE (Block AES_128_CBC) SHA256)
    | TLS_RSA_WITH_AES_256_CBC_SHA256        -> CipherSuite Kex_RSA None (MtE (Block AES_256_CBC) SHA256)

    | TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA      -> CipherSuite Kex_DHE (Some DSA) (MtE (Block TDES_EDE_CBC) SHA1)
    | TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA      -> CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)
    | TLS_DHE_DSS_WITH_AES_128_CBC_SHA       -> CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_128_CBC) SHA1)
    | TLS_DHE_RSA_WITH_AES_128_CBC_SHA       -> CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1)
    | TLS_DHE_DSS_WITH_AES_256_CBC_SHA       -> CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_256_CBC) SHA1)
    | TLS_DHE_RSA_WITH_AES_256_CBC_SHA       -> CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1)
    | TLS_DHE_DSS_WITH_AES_128_CBC_SHA256    -> CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_128_CBC) SHA256)
    | TLS_DHE_RSA_WITH_AES_128_CBC_SHA256    -> CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256)
    | TLS_DHE_DSS_WITH_AES_256_CBC_SHA256    -> CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_256_CBC) SHA256)
    | TLS_DHE_RSA_WITH_AES_256_CBC_SHA256    -> CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA256)

    | TLS_ECDHE_RSA_WITH_RC4_128_SHA         -> CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1)
    | TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA    -> CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)
    | TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA     -> CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1)
    | TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256  -> CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256)
    | TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA     -> CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1)
    | TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384  -> CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA384)

    | TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256  -> CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_128_GCM SHA256)
    | TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384  -> CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_256_GCM SHA384)

    | TLS_DH_anon_WITH_RC4_128_MD5           -> CipherSuite Kex_DHE None (MtE (Stream RC4_128) MD5)
    | TLS_DH_anon_WITH_3DES_EDE_CBC_SHA      -> CipherSuite Kex_DHE None (MtE (Block TDES_EDE_CBC) SHA1)
    | TLS_DH_anon_WITH_AES_128_CBC_SHA       -> CipherSuite Kex_DHE None (MtE (Block AES_128_CBC) SHA1)
    | TLS_DH_anon_WITH_AES_256_CBC_SHA       -> CipherSuite Kex_DHE None (MtE (Block AES_256_CBC) SHA1)
    | TLS_DH_anon_WITH_AES_128_CBC_SHA256    -> CipherSuite Kex_DHE None (MtE (Block AES_128_CBC) SHA256)
    | TLS_DH_anon_WITH_AES_256_CBC_SHA256    -> CipherSuite Kex_DHE None (MtE (Block AES_256_CBC) SHA256)

    | TLS_RSA_WITH_AES_128_GCM_SHA256        -> CipherSuite Kex_RSA None     (AEAD AES_128_GCM SHA256)
    | TLS_RSA_WITH_AES_256_GCM_SHA384        -> CipherSuite Kex_RSA None     (AEAD AES_256_GCM SHA384)
    | TLS_DHE_RSA_WITH_AES_128_GCM_SHA256    -> CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_128_GCM SHA256)
    | TLS_DHE_RSA_WITH_AES_256_GCM_SHA384    -> CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_256_GCM SHA384)
    | TLS_DH_RSA_WITH_AES_128_GCM_SHA256     -> CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_128_GCM SHA256)
    | TLS_DH_RSA_WITH_AES_256_GCM_SHA384     -> CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_256_GCM SHA384)
    | TLS_DHE_DSS_WITH_AES_128_GCM_SHA256    -> CipherSuite Kex_DHE (Some DSA) (AEAD AES_128_GCM SHA256)
    | TLS_DHE_DSS_WITH_AES_256_GCM_SHA384    -> CipherSuite Kex_DHE (Some DSA) (AEAD AES_256_GCM SHA384)
    | TLS_DH_DSS_WITH_AES_128_GCM_SHA256     -> CipherSuite Kex_DH (Some DSA)  (AEAD AES_128_GCM SHA256)
    | TLS_DH_DSS_WITH_AES_256_GCM_SHA384     -> CipherSuite Kex_DH (Some DSA)  (AEAD AES_256_GCM SHA384)
    | TLS_DH_anon_WITH_AES_128_GCM_SHA256    -> CipherSuite Kex_DHE None (AEAD AES_128_GCM SHA256)
    | TLS_DH_anon_WITH_AES_256_GCM_SHA384    -> CipherSuite Kex_DHE None (AEAD AES_256_GCM SHA384)

val cipherSuites_of_nameList: l1:list cipherSuiteName -> l2:known_cipher_suites{List.length l2 = List.length l1}
let cipherSuites_of_nameList nameList = List.mapT cipherSuite_of_name nameList

let name_of_cipherSuite cs =
    match cs with
    | NullCipherSuite                                  ->  Correct TLS_NULL_WITH_NULL_NULL

    | CipherSuite Kex_RSA None (MACOnly MD5)                       ->  Correct TLS_RSA_WITH_NULL_MD5
    | CipherSuite Kex_RSA None (MACOnly SHA1)                       ->  Correct TLS_RSA_WITH_NULL_SHA
    | CipherSuite Kex_RSA None (MACOnly SHA256)                    ->  Correct TLS_RSA_WITH_NULL_SHA256
    | CipherSuite Kex_RSA None (MtE (Stream RC4_128) MD5)             ->  Correct TLS_RSA_WITH_RC4_128_MD5
    | CipherSuite Kex_RSA None (MtE (Stream RC4_128) SHA1)             ->  Correct TLS_RSA_WITH_RC4_128_SHA
    | CipherSuite Kex_RSA None (MtE (Block TDES_EDE_CBC) SHA1)        ->  Correct TLS_RSA_WITH_3DES_EDE_CBC_SHA
    | CipherSuite Kex_RSA None (MtE (Block AES_128_CBC) SHA1)         ->  Correct TLS_RSA_WITH_AES_128_CBC_SHA
    | CipherSuite Kex_RSA None (MtE (Block AES_256_CBC) SHA1)         ->  Correct TLS_RSA_WITH_AES_256_CBC_SHA
    | CipherSuite Kex_RSA None (MtE (Block AES_128_CBC) SHA256)      ->  Correct TLS_RSA_WITH_AES_128_CBC_SHA256
    | CipherSuite Kex_RSA None (MtE (Block AES_256_CBC) SHA256)      ->  Correct TLS_RSA_WITH_AES_256_CBC_SHA256

    | CipherSuite Kex_DHE (Some DSA) (MtE (Block TDES_EDE_CBC) SHA1)    ->  Correct TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)    ->  Correct TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA
    | CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_128_CBC) SHA1)     ->  Correct TLS_DHE_DSS_WITH_AES_128_CBC_SHA
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1)     ->  Correct TLS_DHE_RSA_WITH_AES_128_CBC_SHA
    | CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_256_CBC) SHA1)     ->  Correct TLS_DHE_DSS_WITH_AES_256_CBC_SHA
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1)     ->  Correct TLS_DHE_RSA_WITH_AES_256_CBC_SHA
    | CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_128_CBC) SHA256)  ->  Correct TLS_DHE_DSS_WITH_AES_128_CBC_SHA256
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256)  ->  Correct TLS_DHE_RSA_WITH_AES_128_CBC_SHA256
    | CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_256_CBC) SHA256)  ->  Correct TLS_DHE_DSS_WITH_AES_256_CBC_SHA256
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA256)  ->  Correct TLS_DHE_RSA_WITH_AES_256_CBC_SHA256

    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1)       ->  Correct TLS_ECDHE_RSA_WITH_RC4_128_SHA
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)  ->  Correct TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1)   ->  Correct TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256) -> Correct TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1)    ->  Correct TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA384) -> Correct TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384

    | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_128_GCM SHA256) -> Correct TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
    | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_256_GCM SHA384) -> Correct TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384

    | CipherSuite Kex_DHE None (MtE (Stream RC4_128) MD5)         ->  Correct TLS_DH_anon_WITH_RC4_128_MD5
    | CipherSuite Kex_DHE None (MtE (Block TDES_EDE_CBC) SHA1)    ->  Correct TLS_DH_anon_WITH_3DES_EDE_CBC_SHA
    | CipherSuite Kex_DHE None (MtE (Block AES_128_CBC) SHA1)     ->  Correct TLS_DH_anon_WITH_AES_128_CBC_SHA
    | CipherSuite Kex_DHE None (MtE (Block AES_256_CBC) SHA1)     ->  Correct TLS_DH_anon_WITH_AES_256_CBC_SHA
    | CipherSuite Kex_DHE None (MtE (Block AES_128_CBC) SHA256)  ->  Correct TLS_DH_anon_WITH_AES_128_CBC_SHA256
    | CipherSuite Kex_DHE None (MtE (Block AES_256_CBC) SHA256)  ->  Correct TLS_DH_anon_WITH_AES_256_CBC_SHA256

    | CipherSuite Kex_RSA None     (AEAD AES_128_GCM SHA256)  ->  Correct TLS_RSA_WITH_AES_128_GCM_SHA256
    | CipherSuite Kex_RSA None     (AEAD AES_256_GCM SHA384)  ->  Correct TLS_RSA_WITH_AES_256_GCM_SHA384
    | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_128_GCM SHA256)  ->  Correct TLS_DHE_RSA_WITH_AES_128_GCM_SHA256
    | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_256_GCM SHA384)  ->  Correct TLS_DHE_RSA_WITH_AES_256_GCM_SHA384
    | CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_128_GCM SHA256)  ->  Correct TLS_DH_RSA_WITH_AES_128_GCM_SHA256
    | CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_256_GCM SHA384)  ->  Correct TLS_DH_RSA_WITH_AES_256_GCM_SHA384
    | CipherSuite Kex_DHE (Some DSA) (AEAD AES_128_GCM SHA256)  ->  Correct TLS_DHE_DSS_WITH_AES_128_GCM_SHA256
    | CipherSuite Kex_DHE (Some DSA) (AEAD AES_256_GCM SHA384)  ->  Correct TLS_DHE_DSS_WITH_AES_256_GCM_SHA384
    | CipherSuite Kex_DH (Some DSA)  (AEAD AES_128_GCM SHA256)  ->  Correct TLS_DH_DSS_WITH_AES_128_GCM_SHA256
    | CipherSuite Kex_DH (Some DSA)  (AEAD AES_256_GCM SHA384)  ->  Correct TLS_DH_DSS_WITH_AES_256_GCM_SHA384
    | CipherSuite Kex_DHE None (AEAD AES_128_GCM SHA256)  ->  Correct TLS_DH_anon_WITH_AES_128_GCM_SHA256
    | CipherSuite Kex_DHE None (AEAD AES_256_GCM SHA384)  ->  Correct TLS_DH_anon_WITH_AES_256_GCM_SHA384

    | _ -> Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Invoked on a unknown ciphersuite")

val names_of_cipherSuites : cipherSuites -> Tot (Result cipherSuiteNames)
let rec names_of_cipherSuites css =
    match css with
    | [] -> Correct []
    | h::t ->
       begin match name_of_cipherSuite h with
             | Error(x,y) -> Error(x,y)
             | Correct(n) ->
                begin match names_of_cipherSuites t with
                      | Error(x,y) -> Error(x,y)
                      | Correct(rem) -> Correct (n::rem)
                end
       end

(* TLS messages types *)
type ContentType =
    | Change_cipher_spec
    | Alert
    | Handshake
    | Application_data

val ctBytes: ContentType -> Tot (lbytes 1)
let ctBytes ct =
    match ct with
    | Change_cipher_spec -> abyte 20uy
    | Alert              -> abyte 21uy
    | Handshake          -> abyte 22uy
    | Application_data   -> abyte 23uy

val parseCT: pinverse_t ctBytes
let parseCT b =
    match cbyte b with
    | 20uy -> Correct Change_cipher_spec
    | 21uy -> Correct Alert
    | 22uy -> Correct Handshake
    | 23uy -> Correct Application_data
    | _        -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val inverse_ct: x:_ -> Lemma
  (requires (True)) 
  (ensures lemma_inverse_g_f ctBytes parseCT x)
  [SMTPat (parseCT (ctBytes x))]
let inverse_ct x = ()

val pinverse_ct: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.Eq ctBytes parseCT x))
  [SMTPat (ctBytes (Correct._0 (parseCT x)))]
let pinverse_ct x = ()

let ctToString = function
    | Change_cipher_spec -> "CCS"
    | Alert              -> "Alert"
    | Handshake          -> "Handshake"
    | Application_data   -> "Data"

val bytes_of_seq: n:nat{ repr_bytes n <= 8 } -> Tot bytes
let bytes_of_seq sn = bytes_of_int 8 sn
val seq_of_bytes: b:bytes{ length b <= 8 } -> Tot nat
let seq_of_bytes b = int_of_bytes b

val vlbytes: lSize:nat -> b:bytes{repr_bytes (length b) <= lSize} -> Tot (r:bytes{length r = lSize + length b})
let vlbytes lSize b = bytes_of_int lSize (length b) @| b

val lemma_vlbytes_inj : i:nat
          -> b:bytes{repr_bytes (length b) <= i}
          -> b':bytes{repr_bytes (length b') <= i}
          -> Lemma (requires (Seq.Eq (vlbytes i b) (vlbytes i b')))
                   (ensures (b=b'))
let lemma_vlbytes_inj i b b' =
  let l = bytes_of_int i (length b) in
  SeqProperties.lemma_append_inj l b l b'

#set-options "--max_ifuel 1 --initial_ifuel 1 --max_fuel 0 --initial_fuel 0"   //need to reason about length
val vlsplit: lSize:nat{lSize <= 4}
  -> vlb:bytes{lSize <= length vlb}
  -> Tot (Result (b:(bytes * bytes){
                      repr_bytes (length (fst b)) <= lSize
                  /\  Seq.Eq vlb (vlbytes lSize (fst b) @| (snd b))}))
let vlsplit lSize vlb =
  let (vl,b) = Platform.Bytes.split vlb lSize in
  let l = int_of_bytes vl in
  if l <= length b
  then Correct(Platform.Bytes.split b l)
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val vlparse: lSize:nat{lSize <= 4} -> vlb:bytes{lSize <= length vlb}
             -> Tot (Result (b:bytes{repr_bytes (length b) <= lSize /\ Seq.Eq vlb (vlbytes lSize b)}))
let vlparse lSize vlb =
    let (vl,b) = Platform.Bytes.split vlb lSize in
    let l = int_of_bytes vl in
    if l = length b
    then Correct b
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val lemma_vlbytes_len : i:nat -> b:bytes{repr_bytes (length b) <= i}
                        -> Lemma (ensures (length (vlbytes i b) = i + length b))
let lemma_vlbytes_len i b = ()

type certType =
    | RSA_sign
    | DSA_sign
    | RSA_fixed_dh
    | DSA_fixed_dh

val certTypeBytes : certType -> Tot (lbytes 1)
let certTypeBytes ct =
    match ct with
    | RSA_sign     -> abyte (1uy)
    | DSA_sign     -> abyte (2uy)
    | RSA_fixed_dh -> abyte (3uy)
    | DSA_fixed_dh -> abyte (4uy)

val parseCertType: pinverse_t certTypeBytes
let parseCertType b =
    match cbyte b with
    | (1uy) -> Correct(RSA_sign)
    | (2uy) -> Correct(DSA_sign)
    | (3uy) -> Correct(RSA_fixed_dh)
    | (4uy) -> Correct(DSA_fixed_dh)
    | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val inverse_certType: x:_ -> Lemma
  (requires (True)) 
  (ensures lemma_inverse_g_f certTypeBytes parseCertType x)
  [SMTPat (parseCertType (certTypeBytes x))]
let inverse_certType x = ()

val pinverse_certType: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.Eq certTypeBytes parseCertType x))
  [SMTPat (certTypeBytes (Correct._0 (parseCertType x)))]
let pinverse_certType x = ()

#set-options "--max_fuel 1 --initial_fuel 1"
val certificateTypeListBytes: ctl:list certType -> Tot (lbytes (List.length ctl))
let rec certificateTypeListBytes ctl =
    match ctl with
    | [] -> empty_bytes
    | h::t ->
        let ct = certTypeBytes h in
        ct @| certificateTypeListBytes t

val parseCertificateTypeList: data:bytes -> Tot (list certType) (decreases (length data))
let rec parseCertificateTypeList data =
  let l = length data in
    if l = 0 then []
    else
        let (thisByte,data) = Platform.Bytes.split data 1 in
        match parseCertType thisByte with
        | Error(z) -> // we skip this one
            parseCertificateTypeList data
        | Correct(ct) ->
            let rem = parseCertificateTypeList data in
            ct :: rem

#set-options "--max_ifuel 4 --initial_ifuel 1 --max_fuel 4 --initial_fuel 1"

val defaultCertTypes: bool -> cipherSuite -> l:list certType{List.length l <= 1}
let defaultCertTypes sign cs =
  let alg = sigAlg_of_ciphersuite cs in
    if sign then
      match alg with
        | RSASIG -> [RSA_sign]
        | DSA -> [DSA_sign]
        | _ -> unexpected "[defaultCertTypes] invoked on an invalid ciphersuite"
    else
      match alg with
        | RSASIG -> [RSA_fixed_dh]
        | DSA -> [DSA_fixed_dh]
        | _ -> unexpected "[defaultCertTypes] invoked on an invalid ciphersuite"

type dn = s:string{length(utf8 s) <= 256}
val distinguishedNameListBytes: names:list dn -> Tot (b:bytes{length b <= 258 * List.length names})
let rec distinguishedNameListBytes names =
    match names with
    | [] -> empty_bytes
    | h::t ->
        lemma_repr_bytes_values (length (utf8 h));
        let name = vlbytes 2 (utf8 h) in
        name @| distinguishedNameListBytes t

val parseDistinguishedNameList: data:bytes -> res:list string -> Tot (Result (list string)) (decreases (length data))
let rec parseDistinguishedNameList data res =
    if length data = 0 then
        Correct (res)
    else
        if length data < 2 then
            Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
        else
            match vlsplit 2 data with
            | Error(z) -> Error(z)
            | Correct (nameBytes,data) ->
               begin match iutf8_opt nameBytes with
                     | None -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
                     | Some name ->
                        let res = name :: res in
                        parseDistinguishedNameList data res
               end

let contains_TLS_EMPTY_RENEGOTIATION_INFO_SCSV (css: list cipherSuite) =
    List.mem (SCSV (TLS_EMPTY_RENEGOTIATION_INFO_SCSV)) css

// let test_me () = assert False
