(* This file implements type representations and parsing functions
   for the different values negotiated during the TLS
   handshake. For instance protocol version, key exchange mechanism,
   hash algorithm etc. *)
module TLSConstants

(* SMT solver parameters *)
#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1"

open FStar.SeqProperties
open Platform.Bytes
open Platform.Error
open TLSError
open CoreCrypto

(* Type representations for TLS negotiated values *)
type protocolVersion =
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
    | Hash of hash_alg (* Defined in CoreCrypto library *)

type macAlg =
    | HMAC     of hash_alg
    | SSLKHASH of hash_alg

type aeAlg =
    | MACOnly : hash_alg -> aeAlg
    | MtE   : encAlg -> hash_alg -> aeAlg
    | AEAD  : aeadAlg -> hash_alg -> aeAlg

// does this algorithm provide padding support with TLS 1.2? 
let lhae = function
  | MtE (Block _) _                         -> true
  | MACOnly _ | AEAD _ _ | MtE (Stream _) _ -> false 
   

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

//CF we leave these functions abstract for verification purposes
//CF we may need to be more negative on weak algorithms (so that we don't try to verify their use)
//CF and more precise/positive on algorithms we implement (so that we reflect lower assumptions)

type sigAlg = CoreCrypto.sig_alg

type sigHashAlg = sigAlg * hashAlg


(* Serializing function for signature algorithms *)
val sigAlgBytes: sigAlg -> Tot (lbytes 1)
let sigAlgBytes sa =
    match sa with
    | CoreCrypto.RSASIG -> abyte 1z
    | CoreCrypto.DSA    -> abyte 2z
    | CoreCrypto.ECDSA  -> abyte 3z
    | CoreCrypto.RSAPSS -> abyte 4z

(* This is the old version of the inverse predicate. According to CF,
   verification was harder with this style, so we moved to the new style with
   pinverse_t + lemmas. The type abbrevations lemma_inverse_* minimize the
   syntactic overhead. *)
(* logic type pinverse (#a:Type) (#b:Type) (r:(b -> b -> Type)) (=f:(a -> Tot b)) =
    (y:b -> Tot (xopt:result a{(forall (x:a). r (f x) y <==> (xopt = Correct x))})) *)

type pinverse_t (#a:Type) (#b:Type) ($f:(a -> Tot b)) =
    (y:b -> Tot (result a))

(* Parsing function associated to sigAlgBytes *)
val parseSigAlg: pinverse_t sigAlgBytes
let parseSigAlg b =
    match cbyte b with
    | 1z -> Correct CoreCrypto.RSASIG
    | 2z -> Correct CoreCrypto.DSA
    | 3z -> Correct CoreCrypto.ECDSA
    | 4z -> Correct CoreCrypto.RSAPSS
    | _ -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

inline type lemma_inverse_g_f (#a:Type) (#b:Type) ($f:(a -> Tot b)) ($g:(b -> Tot (result a))) (x:a) = 
  g (f x) = Correct x

inline type lemma_pinverse_f_g (#a:Type) (#b:Type) (r:b -> b -> Type) ($f:(a -> Tot b)) ($g:(b -> Tot (result a))) (y:b) =
  is_Correct (g y) ==> r (f (Correct._0 (g y))) y

val inverse_sigAlg: x:_ -> Lemma
  (requires (True)) 
  (ensures lemma_inverse_g_f sigAlgBytes parseSigAlg x)
  [SMTPat (parseSigAlg (sigAlgBytes x))]
let inverse_sigAlg x = ()

val pinverse_sigAlg: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal sigAlgBytes parseSigAlg x))
  [SMTPat (sigAlgBytes (Correct._0 (parseSigAlg x)))]
let pinverse_sigAlg x = ()


type hashAlg' = h:hashAlg{h <> NULL /\ h <> MD5SHA1 }

#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 2"
val hashAlgBytes: hashAlg' -> Tot (lbytes 1)
 let hashAlgBytes ha =
   match ha with
    | Hash MD5     -> abyte 1z
    | Hash SHA1    -> abyte 2z
    | Hash SHA224  -> abyte 3z
    | Hash SHA256  -> abyte 4z
    | Hash SHA384  -> abyte 5z
    | Hash SHA512  -> abyte 6z

val parseHashAlg: pinverse_t hashAlgBytes
let parseHashAlg b =
    match cbyte b with
    | 1z -> Correct (Hash MD5)
    | 2z -> Correct (Hash SHA1)
    | 3z -> Correct (Hash SHA224)
    | 4z -> Correct (Hash SHA256)
    | 5z -> Correct (Hash SHA384)
    | 6z -> Correct (Hash SHA512)
    | _ -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val inverse_hashAlg: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f hashAlgBytes parseHashAlg x)
  [SMTPat (parseHashAlg (hashAlgBytes x))]
let inverse_hashAlg x = ()

val pinverse_hashAlg: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal hashAlgBytes parseHashAlg x))
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

type scsv_suite =
    | TLS_EMPTY_RENEGOTIATION_INFO_SCSV

type cipherSuite =
    | NullCipherSuite    : cipherSuite
    | CipherSuite        : kexAlg -> option sig_alg -> aeAlg -> cipherSuite
    | SCSV               : scsv_suite -> cipherSuite

type cipherSuites = list cipherSuite

type compression =
    | NullCompression
    | UnknownCompression of byte

val parseCompression: b:bytes{Seq.length b > 0} -> Tot compression
let parseCompression b =
    match cbyte b with
    | 0z -> NullCompression
    | b   -> UnknownCompression b

// We ignore compression methods we don't understand. This is a departure
// from usual parsing, where we fail on unknown values, but that's how TLS
// handles compression method lists.
val parseCompressions: b:bytes -> Tot (list compression) (decreases (length b))
let rec parseCompressions b =
    let l = length b in
    if l > 0
    then
        let (cmB,b) = split b 1 in
        let cm = parseCompression cmB in
        cm :: parseCompressions b
    else []

val compressionBytes: compression -> Tot (lbytes 1)
let compressionBytes (comp:compression) =
    match comp with
    | NullCompression -> abyte 0z
    | UnknownCompression b -> abyte b

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

#set-options "--max_ifuel 4 --initial_ifuel 2 --max_fuel 2 --initial_fuel 2"

val compressionMethodsBytes : cms:list compression -> Tot (lbytes (List.Tot.length cms))
let rec compressionMethodsBytes cms =
   match cms with
   | c::cs -> compressionBytes c @| compressionMethodsBytes cs
   | []    -> empty_bytes

#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1"
val versionBytes : protocolVersion -> Tot (lbytes 2)
let versionBytes pv =
    match pv with
    | SSL_3p0 -> abyte2 ( 3z, 0z)
    | TLS_1p0 -> abyte2 ( 3z, 1z)
    | TLS_1p1 -> abyte2 ( 3z, 2z )
    | TLS_1p2 -> abyte2 ( 3z, 3z )
    | TLS_1p3 -> abyte2 ( 3z, 4z )

val parseVersion: pinverse_t versionBytes
let parseVersion v =
    match cbyte2 v with
    | ( 3z, 0z ) -> Correct(SSL_3p0)
    | ( 3z, 1z ) -> Correct(TLS_1p0)
    | ( 3z, 2z ) -> Correct(TLS_1p1)
    | ( 3z, 3z ) -> Correct(TLS_1p2)
    | ( 3z, 4z ) -> Correct(TLS_1p3)
    | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Parsed an unknown version")

val inverse_version: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f versionBytes parseVersion x)
  [SMTPat (parseVersion (versionBytes x))]
let inverse_version x = ()

val pinverse_version: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal versionBytes parseVersion x))
  [SMTPat (versionBytes (Correct._0 (parseVersion x)))]
let pinverse_version x = ()

let minPV (a:protocolVersion) (b:protocolVersion) =
  match (a,b) with
  | SSL_3p0, _  | _, SSL_3p0 -> SSL_3p0
  | TLS_1p0, _  | _, TLS_1p0 -> TLS_1p0
  | TLS_1p1, _  | _, TLS_1p1 -> TLS_1p1
  | TLS_1p2, _  | _, TLS_1p2 -> TLS_1p2
  | TLS_1p3, _  | _, TLS_1p3 -> TLS_1p3

let somePV (a:protocolVersion) = Some a
let geqPV a b = (b = minPV a b)


let nullCipherSuite = NullCipherSuite

let isNullCipherSuite cs = (cs = NullCipherSuite)

val cipherSuiteBytesOpt: cipherSuite -> Tot (option (lbytes 2))
let cipherSuiteBytesOpt cs =
  let abyte2 b : option (lbytes 2) = Some (abyte2 b) in
    match cs with
    | NullCipherSuite                                 -> abyte2 ( 0x00z, 0x00z )

    | CipherSuite Kex_RSA None (MACOnly MD5)                       -> abyte2 ( 0x00z, 0x01z )
    | CipherSuite Kex_RSA None (MACOnly SHA1)                      -> abyte2 ( 0x00z, 0x02z )
    | CipherSuite Kex_RSA None (MACOnly SHA256)                    -> abyte2 ( 0x00z, 0x3Bz )
    | CipherSuite Kex_RSA None(MtE (Stream RC4_128) MD5)           -> abyte2 ( 0x00z, 0x04z )
    | CipherSuite Kex_RSA None(MtE (Stream RC4_128) SHA1)          -> abyte2 ( 0x00z, 0x05z )

    | CipherSuite Kex_RSA None(MtE (Block TDES_EDE_CBC) SHA1)      -> abyte2 ( 0x00z, 0x0Az )
    | CipherSuite Kex_RSA None(MtE (Block AES_128_CBC) SHA1)       -> abyte2 ( 0x00z, 0x2Fz )
    | CipherSuite Kex_RSA None(MtE (Block AES_256_CBC) SHA1)       -> abyte2 ( 0x00z, 0x35z )
    | CipherSuite Kex_RSA None(MtE (Block AES_128_CBC) SHA256)     -> abyte2 ( 0x00z, 0x3Cz )
    | CipherSuite Kex_RSA None(MtE (Block AES_256_CBC) SHA256)     -> abyte2 ( 0x00z, 0x3Dz )

    (**************************************************************************)
    | CipherSuite Kex_DH (Some DSA)     (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0x00z, 0x0Dz )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0x00z, 0x10z )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0x00z, 0x13z )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0x00z, 0x16z )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0x00z, 0x30z )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0x00z, 0x31z )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0x00z, 0x32z )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0x00z, 0x33z )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0x00z, 0x36z )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0x00z, 0x37z )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0x00z, 0x38z )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0x00z, 0x39z )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0x00z, 0x3Ez )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0x00z, 0x3Fz )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0x00z, 0x40z )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0x00z, 0x67z )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_256_CBC) SHA256)  -> abyte2 ( 0x00z, 0x68z )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_256_CBC) SHA256)  -> abyte2 ( 0x00z, 0x69z )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_256_CBC) SHA256)  -> abyte2 ( 0x00z, 0x6Az )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA256)  -> abyte2 ( 0x00z, 0x6Bz )

    (**************************************************************************)
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1)       -> abyte2 ( 0xc0z, 0x11z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)   -> abyte2 ( 0xc0z, 0x12z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1)    -> abyte2 ( 0xc0z, 0x13z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1)    -> abyte2 ( 0xc0z, 0x14z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256)  -> abyte2 ( 0xc0z, 0x27z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA384)  -> abyte2 ( 0xc0z, 0x28z )

    | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_128_GCM SHA256) -> abyte2 ( 0xc0z, 0x2fz )
    | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_256_GCM SHA384) -> abyte2 ( 0xc0z, 0x30z )

    (**************************************************************************)
    | CipherSuite Kex_DHE None   (MtE (Stream RC4_128) MD5)         -> abyte2 ( 0x00z, 0x18z )
    | CipherSuite Kex_DHE None   (MtE (Block TDES_EDE_CBC) SHA1)    -> abyte2 ( 0x00z, 0x1Bz )
    | CipherSuite Kex_DHE None   (MtE (Block AES_128_CBC) SHA1)     -> abyte2 ( 0x00z, 0x34z )
    | CipherSuite Kex_DHE None   (MtE (Block AES_256_CBC) SHA1)     -> abyte2 ( 0x00z, 0x3Az )
    | CipherSuite Kex_DHE None   (MtE (Block AES_128_CBC) SHA256)   -> abyte2 ( 0x00z, 0x6Cz )
    | CipherSuite Kex_DHE None   (MtE (Block AES_256_CBC) SHA256)   -> abyte2 ( 0x00z, 0x6Dz )

    (**************************************************************************)
    | CipherSuite Kex_RSA None     (AEAD AES_128_GCM SHA256) -> abyte2( 0x00z, 0x9Cz )
    | CipherSuite Kex_RSA None     (AEAD AES_256_GCM SHA384) -> abyte2( 0x00z, 0x9Dz )

    | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_128_GCM SHA256) -> abyte2( 0x00z, 0x9Ez )
    | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_256_GCM SHA384) -> abyte2( 0x00z, 0x9Fz )
    | CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_128_GCM SHA256) -> abyte2( 0x00z, 0xA0z )
    | CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_256_GCM SHA384) -> abyte2( 0x00z, 0xA1z )

    | CipherSuite Kex_DHE (Some DSA) (AEAD AES_128_GCM SHA256) -> abyte2( 0x00z, 0xA2z )
    | CipherSuite Kex_DHE (Some DSA) (AEAD AES_256_GCM SHA384) -> abyte2( 0x00z, 0xA3z )
    | CipherSuite Kex_DH (Some DSA)  (AEAD AES_128_GCM SHA256) -> abyte2( 0x00z, 0xA4z )
    | CipherSuite Kex_DH (Some DSA)  (AEAD AES_256_GCM SHA384) -> abyte2( 0x00z, 0xA5z )

    | CipherSuite Kex_DHE None (AEAD AES_128_GCM SHA256) -> abyte2( 0x00z, 0xA6z )
    | CipherSuite Kex_DHE None (AEAD AES_256_GCM SHA384) -> abyte2( 0x00z, 0xA7z )

    | SCSV (TLS_EMPTY_RENEGOTIATION_INFO_SCSV)         -> abyte2 ( 0x00z, 0xFFz )
    | _ -> None

let knownCipherSuite (c:cipherSuite) = is_Some (cipherSuiteBytesOpt c)
type known_cipher_suite = c:cipherSuite{knownCipherSuite c}
type known_cipher_suites = list known_cipher_suite

val cipherSuiteBytes: known_cipher_suite -> Tot (lbytes 2)
let cipherSuiteBytes c = Some.v (cipherSuiteBytesOpt c)

val parseCipherSuiteAux : lbytes 2 -> Tot (result cipherSuite)
let parseCipherSuiteAux b =
    match cbyte2 b with
    | ( 0x00z, 0x00z ) -> Correct(NullCipherSuite)

    | ( 0x00z, 0x01z ) -> Correct(CipherSuite Kex_RSA None (MACOnly MD5))
    | ( 0x00z, 0x02z ) -> Correct(CipherSuite Kex_RSA None (MACOnly SHA1))
    | ( 0x00z, 0x3Bz ) -> Correct(CipherSuite Kex_RSA None (MACOnly SHA256))
    | ( 0x00z, 0x04z ) -> Correct(CipherSuite Kex_RSA None (MtE (Stream RC4_128) MD5))
    | ( 0x00z, 0x05z ) -> Correct(CipherSuite Kex_RSA None (MtE (Stream RC4_128) SHA1))

    | ( 0x00z, 0x0Az ) -> Correct(CipherSuite Kex_RSA None (MtE (Block TDES_EDE_CBC) SHA1))
    | ( 0x00z, 0x2Fz ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES_128_CBC) SHA1))
    | ( 0x00z, 0x35z ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES_256_CBC) SHA1))
    | ( 0x00z, 0x3Cz ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES_128_CBC) SHA256))
    | ( 0x00z, 0x3Dz ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES_256_CBC) SHA256))

    (**************************************************************************)
    | ( 0x00z, 0x0Dz ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block TDES_EDE_CBC) SHA1))
    | ( 0x00z, 0x10z ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1))
    | ( 0x00z, 0x13z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block TDES_EDE_CBC) SHA1))
    | ( 0x00z, 0x16z ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1))

    | ( 0x00z, 0x30z ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES_128_CBC) SHA1))
    | ( 0x00z, 0x31z ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES_128_CBC) SHA1))
    | ( 0x00z, 0x32z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_128_CBC) SHA1))
    | ( 0x00z, 0x33z ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1))

    | ( 0x00z, 0x36z ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES_256_CBC) SHA1))
    | ( 0x00z, 0x37z ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES_256_CBC) SHA1))
    | ( 0x00z, 0x38z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_256_CBC) SHA1))
    | ( 0x00z, 0x39z ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1))

    | ( 0x00z, 0x3Ez ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES_128_CBC) SHA256))
    | ( 0x00z, 0x3Fz ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES_128_CBC) SHA256))
    | ( 0x00z, 0x40z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_128_CBC) SHA256))
    | ( 0x00z, 0x67z ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256))

    | ( 0x00z, 0x68z ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES_256_CBC) SHA256))
    | ( 0x00z, 0x69z ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES_256_CBC) SHA256))
    | ( 0x00z, 0x6Az ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES_256_CBC) SHA256))
    | ( 0x00z, 0x6Bz ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA256))

    (**************************************************************************)
    | ( 0xc0z, 0x11z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1))
    | ( 0xc0z, 0x12z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1))
    | ( 0xc0z, 0x13z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1))
    | ( 0xc0z, 0x14z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1))
    | ( 0xc0z, 0x27z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256))
    | ( 0xc0z, 0x28z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA384))

    | ( 0xc0z, 0x2fz ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_128_GCM SHA256))
    | ( 0xc0z, 0x30z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_256_GCM SHA384))

    (**************************************************************************)
    | ( 0x00z, 0x18z ) -> Correct(CipherSuite Kex_DHE None (MtE (Stream RC4_128) MD5))
    | ( 0x00z, 0x1Bz ) -> Correct(CipherSuite Kex_DHE None (MtE (Block TDES_EDE_CBC) SHA1))
    | ( 0x00z, 0x34z ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES_128_CBC) SHA1))
    | ( 0x00z, 0x3Az ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES_256_CBC) SHA1))
    | ( 0x00z, 0x6Cz ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES_128_CBC) SHA256))
    | ( 0x00z, 0x6Dz ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES_256_CBC) SHA256))

    (**************************************************************************)
    | ( 0x00z, 0x9Cz ) -> Correct(CipherSuite Kex_RSA None     (AEAD AES_128_GCM SHA256))
    | ( 0x00z, 0x9Dz ) -> Correct(CipherSuite Kex_RSA None     (AEAD AES_256_GCM SHA384))

    | ( 0x00z, 0x9Ez ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_128_GCM SHA256))
    | ( 0x00z, 0x9Fz ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_256_GCM SHA384))
    | ( 0x00z, 0xA0z ) -> Correct(CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_128_GCM SHA256))
    | ( 0x00z, 0xA1z ) -> Correct(CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_256_GCM SHA384))

    | ( 0x00z, 0xA2z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (AEAD AES_128_GCM SHA256))
    | ( 0x00z, 0xA3z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (AEAD AES_256_GCM SHA384))
    | ( 0x00z, 0xA4z ) -> Correct(CipherSuite Kex_DH (Some DSA)  (AEAD AES_128_GCM SHA256))
    | ( 0x00z, 0xA5z ) -> Correct(CipherSuite Kex_DH (Some DSA)  (AEAD AES_256_GCM SHA384))

    | ( 0x00z, 0xA6z ) -> Correct(CipherSuite Kex_DHE None (AEAD AES_128_GCM SHA256))
    | ( 0x00z, 0xA7z ) -> Correct(CipherSuite Kex_DHE None (AEAD AES_256_GCM SHA384))

    | ( 0x00z, 0xFFz ) -> Correct(SCSV (TLS_EMPTY_RENEGOTIATION_INFO_SCSV))

    | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Parsed unknown cipher")

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
			       /\ Seq.equal x (Some.v (cipherSuiteBytesOpt (Correct._0 y)))))))
  [SMTPat (cipherSuiteBytesOpt (Correct._0 (parseCipherSuiteAux x)))]
let pinverse_cipherSuite x = ()

#reset-options
#set-options "--max_ifuel 1 --initial_ifuel 1 --max_fuel 1 --initial_fuel 1"


(* Called by the server handshake; *)
(* ciphersuites that we do not understand are parsed, but ignored *)
val parseCipherSuites: b:bytes -> Tot (result known_cipher_suites) (decreases (length b))
let rec parseCipherSuites b : result known_cipher_suites =
     if length b > 1 then
       let (b0,b1) = split b 2 in
       match parseCipherSuites b1 with
         | Correct(css) ->
           (match parseCipherSuite b0 with
             | Error(z) ->    Correct (css)      (* ignore this cs *)
             | Correct(cs) -> Correct(cs::css))
         | Error(z) -> Error(z)
     else if length b = 0 then Correct ([])
     else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Odd cs bytes number")

val cipherSuitesBytes: css:known_cipher_suites -> Tot (lbytes (op_Multiply 2 (List.Tot.length css)))
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
  | PRF_TLS_1p3 // TBC

type kefAlg_t = prePrfAlg
type kdfAlg_t = prePrfAlg
type vdAlg_t = protocolVersion * cipherSuite

(* Only to be invoked with TLS 1.2 (hardcoded in previous versions *)
let verifyDataLen_of_ciphersuite (cs:cipherSuite) = 12

(* Only to be invoked with TLS 1.2 (hardcoded in previous versions *)
val prfMacAlg_of_ciphersuite_aux: cipherSuite -> Tot (option macAlg)
let prfMacAlg_of_ciphersuite_aux = function
    | CipherSuite  _ _  (MtE  _ _ )   -> Some (HMAC SHA256)
    | CipherSuite  _ _  (AEAD _ hAlg) -> Some (HMAC hAlg)
    | CipherSuite  _ _  (MACOnly _)  -> Some (HMAC SHA256) //MK was (MACOnly hAlg) should it also be be (HMAC hAlg)?
    | _                                -> None

let pvcs (pv:protocolVersion) (cs:cipherSuite) =
  match pv with
  | TLS_1p2 | TLS_1p3 -> is_Some (prfMacAlg_of_ciphersuite_aux cs)
  | _                 -> true

inline type require_some (#a:Type) (#b:Type) ($f:(a -> Tot (option b))) = 
  x:a{is_Some (f x)} -> Tot b

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

val sessionHashAlg: pv:protocolVersion -> cs:cipherSuite{pvcs pv cs} -> Tot hashAlg
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

val encAlg_of_aeAlg: (pv:protocolVersion) -> (a:aeAlg { is_MtE a }) -> Tot (encAlg * ivMode)
let encAlg_of_aeAlg  pv ae =
    match pv,ae with
    | SSL_3p0, MtE (Block e) m -> (Block e),Stale
    | TLS_1p0, MtE (Block e) m -> (Block e),Stale
    | _, MtE e m -> e,Fresh

val macAlg_of_aeAlg: (pv:protocolVersion) -> (a:aeAlg { pv <> TLS_1p3 /\ ~(is_AEAD a) }) -> Tot macAlg
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

val cipherSuites_of_nameList: l1:list cipherSuiteName -> l2:known_cipher_suites{List.Tot.length l2 = List.Tot.length l1}
let cipherSuites_of_nameList nameList = List.Tot.map cipherSuite_of_name nameList

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

#set-options "--max_ifuel 5 --initial_ifuel 5 --max_fuel 1 --initial_fuel 1"

val names_of_cipherSuites : cipherSuites -> Tot (result cipherSuiteNames)
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

// migrated contentType to Content.fst (this is internal to TLS)

val bytes_of_seq: n:nat{ repr_bytes n <= 8 } -> Tot bytes
let bytes_of_seq sn = bytes_of_int 8 sn
val seq_of_bytes: b:bytes{ length b <= 8 } -> Tot nat
let seq_of_bytes b = int_of_bytes b

val vlbytes: lSize:nat -> b:bytes{repr_bytes (length b) <= lSize} -> Tot (r:bytes{length r = lSize + length b})
let vlbytes lSize b = bytes_of_int lSize (length b) @| b

val lemma_vlbytes_inj : i:nat
          -> b:bytes{repr_bytes (length b) <= i}
          -> b':bytes{repr_bytes (length b') <= i}
          -> Lemma (requires (Seq.equal (vlbytes i b) (vlbytes i b')))
                   (ensures (b=b'))
let lemma_vlbytes_inj i b b' =
  let l = bytes_of_int i (length b) in
  SeqProperties.lemma_append_inj l b l b'

#set-options "--max_ifuel 1 --initial_ifuel 1 --max_fuel 0 --initial_fuel 0"   //need to reason about length
val vlsplit: lSize:nat{lSize <= 4}
  -> vlb:bytes{lSize <= length vlb}
  -> Tot (result (b:(bytes * bytes){
                    repr_bytes (length (fst b)) <= lSize
                  /\ Seq.equal vlb (vlbytes lSize (fst b) @| (snd b))}))
let vlsplit lSize vlb =
  let (vl,b) = Platform.Bytes.split vlb lSize in
  let l = int_of_bytes vl in
  if l <= length b
  then Correct(Platform.Bytes.split b l)
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val vlparse: lSize:nat{lSize <= 4} -> vlb:bytes //{lSize <= length vlb}
             -> Tot (result (b:bytes{repr_bytes (length b) <= lSize /\ Seq.equal vlb (vlbytes lSize b)}))
let vlparse lSize vlb =
    if lSize <= length vlb then
      let (vl,b) = Platform.Bytes.split vlb lSize in
      let l = int_of_bytes vl in
      if l = length b
      then Correct b
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
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
    | RSA_sign     -> abyte (1z)
    | DSA_sign     -> abyte (2z)
    | RSA_fixed_dh -> abyte (3z)
    | DSA_fixed_dh -> abyte (4z)

val parseCertType: pinverse_t certTypeBytes
let parseCertType b =
    match cbyte b with
    | (1z) -> Correct(RSA_sign)
    | (2z) -> Correct(DSA_sign)
    | (3z) -> Correct(RSA_fixed_dh)
    | (4z) -> Correct(DSA_fixed_dh)
    | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val inverse_certType: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f certTypeBytes parseCertType x)
  [SMTPat (parseCertType (certTypeBytes x))]
let inverse_certType x = ()

val pinverse_certType: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal certTypeBytes parseCertType x))
  [SMTPat (certTypeBytes (Correct._0 (parseCertType x)))]
let pinverse_certType x = ()

#set-options "--max_fuel 1 --initial_fuel 1"
val certificateTypeListBytes: ctl:list certType -> Tot (lbytes (List.Tot.length ctl))
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

val defaultCertTypes: bool -> cipherSuite -> l:list certType{List.Tot.length l <= 1}
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
val distinguishedNameListBytes: names:list dn -> Tot (b:bytes{length b <= op_Multiply 258  (List.Tot.length names)})
let rec distinguishedNameListBytes names =
    match names with
    | [] -> empty_bytes
    | h::t ->
        lemma_repr_bytes_values (length (utf8 h));
        let name = vlbytes 2 (utf8 h) in
        name @| distinguishedNameListBytes t

val parseDistinguishedNameList: data:bytes -> res:list string -> Tot (result (list string)) (decreases (length data))
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
    List.Tot.mem (SCSV (TLS_EMPTY_RENEGOTIATION_INFO_SCSV)) css


(* TODO: move all the definitions below to a separate file / figure out whether
 they belong here? *)
(* TODO: all occurrences of [pinverse] from there on have been replaced by calls
 to [pinverse_t]; we should write corresponding inversion lemmas. *)

type ffdhe =
  | FFDHE2048
  | FFDHE3072
  | FFDHE4096
  | FFDHE6144
  | FFDHE8192

(* TLS 1.3 constants *)
type namedGroup =
  | SEC of CoreCrypto.ec_curve
  | EC_UNSUPPORTED of byte
  | FFDHE of ffdhe
  | FFDHE_PRIVATE_USE of byte // fist byte is fixed
  | ECDHE_PRIVATE_USE of byte // fist byte is fixed

val namedGroupBytes: namedGroup -> Tot (lbytes 2)
let namedGroupBytes ng =
  match ng with
  | SEC ec ->
    (match ec with
    | ECC_P256                      -> abyte2 (0x00z, 0x17z)
    | ECC_P384                      -> abyte2 (0x00z, 0x18z)
    | ECC_P521                      -> abyte2 (0x00z, 0x19z))
  | EC_UNSUPPORTED(b)               -> abyte2 (0x00z, b)
  | FFDHE dhe ->
    (match dhe with
    | FFDHE2048                     -> abyte2 (0x01z, 0x00z)
    | FFDHE3072                     -> abyte2 (0x01z, 0x01z)
    | FFDHE4096                     -> abyte2 (0x01z, 0x02z)
    | FFDHE6144                     -> abyte2 (0x01z, 0x03z)
    | FFDHE8192                     -> abyte2 (0x01z, 0x04z)
  )
  | FFDHE_PRIVATE_USE(b)            -> abyte2 (0x01z, b)
  | ECDHE_PRIVATE_USE(b)            -> abyte2 (0xFEz, b)

val parseNamedGroup: pinverse_t namedGroupBytes
let parseNamedGroup b =
  match cbyte2 b with
  | (0x00z, 0x17z) -> Correct (SEC(ECC_P256))
  | (0x00z, 0x18z) -> Correct (SEC(ECC_P384))
  | (0x00z, 0x19z) -> Correct (SEC(ECC_P521))
  | (0x00z, x) -> let v = int_of_bytes (abyte x) in
		   (*if v > 0 && v < 17 then *) Correct(EC_UNSUPPORTED (x))
//		   else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Wrong ec named group")
  | (0x01z, 0x00z) -> Correct (FFDHE(FFDHE2048))
  | (0x01z, 0x01z) -> Correct (FFDHE(FFDHE3072))
  | (0x01z, 0x02z) -> Correct (FFDHE(FFDHE4096))
  | (0x01z, 0x03z) -> Correct (FFDHE(FFDHE6144))
  | (0x01z, 0x04z) -> Correct (FFDHE(FFDHE8192))
  | (0x01z, v)      -> if v = 0xFCz || v = 0xFDz || v = 0xFEz || v = 0xFFz
			then Correct (FFDHE_PRIVATE_USE v)
			else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Wrong ffdhe private use group")
  | (0xFEz, v)      -> Correct (ECDHE_PRIVATE_USE v)
  | _ -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Wrong named group")


private val namedGroupsBytes0: groups:list namedGroup -> Tot (b:bytes { length b = op_Multiply 2 (List.Tot.length groups)})
let rec namedGroupsBytes0 groups =
  match groups with
  | [] -> empty_bytes
  | g::gs -> namedGroupBytes g @| namedGroupsBytes0 gs

val namedGroupsBytes: groups:list namedGroup{List.Tot.length groups < 65536/2}-> Tot (b:bytes { length b = 2 + op_Multiply 2 (List.Tot.length groups)})
let namedGroupsBytes groups =
  let gs = namedGroupsBytes0 groups in
  lemma_repr_bytes_values (length gs);
  vlbytes 2 gs

//val parseNamedGroups: pinverse_t namedGroupsBytes
let parseNamedGroups (b:bytes) =
  let rec (aux: b:bytes -> list namedGroup -> Tot (result (list namedGroup)) (decreases (length b))) = fun b groups ->
    if length b > 0 then
      if length b >= 2 then
	let (ng, bytes) = split b 2 in
	match parseNamedGroup ng with
	| Correct(ng) -> aux bytes (ng::groups)
	| Error(z) -> Error(z)
      else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    else Correct(groups) in
  match vlparse 2 b with
  | Correct(b) -> aux b []
  | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse named groups")


(* TODO : precise configurationId type *)
type configurationId = b:bytes{not (equalBytes b empty_bytes) /\ length b < 65536}

val configurationIdBytes: configurationId -> Tot bytes
let configurationIdBytes cid =
  lemma_repr_bytes_values (length cid);
  vlbytes 2 cid

//val parseConfigurationId: pinverse_t configurationIdBytes
let parseConfigurationId b =
  vlparse 2 b

type uint32 = b:lbytes 4

val uint32Bytes: uint32 -> Tot (lbytes 4)
let uint32Bytes u = u

val parseUint32: pinverse_t uint32Bytes
let parseUint32 b =
  if length b = 4 then Correct(b)
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

type earlyDataType =
  | ClientAuthentication
  | EarlyData
  | ClientAuthenticationAndData

val earlyDataTypeBytes : earlyDataType -> Tot (lbytes 1)
let earlyDataTypeBytes edt =
  match edt with
  | ClientAuthentication          -> abyte 1z
  | EarlyData                     -> abyte 2z
  | ClientAuthenticationAndData   -> abyte 3z

val parseEarlyDataType: pinverse_t earlyDataTypeBytes
let parseEarlyDataType b =
    match cbyte b with
    | (1z) -> Correct (ClientAuthentication)
    | (2z) -> Correct (EarlyData)
    | (3z) -> Correct (ClientAuthenticationAndData)
    | _ -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse early data type")

// TODO : replace with more precise types when available
type configurationExtension =
  | UnknownConfigurationExtension:
      typ:lbytes 2 -> payload: bytes { repr_bytes (length payload) <= 2 } -> configurationExtension

val configurationExtensionBytes: ce:configurationExtension -> Tot bytes
let configurationExtensionBytes ce =
  match ce with
  | UnknownConfigurationExtension typ payload -> typ @| vlbytes 2 payload

val parseConfigurationExtension: pinverse_t configurationExtensionBytes
let parseConfigurationExtension b =
  if length b >= 4 then
  ( let (typ, payload) = split b 2 in
    match vlparse 2 payload with
    | Correct (payload) -> Correct (UnknownConfigurationExtension typ payload)
    | Error(z) -> Error(z))
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Too few bytes to parse a configuration extension")

val configurationExtensionsBytes: list configurationExtension -> Tot bytes
let configurationExtensionsBytes ce =
  let b = (List.Tot.fold_left (fun bytes x -> bytes @| configurationExtensionBytes x) empty_bytes ce) in
  admit(); //TODO
  vlbytes 2 b


val parseConfigurationExtensions: pinverse_t configurationExtensionsBytes
let parseConfigurationExtensions b =
  let rec (aux: b:bytes -> list configurationExtension -> Tot (result (list configurationExtension)) (decreases (length b))) =
    fun b exts ->
    if length b > 0 then
      if length b >= 4 then
	let typ, len, data = split2 b 2 2 in
	let len = int_of_bytes len in
	if length b >= 4 + len then
	  let ext, bytes = split b len in
	  match parseConfigurationExtension ext with
	  | Correct(ext') -> aux bytes (ext'::exts)
	  | Error(z) -> Error(z)
	else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse configuration extension length")
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Configuration extension length should be at least 4")
    else Correct(exts) in
  if length b >= 2 then
  match vlparse 2 b with
  | Correct (b) ->  aux b []
  | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse configuration extension")
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse configuration extension")


val sigHashAlgBytes: sigHashAlg -> Tot (lbytes 2)
let sigHashAlgBytes sha =
  let sign = sigAlgBytes (fst sha) in
  admit(); // FIXME
  let hash = hashAlgBytes (snd sha) in
  hash @| sign

val parseSigHashAlg: pinverse_t sigHashAlgBytes
let parseSigHashAlg b =
  if length b = 2 then
    let (hash, sign) = split b 1 in
    match parseSigAlg sign with
    | Correct(sign) ->
	(match parseHashAlg hash with
	| Correct(hash) -> Correct(sign, hash)
	| Error(z) -> Error(z))
    | Error(z) -> Error(z)
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Remaining unparsed bytes after signature hash algorithm")

val sigHashAlgsBytes: list sigHashAlg -> Tot bytes
let sigHashAlgsBytes algs =
  admit(); // TODO
  vlbytes 2 (List.Tot.fold_left (fun l x -> sigHashAlgBytes x @| l) empty_bytes algs)

val parseSigHashAlgs: pinverse_t sigHashAlgsBytes
let parseSigHashAlgs b =
  let rec (aux: b:bytes -> list sigHashAlg -> Tot (result (list sigHashAlg)) (decreases (length b))) = fun b algs ->
    if length b > 0 then
      if length b >= 2 then
      let (alg, bytes) = split b 2 in
      match parseSigHashAlg alg with
      | Correct(sha) -> aux bytes (sha::algs)
      | Error(z) -> Error(z)
      else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Too few bytes to parse sig hash algs")
    else Correct(algs) in
  match vlparse 2 b with
  | Correct (b) -> aux b []
  | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse sig hash algs")

// TODO : replace "bytes" by either DH or ECDH parameters
type keyShareEntry = namedGroup * b:bytes { repr_bytes (length b) <= 2 }

val keyShareEntryBytes: keyShareEntry -> Tot bytes
let keyShareEntryBytes (ng, bytes) =
  let ng_bytes = namedGroupBytes ng in
  ng_bytes @| vlbytes 2 bytes

val parseKeyShareEntry: pinverse_t keyShareEntryBytes
let parseKeyShareEntry b =
  if length b >= 2 then
    let ng, key_exchange = split b 2 in
    match parseNamedGroup ng with
    | Correct(ng) ->
	(match vlparse 2 key_exchange with
	| Correct(ke) -> Correct (ng, ke)
	| Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share entry"))
    | Error(z) -> Error(z)
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Too few bytes to parse key share entry")

val keyShareEntriesBytes: list keyShareEntry -> Tot bytes
let keyShareEntriesBytes kses =
  admit(); //TODO
  vlbytes 2 (List.Tot.fold_left (fun l s -> l @| keyShareEntryBytes s) empty_bytes kses)

val parseKeyShareEntries: pinverse_t keyShareEntriesBytes
let parseKeyShareEntries b =
  let rec (aux: b:bytes -> list keyShareEntry -> Tot (result (list keyShareEntry)) (decreases(length b))) = fun b entries ->
    if length b > 0 then
      if length b >= 4 then
	let (ng, data) = split b 2 in
	match vlsplit 2 data with
	| Correct(kex, bytes) ->
	    (match parseKeyShareEntry (ng @| vlbytes 2 kex) with
	    | Correct(entry) -> aux bytes (entry::entries)
	    | Error(z) -> Error(z))
	| Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share entry")
      else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Too few bytes to parse key share entries")
    else Correct(entries) in
  match vlparse 2 b with
  | Correct (b) ->  aux b []
  | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share entries")
  
type clientKeyShare = l:list keyShareEntry{List.Tot.length l >= 4 /\ List.Tot.length l < 65536}
type serverKeyShare = keyShareEntry

type keyShare =
  | ClientKeyShare of clientKeyShare
  | ServerKeyShare of serverKeyShare

val clientKeyShareBytes: clientKeyShare -> Tot bytes
let clientKeyShareBytes cks =
  keyShareEntriesBytes cks

//val parseClientKeyShare: pinverse_t clientKeyShareBytes
let parseClientKeyShare b = parseKeyShareEntries b

val serverKeyShareBytes: serverKeyShare -> Tot bytes
let serverKeyShareBytes sks = keyShareEntryBytes sks

val parseServerKeyShare: pinverse_t serverKeyShareBytes
let parseServerKeyShare b = parseKeyShareEntry b

val keyShareBytes: keyShare -> Tot bytes
let keyShareBytes = function
  | ClientKeyShare cks -> clientKeyShareBytes cks
  | ServerKeyShare sks -> serverKeyShareBytes sks

(* TODO: FIXME *)
let parseKeyShare is_client b =
  if is_client then 
    match parseClientKeyShare b with
    | Correct kse -> Correct (ClientKeyShare kse)
    | Error z -> Error z
  else
    match parseServerKeyShare b with
    | Correct ks -> Correct (ServerKeyShare ks)
    | Error z -> Error z

// TODO : give more precise type
type pskIdentity = b:bytes{length b < 65536}

val pskIdentityBytes: pskIdentity -> Tot bytes
let pskIdentityBytes pski =
  lemma_repr_bytes_values (length pski);
  vlbytes 2 (pski)

//val parsePskIdentity: pinverse_t pskIdentityBytes
let parsePskIdentity b = vlparse 2 b

val pskIdentitiesBytes: list pskIdentity -> Tot bytes
let pskIdentitiesBytes l =
  admit(); // TODO
  vlbytes 2 (List.Tot.fold_left (fun l s -> l @| pskIdentityBytes s) empty_bytes l)

val parsePskIdentities: pinverse_t pskIdentitiesBytes
let parsePskIdentities b =
  let rec (aux: b:bytes -> list pskIdentity -> Tot (result (list pskIdentity)) (decreases (length b))) = fun b ids ->
    if length b > 0 then
      if length b >= 2 then
	let len, data = split b 2 in
	let len = int_of_bytes len in
	if length b >= len then
	  let pski, bytes = split b len in
	  match parsePskIdentity pski with
	  | Correct(id) ->
              admit(); // TODO
              aux bytes (id::ids)
	  | Error(z) -> Error(z)
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse psk identity length")
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Expected psk identity to be at least 2 bytes long")
    else Correct(ids) in
  match vlparse 2 b with
  | Correct (b) -> aux b []
  | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse psk identities")

type clientPreSharedKey = l:list pskIdentity{List.Tot.length l >= 2 /\ List.Tot.length l < 65536 }
type serverPreSharedKey = pskIdentity
type preSharedKey =
  | ClientPreSharedKey of clientPreSharedKey
  | ServerPreSharedKey of serverPreSharedKey

val clientPreSharedKeyBytes: clientPreSharedKey -> Tot bytes
let clientPreSharedKeyBytes cpsk = pskIdentitiesBytes cpsk

//val parseClientPreSharedKey: pinverse_t clientPreSharedKeyBytes
let parseClientPreSharedKey b = parsePskIdentities b

val serverPreSharedKeyBytes: serverPreSharedKey -> Tot bytes
let serverPreSharedKeyBytes cpsk = pskIdentityBytes cpsk

//val parseServerPreSharedKey: pinverse_t serverPreSharedKeyBytes
let parseServerPreSharedKey b = parsePskIdentity b

val preSharedKeyBytes: preSharedKey -> Tot bytes
let preSharedKeyBytes = function
  | ClientPreSharedKey cpsk -> clientPreSharedKeyBytes cpsk
  | ServerPreSharedKey spsk -> serverPreSharedKeyBytes spsk

val parsePreSharedKey: pinverse_t preSharedKeyBytes
let parsePreSharedKey b =
  match vlparse 2 b with
  | Correct(b') ->
      (match vlparse 2 b with
      | Correct(b'') -> // Client case
	(match parseClientPreSharedKey b with
	| Correct(psks) -> admit(); //TODO
                          Correct(ClientPreSharedKey psks)
	| Error(z) -> Error(z))
      | Error(_) -> // Server case
	(match parseServerPreSharedKey b with
	| Correct(psk) -> Correct (ServerPreSharedKey psk)
	| Error(z) -> Error(z)))
  | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse pre shared key")
