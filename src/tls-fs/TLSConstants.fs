(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module TLSConstants

open Bytes
open Error
open TLSError
//open Seq

type kexAlg =
    | RSA 
    | DH_DSS
    | DH_RSA
    | DHE_DSS
    | DHE_RSA
    | ECDHE_RSA
    | ECDHE_ECDSA
    | DH_anon

type blockCipher =
    | TDES_EDE
    | AES_128
    | AES_256

type encAlg =
    | CBC_Stale of blockCipher
    | CBC_Fresh of blockCipher
    | Stream_RC4_128

type hashAlg =
    | NULL
    | MD5SHA1
    | MD5
    | SHA
    | SHA256
    | SHA384

type macAlg =
    | MA_HMAC of hashAlg
    | MA_SSLKHASH of hashAlg // MD5(SHA1(...))

type sigAlg = 
    | SA_RSA
    | SA_DSA 
    | SA_ECDSA

type sigHashAlg   = sigAlg * hashAlg

let sigAlgBytes sa =
    match sa with
    | SA_RSA   -> (abyte 1uy)
    | SA_DSA   -> (abyte 2uy)
    | SA_ECDSA -> (abyte 3uy)
let parseSigAlg b =
    match cbyte b with
    | (1uy) -> correct SA_RSA
    | (2uy) -> correct SA_DSA
    | (3uy) -> correct SA_ECDSA
    | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

let hashAlgBytes ha =
    match ha with
    | MD5     -> (abyte 1uy)
    | SHA     -> (abyte 2uy)
    | SHA256  -> (abyte 4uy)
    | SHA384  -> (abyte 5uy)
    | NULL    -> unexpected "[macAlgBytes] Cannot enode NULL hash alg."
    | MD5SHA1 -> unexpected "[macAlgBytes] Cannot enode MD5SHA1 hash alg."

let parseHashAlg b =
    match cbyte b with
    | (1uy) -> correct MD5   
    | (2uy) -> correct SHA   
    | (4uy) -> correct SHA256
    | (5uy) -> correct SHA384
    | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

type aeadAlg =
    | AES_128_GCM
    | AES_256_GCM

type aeAlg = //for specification
    | MACOnly of macAlg
    | MtE of encAlg * macAlg
    | AEAD of aeadAlg * macAlg // for the PRF

let encKeySize ciph =
    match ciph with
    | Stream_RC4_128       -> 16
    | CBC_Stale(TDES_EDE)  -> 24
    | CBC_Stale(AES_128)   -> 16
    | CBC_Stale(AES_256)   -> 32
    | CBC_Fresh(TDES_EDE)  -> 24
    | CBC_Fresh(AES_128)   -> 16
    | CBC_Fresh(AES_256)   -> 32

let blockSize ciph =
    match ciph with
    | TDES_EDE      -> 8
    | AES_128       -> 16
    | AES_256       -> 16

let aeadKeySize ciph =
    match ciph with
    | AES_128_GCM -> 16
    | AES_256_GCM -> 32

let aeadIVSize ciph =
    match ciph with
    | AES_128_GCM -> 4
    | AES_256_GCM -> 4

let aeadRecordIVSize ciph =
    match ciph with
    | AES_128_GCM -> 8
    | AES_256_GCM -> 8

let aeadTagSize ciph =
    match ciph with
    | AES_128_GCM -> 16
    | AES_256_GCM -> 16

let hashSize alg =
    match alg with
    | MD5     -> 16
    | SHA     -> 20
    | SHA256  -> 32
    | SHA384  -> 48
    | MD5SHA1 -> 16 + 20
    | NULL    -> Error.unexpected "[hashSize] Unknown hash size for NULL algorithm"

let macKeySize mac =
    match mac with
    | MA_HMAC(alg) | MA_SSLKHASH(alg) ->
        hashSize alg

let macSize mac =
    match mac with
    | MA_HMAC(alg) | MA_SSLKHASH(alg) ->
        hashSize alg

(* ------------------------------------------------------------------------ *)
(* Key parameters *)
type dsaparams = { p : bytes; q : bytes; g : bytes; }

type skeyparams =
| SK_RSA of bytes * bytes (* modulus x exponent *)
| SK_DSA of bytes * dsaparams

type pkeyparams =
| PK_RSA of bytes * bytes
| PK_DSA of bytes * dsaparams

let sigalg_of_skeyparams = function
| SK_RSA _ -> SA_RSA
| SK_DSA _ -> SA_DSA

let sigalg_of_pkeyparams = function
| PK_RSA _ -> SA_RSA
| PK_DSA _ -> SA_DSA

(* Cipher Suites *)

// For now we only support one SCSV, but there exist others.
type SCSVsuite =
    | TLS_EMPTY_RENEGOTIATION_INFO_SCSV

type cipherAlg = // used only in ciphersuite definition
    | RC4_128
    | TDES_EDE_CBC
    | AES_128_CBC
    | AES_256_CBC

type csAuthEncAlg =
    | CS_MtE of cipherAlg * hashAlg
    | CS_AEAD of aeadAlg * hashAlg

type cipherSuite =
    | NullCipherSuite
    | CipherSuite of kexAlg * csAuthEncAlg
    | OnlyMACCipherSuite of kexAlg * hashAlg
    | SCSV of SCSVsuite

type cipherSuites = list<cipherSuite>

type PreCompression =
    | NullCompression
type Compression = PreCompression

let parseCompression b =
    match cbyte b with
    | 0uy -> correct(NullCompression)
    | _       -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

// Ignore compression methods we don't understand. This is a departure
// from usual parsing, where we fail on unknown values, but that's how TLS
// handles compression method lists.
let rec parseCompressions b =
    let l = length b in
    if l > 0 
    then
        let (cmB,b) = split b 1 in
        match parseCompression cmB with
        | Error(z) -> // skip this one
            parseCompressions b
        | Correct(cm) -> cm :: parseCompressions b
    else []

let compressionBytes (comp:Compression) = 
    match comp with
    | NullCompression -> abyte 0uy

let rec compressionMethodsBytes cs =
   match cs with
   | c::cs -> compressionBytes c @| compressionMethodsBytes cs
   | []    -> empty_bytes 

type PreProtocolVersion =
    | SSL_3p0
    | TLS_1p0
    | TLS_1p1
    | TLS_1p2
type ProtocolVersion = PreProtocolVersion

let versionBytes pv =
    match pv with
    | SSL_3p0 -> abyte2 ( 3uy, 0uy)
    | TLS_1p0 -> abyte2 ( 3uy, 1uy)
    | TLS_1p1 -> abyte2 ( 3uy, 2uy )
    | TLS_1p2 -> abyte2 ( 3uy, 3uy )

let parseVersion (v:bytes) =
    match cbyte2 v with
    | ( 3uy, 0uy ) -> correct(SSL_3p0)
    | ( 3uy, 1uy ) -> correct(TLS_1p0)
    | ( 3uy, 2uy ) -> correct(TLS_1p1)
    | ( 3uy, 3uy ) -> correct(TLS_1p2)
    | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

let minPV (a:ProtocolVersion) (b:ProtocolVersion) =
  match (a,b) with
  | SSL_3p0, _ | _, SSL_3p0 -> SSL_3p0
  | TLS_1p0, _ | _, TLS_1p0 -> TLS_1p0
  | TLS_1p1, _ | _, TLS_1p1 -> TLS_1p1
  | _, _                    -> TLS_1p2
  // in F#, could use if a < b then a else b

let somePV (a:ProtocolVersion) = Some a

let geqPV (a:ProtocolVersion) (b:ProtocolVersion) =
    match (a,b) with
    | _,SSL_3p0 -> true
    | SSL_3p0,_ -> false
    | _,TLS_1p0 -> true
    | TLS_1p0,_ -> false
    | _,TLS_1p1 -> true
    | TLS_1p1,_ -> false
    | _,_       -> true

let nullCipherSuite = NullCipherSuite

let isNullCipherSuite cs =
    cs = NullCipherSuite

let cipherSuiteBytes cs =
    match cs with
    | NullCipherSuite                                     -> abyte2 ( 0x00uy, 0x00uy )
                                                      
    | OnlyMACCipherSuite (RSA, MD5)                       -> abyte2 ( 0x00uy, 0x01uy )
    | OnlyMACCipherSuite (RSA, SHA)                       -> abyte2 ( 0x00uy, 0x02uy )
    | OnlyMACCipherSuite (RSA, SHA256)                    -> abyte2 ( 0x00uy, 0x3Buy )
    | CipherSuite (RSA, CS_MtE (RC4_128, MD5))            -> abyte2 ( 0x00uy, 0x04uy )
    | CipherSuite (RSA, CS_MtE (RC4_128, SHA))            -> abyte2 ( 0x00uy, 0x05uy )
    | CipherSuite (RSA, CS_MtE (TDES_EDE_CBC, SHA))       -> abyte2 ( 0x00uy, 0x0Auy )
    | CipherSuite (RSA, CS_MtE (AES_128_CBC, SHA))        -> abyte2 ( 0x00uy, 0x2Fuy )
    | CipherSuite (RSA, CS_MtE (AES_256_CBC, SHA))        -> abyte2 ( 0x00uy, 0x35uy )
    | CipherSuite (RSA, CS_MtE (AES_128_CBC, SHA256))     -> abyte2 ( 0x00uy, 0x3Cuy )
    | CipherSuite (RSA, CS_MtE (AES_256_CBC, SHA256))     -> abyte2 ( 0x00uy, 0x3Duy )

    | CipherSuite (DH_DSS,  CS_MtE (TDES_EDE_CBC, SHA))   -> abyte2 ( 0x00uy, 0x0Duy )
    | CipherSuite (DH_RSA,  CS_MtE (TDES_EDE_CBC, SHA))   -> abyte2 ( 0x00uy, 0x10uy )
    | CipherSuite (DHE_DSS, CS_MtE (TDES_EDE_CBC, SHA))   -> abyte2 ( 0x00uy, 0x13uy )
    | CipherSuite (DHE_RSA, CS_MtE (TDES_EDE_CBC, SHA))   -> abyte2 ( 0x00uy, 0x16uy )
    | CipherSuite (DH_DSS,  CS_MtE (AES_128_CBC, SHA))    -> abyte2 ( 0x00uy, 0x30uy )
    | CipherSuite (DH_RSA,  CS_MtE (AES_128_CBC, SHA))    -> abyte2 ( 0x00uy, 0x31uy )
    | CipherSuite (DHE_DSS, CS_MtE (AES_128_CBC, SHA))    -> abyte2 ( 0x00uy, 0x32uy )
    | CipherSuite (DHE_RSA, CS_MtE (AES_128_CBC, SHA))    -> abyte2 ( 0x00uy, 0x33uy )
    | CipherSuite (DH_DSS,  CS_MtE (AES_256_CBC, SHA))    -> abyte2 ( 0x00uy, 0x36uy )
    | CipherSuite (DH_RSA,  CS_MtE (AES_256_CBC, SHA))    -> abyte2 ( 0x00uy, 0x37uy )
    | CipherSuite (DHE_DSS, CS_MtE (AES_256_CBC, SHA))    -> abyte2 ( 0x00uy, 0x38uy )
    | CipherSuite (DHE_RSA, CS_MtE (AES_256_CBC, SHA))    -> abyte2 ( 0x00uy, 0x39uy )
    | CipherSuite (DH_DSS,  CS_MtE (AES_128_CBC, SHA256)) -> abyte2 ( 0x00uy, 0x3Euy )
    | CipherSuite (DH_RSA,  CS_MtE (AES_128_CBC, SHA256)) -> abyte2 ( 0x00uy, 0x3Fuy )
    | CipherSuite (DHE_DSS, CS_MtE (AES_128_CBC, SHA256)) -> abyte2 ( 0x00uy, 0x40uy )
    | CipherSuite (DHE_RSA, CS_MtE (AES_128_CBC, SHA256)) -> abyte2 ( 0x00uy, 0x67uy )
    | CipherSuite (DH_DSS,  CS_MtE (AES_256_CBC, SHA256)) -> abyte2 ( 0x00uy, 0x68uy )
    | CipherSuite (DH_RSA,  CS_MtE (AES_256_CBC, SHA256)) -> abyte2 ( 0x00uy, 0x69uy )
    | CipherSuite (DHE_DSS, CS_MtE (AES_256_CBC, SHA256)) -> abyte2 ( 0x00uy, 0x6Auy )
    | CipherSuite (DHE_RSA, CS_MtE (AES_256_CBC, SHA256)) -> abyte2 ( 0x00uy, 0x6Buy )

    | CipherSuite (ECDHE_RSA, CS_MtE (RC4_128, SHA))      -> abyte2 ( 0xc0uy, 0x11uy )
    | CipherSuite (ECDHE_RSA, CS_MtE (TDES_EDE_CBC, SHA)) -> abyte2 ( 0xc0uy, 0x12uy )
    | CipherSuite (ECDHE_RSA, CS_MtE (AES_128_CBC, SHA))  -> abyte2 ( 0xc0uy, 0x13uy )
    | CipherSuite (ECDHE_RSA, CS_MtE (AES_128_CBC, SHA256)) -> abyte2 ( 0xc0uy, 0x27uy )
    | CipherSuite (ECDHE_RSA, CS_MtE (AES_256_CBC, SHA))  -> abyte2 ( 0xc0uy, 0x14uy )
    | CipherSuite (ECDHE_RSA, CS_MtE (AES_256_CBC, SHA384)) -> abyte2 ( 0xc0uy, 0x28uy )

    | CipherSuite (ECDHE_RSA, CS_AEAD(AES_128_GCM, SHA256)) -> abyte2 ( 0xc0uy, 0x2fuy )
    | CipherSuite (ECDHE_RSA, CS_AEAD(AES_256_GCM, SHA384)) -> abyte2 ( 0xc0uy, 0x30uy )

    | CipherSuite (DH_anon, CS_MtE (RC4_128, MD5))        -> abyte2 ( 0x00uy, 0x18uy )
    | CipherSuite (DH_anon, CS_MtE (TDES_EDE_CBC, SHA))   -> abyte2 ( 0x00uy, 0x1Buy )
    | CipherSuite (DH_anon, CS_MtE (AES_128_CBC, SHA))    -> abyte2 ( 0x00uy, 0x34uy )
    | CipherSuite (DH_anon, CS_MtE (AES_256_CBC, SHA))    -> abyte2 ( 0x00uy, 0x3Auy )
    | CipherSuite (DH_anon, CS_MtE (AES_128_CBC, SHA256)) -> abyte2 ( 0x00uy, 0x6Cuy )
    | CipherSuite (DH_anon, CS_MtE (AES_256_CBC, SHA256)) -> abyte2 ( 0x00uy, 0x6Duy )

    | CipherSuite (RSA,     CS_AEAD(AES_128_GCM, SHA256)) -> abyte2( 0x00uy, 0x9Cuy )
    | CipherSuite (RSA,     CS_AEAD(AES_256_GCM, SHA384)) -> abyte2( 0x00uy, 0x9Duy )
    | CipherSuite (DHE_RSA, CS_AEAD(AES_128_GCM, SHA256)) -> abyte2( 0x00uy, 0x9Euy )
    | CipherSuite (DHE_RSA, CS_AEAD(AES_256_GCM, SHA384)) -> abyte2( 0x00uy, 0x9Fuy )
    | CipherSuite (DH_RSA,  CS_AEAD(AES_128_GCM, SHA256)) -> abyte2( 0x00uy, 0xA0uy )
    | CipherSuite (DH_RSA,  CS_AEAD(AES_256_GCM, SHA384)) -> abyte2( 0x00uy, 0xA1uy )
    | CipherSuite (DHE_DSS, CS_AEAD(AES_128_GCM, SHA256)) -> abyte2( 0x00uy, 0xA2uy )
    | CipherSuite (DHE_DSS, CS_AEAD(AES_256_GCM, SHA384)) -> abyte2( 0x00uy, 0xA3uy )
    | CipherSuite (DH_DSS,  CS_AEAD(AES_128_GCM, SHA256)) -> abyte2( 0x00uy, 0xA4uy )
    | CipherSuite (DH_DSS,  CS_AEAD(AES_256_GCM, SHA384)) -> abyte2( 0x00uy, 0xA5uy )
    | CipherSuite (DH_anon, CS_AEAD(AES_128_GCM, SHA256)) -> abyte2( 0x00uy, 0xA6uy )
    | CipherSuite (DH_anon, CS_AEAD(AES_256_GCM, SHA384)) -> abyte2( 0x00uy, 0xA7uy )

    | SCSV (TLS_EMPTY_RENEGOTIATION_INFO_SCSV)            -> abyte2 ( 0x00uy, 0xFFuy )

(* KB: Must define known cipher suites as a predicate before typechecking the following: *)
    | _ -> unexpected "[cipherSuiteBytes] invoked on an unknown ciphersuite"

let parseCipherSuite b = 
    match cbyte2 b with
    | ( 0x00uy, 0x00uy ) -> correct(NullCipherSuite)
   
    | ( 0x00uy, 0x01uy ) -> correct(OnlyMACCipherSuite (RSA, MD5))
    | ( 0x00uy, 0x02uy ) -> correct(OnlyMACCipherSuite (RSA, SHA))
    | ( 0x00uy, 0x3Buy ) -> correct(OnlyMACCipherSuite (RSA, SHA256))

    | ( 0x00uy, 0x04uy ) -> correct(CipherSuite (    RSA, CS_MtE (     RC4_128, MD5)))
    | ( 0x00uy, 0x05uy ) -> correct(CipherSuite (    RSA, CS_MtE (     RC4_128, SHA)))
    | ( 0x00uy, 0x0Auy ) -> correct(CipherSuite (    RSA, CS_MtE (TDES_EDE_CBC, SHA)))
    | ( 0x00uy, 0x2Fuy ) -> correct(CipherSuite (    RSA, CS_MtE ( AES_128_CBC, SHA)))
    | ( 0x00uy, 0x35uy ) -> correct(CipherSuite (    RSA, CS_MtE ( AES_256_CBC, SHA)))
    | ( 0x00uy, 0x3Cuy ) -> correct(CipherSuite (    RSA, CS_MtE ( AES_128_CBC, SHA256)))
    | ( 0x00uy, 0x3Duy ) -> correct(CipherSuite (    RSA, CS_MtE ( AES_256_CBC, SHA256)))

    | ( 0x00uy, 0x0Duy ) -> correct(CipherSuite ( DH_DSS, CS_MtE (TDES_EDE_CBC, SHA)))
    | ( 0x00uy, 0x10uy ) -> correct(CipherSuite ( DH_RSA, CS_MtE (TDES_EDE_CBC, SHA)))
    | ( 0x00uy, 0x13uy ) -> correct(CipherSuite (DHE_DSS, CS_MtE (TDES_EDE_CBC, SHA)))
    | ( 0x00uy, 0x16uy ) -> correct(CipherSuite (DHE_RSA, CS_MtE (TDES_EDE_CBC, SHA)))

    | ( 0x00uy, 0x30uy ) -> correct(CipherSuite ( DH_DSS, CS_MtE ( AES_128_CBC, SHA)))
    | ( 0x00uy, 0x31uy ) -> correct(CipherSuite ( DH_RSA, CS_MtE ( AES_128_CBC, SHA)))
    | ( 0x00uy, 0x32uy ) -> correct(CipherSuite (DHE_DSS, CS_MtE ( AES_128_CBC, SHA)))
    | ( 0x00uy, 0x33uy ) -> correct(CipherSuite (DHE_RSA, CS_MtE ( AES_128_CBC, SHA)))

    | ( 0x00uy, 0x36uy ) -> correct(CipherSuite ( DH_DSS, CS_MtE ( AES_256_CBC, SHA)))
    | ( 0x00uy, 0x37uy ) -> correct(CipherSuite ( DH_RSA, CS_MtE ( AES_256_CBC, SHA)))
    | ( 0x00uy, 0x38uy ) -> correct(CipherSuite (DHE_DSS, CS_MtE ( AES_256_CBC, SHA)))
    | ( 0x00uy, 0x39uy ) -> correct(CipherSuite (DHE_RSA, CS_MtE ( AES_256_CBC, SHA)))

    | ( 0x00uy, 0x3Euy ) -> correct(CipherSuite ( DH_DSS, CS_MtE ( AES_128_CBC, SHA256)))
    | ( 0x00uy, 0x3Fuy ) -> correct(CipherSuite ( DH_RSA, CS_MtE ( AES_128_CBC, SHA256)))
    | ( 0x00uy, 0x40uy ) -> correct(CipherSuite (DHE_DSS, CS_MtE ( AES_128_CBC, SHA256)))
    | ( 0x00uy, 0x67uy ) -> correct(CipherSuite (DHE_RSA, CS_MtE ( AES_128_CBC, SHA256)))

    | ( 0x00uy, 0x68uy ) -> correct(CipherSuite ( DH_DSS, CS_MtE ( AES_256_CBC, SHA256)))
    | ( 0x00uy, 0x69uy ) -> correct(CipherSuite ( DH_RSA, CS_MtE ( AES_256_CBC, SHA256)))
    | ( 0x00uy, 0x6Auy ) -> correct(CipherSuite (DHE_DSS, CS_MtE ( AES_256_CBC, SHA256)))
    | ( 0x00uy, 0x6Buy ) -> correct(CipherSuite (DHE_RSA, CS_MtE ( AES_256_CBC, SHA256)))

    | ( 0x00uy, 0x18uy ) -> correct(CipherSuite (DH_anon, CS_MtE (     RC4_128, MD5)))
    | ( 0x00uy, 0x1Buy ) -> correct(CipherSuite (DH_anon, CS_MtE (TDES_EDE_CBC, SHA)))
    | ( 0x00uy, 0x34uy ) -> correct(CipherSuite (DH_anon, CS_MtE ( AES_128_CBC, SHA)))
    | ( 0x00uy, 0x3Auy ) -> correct(CipherSuite (DH_anon, CS_MtE ( AES_256_CBC, SHA)))
    | ( 0x00uy, 0x6Cuy ) -> correct(CipherSuite (DH_anon, CS_MtE ( AES_128_CBC, SHA256)))
    | ( 0x00uy, 0x6Duy ) -> correct(CipherSuite (DH_anon, CS_MtE ( AES_256_CBC, SHA256)))

    | ( 0x00uy, 0x9Cuy ) -> correct(CipherSuite (RSA,     CS_AEAD(AES_128_GCM, SHA256)))
    | ( 0x00uy, 0x9Duy ) -> correct(CipherSuite (RSA,     CS_AEAD(AES_256_GCM, SHA384)))
    | ( 0x00uy, 0x9Euy ) -> correct(CipherSuite (DHE_RSA, CS_AEAD(AES_128_GCM, SHA256)))
    | ( 0x00uy, 0x9Fuy ) -> correct(CipherSuite (DHE_RSA, CS_AEAD(AES_256_GCM, SHA384)))
    | ( 0x00uy, 0xA0uy ) -> correct(CipherSuite (DH_RSA,  CS_AEAD(AES_128_GCM, SHA256)))
    | ( 0x00uy, 0xA1uy ) -> correct(CipherSuite (DH_RSA,  CS_AEAD(AES_256_GCM, SHA384)))
    | ( 0x00uy, 0xA2uy ) -> correct(CipherSuite (DHE_DSS, CS_AEAD(AES_128_GCM, SHA256)))
    | ( 0x00uy, 0xA3uy ) -> correct(CipherSuite (DHE_DSS, CS_AEAD(AES_256_GCM, SHA384)))
    | ( 0x00uy, 0xA4uy ) -> correct(CipherSuite (DH_DSS,  CS_AEAD(AES_128_GCM, SHA256)))
    | ( 0x00uy, 0xA5uy ) -> correct(CipherSuite (DH_DSS,  CS_AEAD(AES_256_GCM, SHA384)))
    | ( 0x00uy, 0xA6uy ) -> correct(CipherSuite (DH_anon, CS_AEAD(AES_128_GCM, SHA256)))
    | ( 0x00uy, 0xA7uy ) -> correct(CipherSuite (DH_anon, CS_AEAD(AES_256_GCM, SHA384)))

    | ( 0xc0uy, 0x11uy ) -> correct(CipherSuite (ECDHE_RSA, CS_MtE (RC4_128, SHA)))
    | ( 0xc0uy, 0x12uy ) -> correct(CipherSuite (ECDHE_RSA, CS_MtE (TDES_EDE_CBC, SHA)))
    | ( 0xc0uy, 0x13uy ) -> correct(CipherSuite (ECDHE_RSA, CS_MtE (AES_128_CBC, SHA)))
    | ( 0xc0uy, 0x14uy ) -> correct(CipherSuite (ECDHE_RSA, CS_MtE (AES_256_CBC, SHA)))
    | ( 0xc0uy, 0x27uy ) -> correct(CipherSuite (ECDHE_RSA, CS_MtE (AES_128_CBC, SHA256)))
    | ( 0xc0uy, 0x28uy ) -> correct(CipherSuite (ECDHE_RSA, CS_MtE (AES_256_CBC, SHA384)))

    | ( 0xc0uy, 0x2fuy ) -> correct(CipherSuite (ECDHE_RSA, CS_AEAD(AES_128_GCM, SHA256)))
    | ( 0xc0uy, 0x30uy ) -> correct(CipherSuite (ECDHE_RSA, CS_AEAD(AES_256_GCM, SHA384)))

    | ( 0x00uy, 0xFFuy ) -> correct(SCSV (TLS_EMPTY_RENEGOTIATION_INFO_SCSV))

    | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")


let consCipherSuites (cs:cipherSuite) (css:cipherSuites) = cs::css

// called by the server handshake;     
// ciphersuites that we do not understand are parsed,
// but not added to the list, and thus will be ignored by the server
let rec parseCipherSuites b:Result<cipherSuites> =
    if length b > 1 then
        let (b0,b1) = split b 2 in
        match parseCipherSuites b1 with 
        | Correct(css) ->
            (match parseCipherSuite b0 with
            | Error(z) -> // ignore this cs
                correct(css)
            | Correct(cs) -> let ncss = consCipherSuites cs css  in correct(ncss))
        | Error(z) -> Error(z) 
    else if length b = 0 then Correct([])
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

let rec cipherSuitesBytes css =
    match css with 
    | [] -> empty_bytes 
    | cs::css -> cipherSuiteBytes cs @| 
                 cipherSuitesBytes css
    
(*CF we could use sub instead, with proper refinements:
let rec cipherSuites_of_bytes2 i b =
    if i <= Length(b) + 2 then 
        cipherSuite_of_bytes (sub b i 2) :: cipherSuites_of_bytes2 (i+2) b 
    else if i = Length(b) then 
        []
    else
        Error // the cipherSuite had an odd length!
*)


let isAnonCipherSuite cs =
    match cs with
    | CipherSuite ( DH_anon, _ )   -> true
 (* | ( ECDH_anon, _ ) -> true *)
    | _ -> false

let isDHECipherSuite cs =
    match cs with
    | CipherSuite ( DHE_DSS, _ )     -> true
    | CipherSuite ( DHE_RSA, _ )     -> true
    | CipherSuite ( ECDHE_ECDSA, _ ) -> true
    | CipherSuite ( ECDHE_RSA, _ )   -> true
    | _ -> false

let isECDHECipherSuite cs =
    match cs with
    | CipherSuite ( ECDHE_ECDSA, _ ) -> true
    | CipherSuite ( ECDHE_RSA, _ )   -> true
    | _ -> false

let isDHCipherSuite cs =
    match cs with
    | CipherSuite (DH_DSS, _ ) -> true
    | CipherSuite (DH_RSA, _ ) -> true
    | _ -> false

let isRSACipherSuite cs =
    match cs with
    | CipherSuite ( RSA, _ )     -> true
    | OnlyMACCipherSuite ( RSA, _ ) -> true
    | _ -> false

let isOnlyMACCipherSuite cs =
    match cs with
    | OnlyMACCipherSuite (_,_) -> true
    | _ -> false

let sigAlg_of_ciphersuite cs =
    match cs with
    | CipherSuite ( RSA, _ ) | OnlyMACCipherSuite( RSA, _ ) | CipherSuite(ECDHE_RSA,_)
    | CipherSuite( DHE_RSA, _) | CipherSuite(DH_RSA,_) -> SA_RSA
    | CipherSuite( DHE_DSS, _) | CipherSuite(DH_DSS,_) -> SA_DSA
    | CipherSuite( ECDHE_ECDSA, _) -> SA_ECDSA
    | _ -> unexpected "[sigAlg_of_ciphersuite] invoked on a worng ciphersuite"

let contains_TLS_EMPTY_RENEGOTIATION_INFO_SCSV (css: list<cipherSuite>) =
    List.memr css (SCSV (TLS_EMPTY_RENEGOTIATION_INFO_SCSV)) 

type prflabel = bytes
let extract_label = utf8 "master secret"
let extended_extract_label = utf8 "extended master secret"
let kdf_label     = utf8 "key expansion" 

type prePrfAlg =
  | PRF_SSL3_nested         // MD5(SHA1(...)) for extraction and keygen
  | PRF_SSL3_concat         // MD5 @| SHA1    for VerifyData tags
  | PRF_TLS_1p01 of prflabel          // MD5 xor SHA1
  | PRF_TLS_1p2 of prflabel * macAlg  // typically SHA256 but may depend on CS


type kefAlg = prePrfAlg
type kdfAlg = prePrfAlg
type vdAlg = ProtocolVersion * cipherSuite

let verifyDataLen_of_ciphersuite (cs:cipherSuite) =
    (* Only to be invoked with TLS 1.2 (hardcoded in previous versions *)
    match cs with
    | _ -> 12

let prfMacAlg_of_ciphersuite (cs:cipherSuite) =
    (* Only to be invoked with TLS 1.2 (hardcoded in previous versions *)
    match cs with
   // | CipherSuite ( ECDH*, MtE (_,SHA384)) -> SHA384
    | CipherSuite ( _ , CS_MtE ( _ , _ )) -> MA_HMAC(SHA256)
    | CipherSuite ( _ , CS_AEAD ( _ , hAlg ))   -> MA_HMAC(hAlg)
    | OnlyMACCipherSuite (_, hAlg) -> MA_HMAC(SHA256) //MK should this be MA_HMAC(hAlg)?
    | NullCipherSuite         -> unexpected "[prfHashAlg_of_ciphersuite] invoked on an invalid ciphersuite" 
    | SCSV (_)                -> unexpected "[prfHashAlg_of_ciphersuite] invoked on an invalid ciphersuite" 

// PRF and verifyData hash algorithms are potentially independent in TLS 1.2,
// so we use two distinct functions. However, all currently defined ciphersuites
// use the same hash algorithm, so the current implementation of the two functions
// is the same.
let verifyDataHashAlg_of_ciphersuite (cs:cipherSuite) =
    (* Only to be invoked with TLS 1.2 (hardcoded in previous versions *)
    match cs with
   // | CipherSuite ( ECDH*, MtE (_,SHA384)) -> SHA384
    | CipherSuite ( _ , CS_MtE ( _ , _ ))     -> SHA256
    | CipherSuite ( _ , CS_AEAD ( _ , hAlg )) -> hAlg
    | OnlyMACCipherSuite (_, hAlg)         -> SHA256
    | NullCipherSuite -> unexpected "[verifyDataHashAlg_of_ciphersuite] invoked on an invalid ciphersuite"
    | SCSV (_)        -> unexpected "[verifyDataHashAlg_of_ciphersuite] invoked on an invalid ciphersuite"

let sessionHashAlg pv cs =
    match pv with
    | SSL_3p0 | TLS_1p0 | TLS_1p1 -> MD5SHA1
    | TLS_1p2 -> verifyDataHashAlg_of_ciphersuite cs

let tlsMacAlg alg pv = 
    match pv with
    | SSL_3p0 -> MA_SSLKHASH(alg)
    | TLS_1p0 | TLS_1p1 | TLS_1p2 -> MA_HMAC(alg)
        
let tlsEncAlg alg pv = 
    match pv with
    | SSL_3p0 | TLS_1p0 ->
       (match alg with
          | RC4_128 -> Stream_RC4_128
          | TDES_EDE_CBC -> CBC_Stale(TDES_EDE)
          | AES_128_CBC -> CBC_Stale(AES_128)
          | AES_256_CBC -> CBC_Stale(AES_256))
    | TLS_1p1 | TLS_1p2 ->
       (match alg with
          | RC4_128 -> Stream_RC4_128
          | TDES_EDE_CBC -> CBC_Fresh(TDES_EDE)
          | AES_128_CBC -> CBC_Fresh(AES_128)
          | AES_256_CBC -> CBC_Fresh(AES_256))


let mk_aeAlg cs pv =
    match cs with
    | OnlyMACCipherSuite (_,alg) ->
        let mac = tlsMacAlg alg pv in
        MACOnly mac
    | CipherSuite(_, CS_MtE(e,a)) ->
        let enc = tlsEncAlg e pv in
        let mac = tlsMacAlg a pv in
        MtE (enc,mac)
    | CipherSuite(_, CS_AEAD(e,a)) ->
        let mac = tlsMacAlg a pv in
        AEAD(e,mac)
    | _ -> unexpected "[mk_aeAlg] invoked on an invalid ciphersuite"


let encAlg_of_aeAlg ae =
    match ae with
    | MtE(e,m) -> e 
    | _ -> unexpected "[encAlg_of_ciphersuite] inovked on an invalid ciphersuite"

let macAlg_of_aeAlg ae =
    match ae with
    | MACOnly(alg) -> alg
    | MtE(_,alg) -> alg
    | _ -> unexpected "[macAlg_of_ciphersuite] invoked on an invalid ciphersuite"

let encAlg_of_ciphersuite cs pv = 
    let a = mk_aeAlg cs pv in
    encAlg_of_aeAlg a 
let macAlg_of_ciphersuite cs pv = 
    let a = mk_aeAlg cs pv in
    macAlg_of_aeAlg a

let mkIntTriple x:(int*int*int) = x


(* Not for verification, just to run the implementation. See TLSInfo.fs *)
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

let cipherSuite_of_name (name:cipherSuiteName) =
    match name with
    | TLS_NULL_WITH_NULL_NULL                -> NullCipherSuite

    | TLS_RSA_WITH_NULL_MD5                  -> OnlyMACCipherSuite (RSA, MD5)
    | TLS_RSA_WITH_NULL_SHA                  -> OnlyMACCipherSuite (RSA, SHA)
    | TLS_RSA_WITH_NULL_SHA256               -> OnlyMACCipherSuite (RSA, SHA256)
    | TLS_RSA_WITH_RC4_128_MD5               -> CipherSuite (RSA, CS_MtE (RC4_128, MD5))
    | TLS_RSA_WITH_RC4_128_SHA               -> CipherSuite (RSA, CS_MtE (RC4_128, SHA))
    | TLS_RSA_WITH_3DES_EDE_CBC_SHA          -> CipherSuite (RSA, CS_MtE (TDES_EDE_CBC, SHA))
    | TLS_RSA_WITH_AES_128_CBC_SHA           -> CipherSuite (RSA, CS_MtE (AES_128_CBC, SHA))
    | TLS_RSA_WITH_AES_256_CBC_SHA           -> CipherSuite (RSA, CS_MtE (AES_256_CBC, SHA))
    | TLS_RSA_WITH_AES_128_CBC_SHA256        -> CipherSuite (RSA, CS_MtE (AES_128_CBC, SHA256))
    | TLS_RSA_WITH_AES_256_CBC_SHA256        -> CipherSuite (RSA, CS_MtE (AES_256_CBC, SHA256))
       
    | TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA      -> CipherSuite (DHE_DSS, CS_MtE (TDES_EDE_CBC, SHA))
    | TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA      -> CipherSuite (DHE_RSA, CS_MtE (TDES_EDE_CBC, SHA))
    | TLS_DHE_DSS_WITH_AES_128_CBC_SHA       -> CipherSuite (DHE_DSS, CS_MtE (AES_128_CBC, SHA))
    | TLS_DHE_RSA_WITH_AES_128_CBC_SHA       -> CipherSuite (DHE_RSA, CS_MtE (AES_128_CBC, SHA))
    | TLS_DHE_DSS_WITH_AES_256_CBC_SHA       -> CipherSuite (DHE_DSS, CS_MtE (AES_256_CBC, SHA))
    | TLS_DHE_RSA_WITH_AES_256_CBC_SHA       -> CipherSuite (DHE_RSA, CS_MtE (AES_256_CBC, SHA))
    | TLS_DHE_DSS_WITH_AES_128_CBC_SHA256    -> CipherSuite (DHE_DSS, CS_MtE (AES_128_CBC, SHA256))
    | TLS_DHE_RSA_WITH_AES_128_CBC_SHA256    -> CipherSuite (DHE_RSA, CS_MtE (AES_128_CBC, SHA256))
    | TLS_DHE_DSS_WITH_AES_256_CBC_SHA256    -> CipherSuite (DHE_DSS, CS_MtE (AES_256_CBC, SHA256))
    | TLS_DHE_RSA_WITH_AES_256_CBC_SHA256    -> CipherSuite (DHE_RSA, CS_MtE (AES_256_CBC, SHA256))

    | TLS_ECDHE_RSA_WITH_RC4_128_SHA         -> CipherSuite (ECDHE_RSA, CS_MtE (RC4_128, SHA))
    | TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA    -> CipherSuite (ECDHE_RSA, CS_MtE (TDES_EDE_CBC, SHA))
    | TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA     -> CipherSuite (ECDHE_RSA, CS_MtE (AES_128_CBC, SHA))
    | TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256  -> CipherSuite (ECDHE_RSA, CS_MtE (AES_128_CBC, SHA256))
    | TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA     -> CipherSuite (ECDHE_RSA, CS_MtE (AES_256_CBC, SHA))
    | TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384  -> CipherSuite (ECDHE_RSA, CS_MtE (AES_256_CBC, SHA384))

    | TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256  -> CipherSuite (ECDHE_RSA, CS_AEAD(AES_128_GCM, SHA256))
    | TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384  -> CipherSuite (ECDHE_RSA, CS_AEAD(AES_256_GCM, SHA384))

    | TLS_DH_anon_WITH_RC4_128_MD5           -> CipherSuite (DH_anon, CS_MtE (RC4_128, MD5))
    | TLS_DH_anon_WITH_3DES_EDE_CBC_SHA      -> CipherSuite (DH_anon, CS_MtE (TDES_EDE_CBC, SHA))
    | TLS_DH_anon_WITH_AES_128_CBC_SHA       -> CipherSuite (DH_anon, CS_MtE (AES_128_CBC, SHA))
    | TLS_DH_anon_WITH_AES_256_CBC_SHA       -> CipherSuite (DH_anon, CS_MtE (AES_256_CBC, SHA))
    | TLS_DH_anon_WITH_AES_128_CBC_SHA256    -> CipherSuite (DH_anon, CS_MtE (AES_128_CBC, SHA256))
    | TLS_DH_anon_WITH_AES_256_CBC_SHA256    -> CipherSuite (DH_anon, CS_MtE (AES_256_CBC, SHA256))

    | TLS_RSA_WITH_AES_128_GCM_SHA256        -> CipherSuite (RSA,     CS_AEAD(AES_128_GCM, SHA256))
    | TLS_RSA_WITH_AES_256_GCM_SHA384        -> CipherSuite (RSA,     CS_AEAD(AES_256_GCM, SHA384))
    | TLS_DHE_RSA_WITH_AES_128_GCM_SHA256    -> CipherSuite (DHE_RSA, CS_AEAD(AES_128_GCM, SHA256))
    | TLS_DHE_RSA_WITH_AES_256_GCM_SHA384    -> CipherSuite (DHE_RSA, CS_AEAD(AES_256_GCM, SHA384))
    | TLS_DH_RSA_WITH_AES_128_GCM_SHA256     -> CipherSuite (DH_RSA,  CS_AEAD(AES_128_GCM, SHA256))
    | TLS_DH_RSA_WITH_AES_256_GCM_SHA384     -> CipherSuite (DH_RSA,  CS_AEAD(AES_256_GCM, SHA384))
    | TLS_DHE_DSS_WITH_AES_128_GCM_SHA256    -> CipherSuite (DHE_DSS, CS_AEAD(AES_128_GCM, SHA256))
    | TLS_DHE_DSS_WITH_AES_256_GCM_SHA384    -> CipherSuite (DHE_DSS, CS_AEAD(AES_256_GCM, SHA384))
    | TLS_DH_DSS_WITH_AES_128_GCM_SHA256     -> CipherSuite (DH_DSS,  CS_AEAD(AES_128_GCM, SHA256))
    | TLS_DH_DSS_WITH_AES_256_GCM_SHA384     -> CipherSuite (DH_DSS,  CS_AEAD(AES_256_GCM, SHA384))
    | TLS_DH_anon_WITH_AES_128_GCM_SHA256    -> CipherSuite (DH_anon, CS_AEAD(AES_128_GCM, SHA256))
    | TLS_DH_anon_WITH_AES_256_GCM_SHA384    -> CipherSuite (DH_anon, CS_AEAD(AES_256_GCM, SHA384))

let cipherSuites_of_nameList (nameList: list<cipherSuiteName>) =
   List.map cipherSuite_of_name nameList 

let name_of_cipherSuite cs =
    match cs with
    | NullCipherSuite                                      ->  correct TLS_NULL_WITH_NULL_NULL            
                                                                
    | OnlyMACCipherSuite (RSA, MD5)                        ->  correct TLS_RSA_WITH_NULL_MD5              
    | OnlyMACCipherSuite (RSA, SHA)                        ->  correct TLS_RSA_WITH_NULL_SHA              
    | OnlyMACCipherSuite (RSA, SHA256)                     ->  correct TLS_RSA_WITH_NULL_SHA256           
    | CipherSuite (RSA, CS_MtE (RC4_128, MD5))             ->  correct TLS_RSA_WITH_RC4_128_MD5           
    | CipherSuite (RSA, CS_MtE (RC4_128, SHA))             ->  correct TLS_RSA_WITH_RC4_128_SHA           
    | CipherSuite (RSA, CS_MtE (TDES_EDE_CBC, SHA))        ->  correct TLS_RSA_WITH_3DES_EDE_CBC_SHA      
    | CipherSuite (RSA, CS_MtE (AES_128_CBC, SHA))         ->  correct TLS_RSA_WITH_AES_128_CBC_SHA       
    | CipherSuite (RSA, CS_MtE (AES_256_CBC, SHA))         ->  correct TLS_RSA_WITH_AES_256_CBC_SHA       
    | CipherSuite (RSA, CS_MtE (AES_128_CBC, SHA256))      ->  correct TLS_RSA_WITH_AES_128_CBC_SHA256    
    | CipherSuite (RSA, CS_MtE (AES_256_CBC, SHA256))      ->  correct TLS_RSA_WITH_AES_256_CBC_SHA256    
                                                                
    | CipherSuite (DHE_DSS, CS_MtE (TDES_EDE_CBC, SHA))    ->  correct TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA  
    | CipherSuite (DHE_RSA, CS_MtE (TDES_EDE_CBC, SHA))    ->  correct TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA  
    | CipherSuite (DHE_DSS, CS_MtE (AES_128_CBC, SHA))     ->  correct TLS_DHE_DSS_WITH_AES_128_CBC_SHA   
    | CipherSuite (DHE_RSA, CS_MtE (AES_128_CBC, SHA))     ->  correct TLS_DHE_RSA_WITH_AES_128_CBC_SHA   
    | CipherSuite (DHE_DSS, CS_MtE (AES_256_CBC, SHA))     ->  correct TLS_DHE_DSS_WITH_AES_256_CBC_SHA   
    | CipherSuite (DHE_RSA, CS_MtE (AES_256_CBC, SHA))     ->  correct TLS_DHE_RSA_WITH_AES_256_CBC_SHA   
    | CipherSuite (DHE_DSS, CS_MtE (AES_128_CBC, SHA256))  ->  correct TLS_DHE_DSS_WITH_AES_128_CBC_SHA256
    | CipherSuite (DHE_RSA, CS_MtE (AES_128_CBC, SHA256))  ->  correct TLS_DHE_RSA_WITH_AES_128_CBC_SHA256
    | CipherSuite (DHE_DSS, CS_MtE (AES_256_CBC, SHA256))  ->  correct TLS_DHE_DSS_WITH_AES_256_CBC_SHA256
    | CipherSuite (DHE_RSA, CS_MtE (AES_256_CBC, SHA256))  ->  correct TLS_DHE_RSA_WITH_AES_256_CBC_SHA256

    | CipherSuite (ECDHE_RSA, CS_MtE (RC4_128, SHA))       ->  correct TLS_ECDHE_RSA_WITH_RC4_128_SHA
    | CipherSuite (ECDHE_RSA, CS_MtE (TDES_EDE_CBC, SHA))  ->  correct TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA  
    | CipherSuite (ECDHE_RSA, CS_MtE (AES_128_CBC, SHA))   ->  correct TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
    | CipherSuite (ECDHE_RSA, CS_MtE (AES_128_CBC, SHA256)) -> correct TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
    | CipherSuite (ECDHE_RSA, CS_MtE (AES_256_CBC, SHA))   ->  correct TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
    | CipherSuite (ECDHE_RSA, CS_MtE (AES_256_CBC, SHA384)) -> correct TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384

    | CipherSuite (ECDHE_RSA, CS_AEAD(AES_128_GCM, SHA256)) -> correct TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
    | CipherSuite (ECDHE_RSA, CS_AEAD(AES_256_GCM, SHA384)) -> correct TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
                                          
    | CipherSuite (DH_anon, CS_MtE (RC4_128, MD5))         ->  correct TLS_DH_anon_WITH_RC4_128_MD5       
    | CipherSuite (DH_anon, CS_MtE (TDES_EDE_CBC, SHA))    ->  correct TLS_DH_anon_WITH_3DES_EDE_CBC_SHA  
    | CipherSuite (DH_anon, CS_MtE (AES_128_CBC, SHA))     ->  correct TLS_DH_anon_WITH_AES_128_CBC_SHA   
    | CipherSuite (DH_anon, CS_MtE (AES_256_CBC, SHA))     ->  correct TLS_DH_anon_WITH_AES_256_CBC_SHA   
    | CipherSuite (DH_anon, CS_MtE (AES_128_CBC, SHA256))  ->  correct TLS_DH_anon_WITH_AES_128_CBC_SHA256
    | CipherSuite (DH_anon, CS_MtE (AES_256_CBC, SHA256))  ->  correct TLS_DH_anon_WITH_AES_256_CBC_SHA256

    | CipherSuite (RSA,     CS_AEAD(AES_128_GCM, SHA256))  ->  correct TLS_RSA_WITH_AES_128_GCM_SHA256    
    | CipherSuite (RSA,     CS_AEAD(AES_256_GCM, SHA384))  ->  correct TLS_RSA_WITH_AES_256_GCM_SHA384    
    | CipherSuite (DHE_RSA, CS_AEAD(AES_128_GCM, SHA256))  ->  correct TLS_DHE_RSA_WITH_AES_128_GCM_SHA256
    | CipherSuite (DHE_RSA, CS_AEAD(AES_256_GCM, SHA384))  ->  correct TLS_DHE_RSA_WITH_AES_256_GCM_SHA384
    | CipherSuite (DH_RSA,  CS_AEAD(AES_128_GCM, SHA256))  ->  correct TLS_DH_RSA_WITH_AES_128_GCM_SHA256 
    | CipherSuite (DH_RSA,  CS_AEAD(AES_256_GCM, SHA384))  ->  correct TLS_DH_RSA_WITH_AES_256_GCM_SHA384 
    | CipherSuite (DHE_DSS, CS_AEAD(AES_128_GCM, SHA256))  ->  correct TLS_DHE_DSS_WITH_AES_128_GCM_SHA256
    | CipherSuite (DHE_DSS, CS_AEAD(AES_256_GCM, SHA384))  ->  correct TLS_DHE_DSS_WITH_AES_256_GCM_SHA384
    | CipherSuite (DH_DSS,  CS_AEAD(AES_128_GCM, SHA256))  ->  correct TLS_DH_DSS_WITH_AES_128_GCM_SHA256 
    | CipherSuite (DH_DSS,  CS_AEAD(AES_256_GCM, SHA384))  ->  correct TLS_DH_DSS_WITH_AES_256_GCM_SHA384 
    | CipherSuite (DH_anon, CS_AEAD(AES_128_GCM, SHA256))  ->  correct TLS_DH_anon_WITH_AES_128_GCM_SHA256
    | CipherSuite (DH_anon, CS_AEAD(AES_256_GCM, SHA384))  ->  correct TLS_DH_anon_WITH_AES_256_GCM_SHA384

    | _ -> Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Invoked on a unknown ciphersuite")

let rec names_of_cipherSuites css =
    match css with
    | [] -> correct []
    | h::t ->
        match name_of_cipherSuite h with
        | Error(x,y) -> Error(x,y)
        | Correct(n) ->
            match names_of_cipherSuites t with
            | Error(x,y) -> Error(x,y)
            | Correct(rem) -> correct (n::rem)


(* From Formats *)

type preContentType =
    | Change_cipher_spec
    | Alert
    | Handshake
    | Application_data

type ContentType = preContentType

let ctBytes ct =
    match ct with
    | Change_cipher_spec -> abyte (20uy)
    | Alert              -> abyte (21uy)
    | Handshake          -> abyte (22uy)
    | Application_data   -> abyte (23uy)

let parseCT b =
    match cbyte b with 
    | (20uy) -> correct(Change_cipher_spec)
    | (21uy) -> correct(Alert)
    | (22uy) -> correct(Handshake)
    | (23uy) -> correct(Application_data)
    | _        -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

let ctToString = function
    | Change_cipher_spec -> "CCS" 
    | Alert              -> "Alert"
    | Handshake          -> "Handshake"
    | Application_data   -> "Data"

let bytes_of_seq sn = bytes_of_int 8 sn
let seq_of_bytes b = int_of_bytes b

let vlbytes (lSize:int) b = bytes_of_int lSize (length b) @| b 

let vlsplit lSize vlb : Result<(bytes * bytes)> = 
    let (vl,b) = split vlb lSize in
    let l = int_of_bytes vl in
    if l <= length b 
    then correct(split b l) 
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
 
let vlparse lSize vlb : Result<bytes> = 
    let (vl,b) = split vlb lSize in
    let l = int_of_bytes vl in
    if l = length b 
    then correct b 
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

(*CF
let split_at_most data len =
    if len >= length data then
        (data,empty_bstr)
    else
        split data len

let rec appendList (xl:list<bytes>) : bytes =
    match xl with
    | [] -> empty_bstr
    | h::t -> append h (appendList t)

let rec splitList (b:bytes) (il:list<int>) : list<bytes> = 
    match il with
    | [] -> [b]
    | h::t -> let (x,y) = split b h in x::(splitList y t)
*)

type certType =
    | RSA_sign
    | DSA_sign
    | RSA_fixed_dh
    | DSA_fixed_dh

let certTypeBytes ct =
    match ct with
    | RSA_sign     -> abyte (1uy)
    | DSA_sign     -> abyte (2uy)
    | RSA_fixed_dh -> abyte (3uy)
    | DSA_fixed_dh -> abyte (4uy)

let parseCertType b =
    match cbyte b with
    | (1uy) -> Correct(RSA_sign)
    | (2uy) -> Correct(DSA_sign)
    | (3uy) -> Correct(RSA_fixed_dh)
    | (4uy) -> Correct(DSA_fixed_dh)
    | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

let rec certificateTypeListBytes ctl =
    match ctl with
    | [] -> empty_bytes
    | h::t ->
        let ct = certTypeBytes h in
        ct @| certificateTypeListBytes t

let rec parseCertificateTypeList data =
  let l = length data in
    if l = 0 then []
    else
        let (thisByte,data) = Bytes.split data 1 in
        match parseCertType thisByte with
        | Error(z) -> // skip this one
            parseCertificateTypeList data
        | Correct(ct) ->
            let rem = parseCertificateTypeList data in
            ct :: rem

let defaultCertTypes sign cs =
  let alg = sigAlg_of_ciphersuite cs in
    if sign then
      match alg with
        | SA_RSA -> [RSA_sign]
        | SA_DSA -> [DSA_sign]
        | _ -> unexpected "[defaultCertTypes] invoked on an invalid ciphersuite"
    else 
      match alg with
        | SA_RSA -> [RSA_fixed_dh]
        | SA_DSA -> [DSA_fixed_dh]
        | _ -> unexpected "[defaultCertTypes] invoked on an invalid ciphersuite"


let rec distinguishedNameListBytes names =
    match names with
    | [] -> empty_bytes
    | h::t ->
        let name = vlbytes 2 (utf8 h) in
        name @| distinguishedNameListBytes t

let rec parseDistinguishedNameList data res =
    if length data = 0 then
        correct (res)
    else
        if length data < 2 then (* Maybe at least 3 bytes, because we don't want empty names... *)
            Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
        else
            match vlsplit 2 data with
            | Error(z) -> Error(z)
            | Correct (nameBytes,data) ->
            let name = iutf8 nameBytes in (* FIXME: I have no idea wat "X501 represented in DER-encoding format" (RFC 5246, page 54) is. I assume UTF8 will do. *)
            let res = name :: res in
            parseDistinguishedNameList data res



