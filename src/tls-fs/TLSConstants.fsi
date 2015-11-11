(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module TLSConstants

open Bytes
open Error
open TLSError

type PreProtocolVersion =
    | SSL_3p0
    | TLS_1p0
    | TLS_1p1
    | TLS_1p2
type ProtocolVersion = PreProtocolVersion

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
    | MA_SSLKHASH of hashAlg

type sigAlg = 
    | SA_RSA
    | SA_DSA 
    | SA_ECDSA

type sigHashAlg = sigAlg * hashAlg

type aeadAlg =
    | AES_128_GCM
    | AES_256_GCM

type aeAlg =
    | MACOnly of macAlg
    | MtE of encAlg * macAlg
    | AEAD of aeadAlg * macAlg

val sigAlgBytes: sigAlg -> bytes
val parseSigAlg: bytes -> Result<sigAlg>
val hashAlgBytes: hashAlg -> bytes
val parseHashAlg: bytes -> Result<hashAlg>

val encKeySize: encAlg -> nat
val blockSize: blockCipher -> nat
val aeadKeySize: aeadAlg -> nat
val aeadIVSize: aeadAlg -> nat
val aeadRecordIVSize: aeadAlg -> nat
val aeadTagSize: aeadAlg -> nat
val hashSize: hashAlg -> nat
val macKeySize: macAlg -> nat
val macSize: macAlg -> nat

type cipherSuite

type cipherSuites = list<cipherSuite>

type PreCompression = NullCompression
type Compression = PreCompression

val versionBytes: ProtocolVersion -> bytes
val parseVersion: bytes -> Result<ProtocolVersion>
val minPV: ProtocolVersion -> ProtocolVersion -> ProtocolVersion
val geqPV: ProtocolVersion -> ProtocolVersion -> bool
val somePV: ProtocolVersion -> option<ProtocolVersion>

val nullCipherSuite: cipherSuite
val isNullCipherSuite: cipherSuite -> bool

val isAnonCipherSuite: cipherSuite -> bool
val isDHCipherSuite: cipherSuite -> bool
val isDHECipherSuite: cipherSuite -> bool
val isECDHECipherSuite: cipherSuite -> bool
val isRSACipherSuite: cipherSuite -> bool
val isOnlyMACCipherSuite: cipherSuite -> bool
val contains_TLS_EMPTY_RENEGOTIATION_INFO_SCSV: cipherSuites -> bool

type prflabel = bytes
val extract_label: prflabel
val extended_extract_label: prflabel
val kdf_label: prflabel 

type prePrfAlg =  
  | PRF_SSL3_nested                   // MD5(SHA1(...)) for extraction and keygen
  | PRF_SSL3_concat                   // MD5 @| SHA1    for VerifyData tags
  | PRF_TLS_1p01 of prflabel          // MD5 xor SHA1
  | PRF_TLS_1p2 of prflabel * macAlg  // typically SHA256 but may depend on CS

type kefAlg = prePrfAlg
type kdfAlg = prePrfAlg
type vdAlg = ProtocolVersion * cipherSuite

val verifyDataLen_of_ciphersuite: cipherSuite -> nat
val prfMacAlg_of_ciphersuite: cipherSuite -> macAlg
val verifyDataHashAlg_of_ciphersuite: cipherSuite -> hashAlg

val sessionHashAlg: ProtocolVersion -> cipherSuite -> hashAlg

val mk_aeAlg: cipherSuite -> ProtocolVersion -> aeAlg
val macAlg_of_aeAlg: aeAlg -> macAlg
val encAlg_of_aeAlg: aeAlg -> encAlg
val macAlg_of_ciphersuite: cipherSuite -> ProtocolVersion -> macAlg
val encAlg_of_ciphersuite: cipherSuite -> ProtocolVersion -> encAlg
val sigAlg_of_ciphersuite: cipherSuite -> sigAlg

val compressionBytes: Compression -> bytes
val compressionMethodsBytes: list<Compression> -> bytes
val parseCompression: bytes -> Result<Compression>
val parseCompressions: bytes -> list<Compression>

val cipherSuiteBytes: cipherSuite -> bytes
val parseCipherSuite: bytes -> Result<cipherSuite>
val parseCipherSuites: bytes -> Result<cipherSuites>
val cipherSuitesBytes: cipherSuites -> bytes

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

val cipherSuite_of_name: cipherSuiteName -> cipherSuite
val cipherSuites_of_nameList: list<cipherSuiteName> -> cipherSuites
val name_of_cipherSuite: cipherSuite -> Result<cipherSuiteName>
val names_of_cipherSuites: cipherSuites -> Result<list<cipherSuiteName>>

type preContentType =
    | Change_cipher_spec
    | Alert
    | Handshake
    | Application_data

type ContentType = preContentType 
val bytes_of_seq: nat -> bytes
val seq_of_bytes: bytes -> nat

val ctBytes: ContentType -> bytes
val parseCT: bytes -> Result<ContentType>
val ctToString: ContentType -> string

val vlbytes: nat -> bytes -> bytes
val vlsplit: nat -> bytes -> Result<(bytes * bytes)>
val vlparse: nat -> bytes -> Result<bytes>

type certType =
    | RSA_sign
    | DSA_sign
    | RSA_fixed_dh
    | DSA_fixed_dh

val certTypeBytes: certType -> bytes
val parseCertType: bytes -> Result<certType>
val certificateTypeListBytes: list<certType> -> bytes
val parseCertificateTypeList: bytes -> list<certType>
val defaultCertTypes: bool -> cipherSuite -> list<certType>
val distinguishedNameListBytes: list<string> -> bytes
val parseDistinguishedNameList: bytes -> list<string> -> Result<list<string>>
