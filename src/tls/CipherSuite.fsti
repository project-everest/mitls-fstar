module CipherSuite

open FStar.Seq
open FStar.UInt32
open FStar.Bytes
open FStar.Error
open TLSError

open Mem
open Parse
//include Parse


/// CIPHERSUITES, with new structure for TLS 1.3
/// 18-02-22 QD fodder, will require a manual translation as we
/// primarily use this structured ADT --- see also cipherSuiteName
/// below, closer to the RFC.

include Parsers.CipherSuite // for TLS_DH_DSS_WITH_3DES_EDE_CBC_SHA

/// Various elements used in ciphersuites

(** Signature algorithms *)
type sigAlg =
 | RSASIG
 | DSA
 | ECDSA
 | RSAPSS

(** Key exchange algorithms **)
type kexAlg =
  | Kex_RSA
  | Kex_DH
  | Kex_PSK
  | Kex_PSK_DHE
  | Kex_PSK_ECDHE
  | Kex_DHE
  | Kex_ECDHE

(** Crypto algorithm names are defined in EverCrypt **)
type blockCipher = EverCrypt.block_cipher_alg
type streamCipher = EverCrypt.stream_cipher_alg
type aeadAlg = EverCrypt.aead_alg

(** Modes for the initialization vectors *)
type ivMode =
  | Fresh
  | Stale

(** Encryption types *)
type encAlg =
  | Block of blockCipher
  | Stream of streamCipher

(** TLS-specific hash and MAC algorithms *)

//18-09-08 eliminate once EverCrypt/Hashing are stable.

type hash_alg = Hashing.Spec.alg
type hashAlg = Hashing.Spec.tls_alg
type macAlg = Hashing.Spec.alg

let hashSize = Hashing.Spec.tls_tagLen
let macKeySize = Hashing.Spec.tagLen
let macSize = Hashing.Spec.tagLen

(** Authenticated Encryption modes *)
type aeAlg =
  | MACOnly: hash_alg -> aeAlg
  | MtE: encAlg -> hash_alg -> aeAlg
  | AEAD: aeadAlg -> hash_alg -> aeAlg // the hash algorithm is for the ciphersuite; it is not used by the record layer.

(** Ciphersuite definition *)
type cipherSuite' =
  | NullCipherSuite
  | CipherSuite    : kexAlg -> option sigAlg -> aeAlg -> cipherSuite'
  | CipherSuite13  : aeadAlg -> hash_alg -> cipherSuite'
  | SCSV // useless, because not a validCipherSuite (see below), but apparently needed in TLSInfo

(** Determine if a ciphersuite implies no peer authentication *)
let isAnonCipherSuite cs =
  match cs with
  | CipherSuite Kex_DHE None _ -> true
  | _ -> false

(** Determine if a ciphersuite implies using (EC)Diffie-Hellman KEX *)
let isDHECipherSuite cs =
  match cs with
  | CipherSuite Kex_DHE (Some DSA) _      -> true
  | CipherSuite Kex_DHE (Some RSASIG) _   -> true
  | CipherSuite Kex_ECDHE (Some ECDSA) _  -> true
  | CipherSuite Kex_ECDHE (Some RSASIG) _ -> true
  | _ -> false

(** Determine if a ciphersuite implies using Elliptic Curves Diffie-Hellman KEX *)
let isECDHECipherSuite cs =
  match cs with
  | CipherSuite Kex_ECDHE (Some ECDSA) _  -> true
  | CipherSuite Kex_ECDHE (Some RSASIG) _ -> true
  | _ -> false

(** Determine if a ciphersuite implies using plain Diffie-Hellman KEX *)
let isDHCipherSuite cs =
  match cs with
  | CipherSuite Kex_DH (Some DSA) _    -> true
  | CipherSuite Kex_DH (Some RSASIG) _ -> true
  | _ -> false

(** Determine if a ciphersuite implies using an RSA key exchange *)
let isRSACipherSuite cs =
  match cs with
  | CipherSuite Kex_RSA None _ -> true
  | _ -> false

(** Determine if a ciphersuite implies using MAC only and no encryption *)
let isOnlyMACCipherSuite cs =
  match cs with
  | CipherSuite _ _ (MACOnly _) -> true
  | _ -> false

(** Determine the signature algorithm associated to a ciphersuite *)
// 2018.05.14 SZ: TODO: turn this into a total function
let sigAlg_of_ciphersuite (cs:cipherSuite') : Dv sigAlg =
  match cs with
  | CipherSuite Kex_RSA None _
  | CipherSuite Kex_ECDHE (Some RSASIG) _
  | CipherSuite Kex_DHE (Some RSASIG) _
  | CipherSuite Kex_DH (Some RSASIG) _   -> RSASIG
  | CipherSuite Kex_DHE (Some DSA) _
  | CipherSuite Kex_DH (Some DSA) _      -> DSA
  | CipherSuite Kex_ECDHE (Some ECDSA) _ -> ECDSA
  | _ -> unexpected "[sigAlg_of_ciphersuite] invoked on a wrong ciphersuite"

/// 18-02-22 The parsers and formatters below are used only in
/// HandshakeMessages, should move there and disappear
/// (except for parseCipherSuite, also used in Ticket)

inline_for_extraction
type cipherSuiteName = Parsers.CipherSuite.cipherSuite

(** Determine the validity of a ciphersuite based on it's name *)
inline_for_extraction
let cipherSuite'_of_name : cipherSuiteName -> Tot (option cipherSuite')  =
  let open EverCrypt in 
  let open Hashing.Spec in function
  | TLS_NULL_WITH_NULL_NULL                -> Some ( NullCipherSuite)

  | TLS_AES_128_GCM_SHA256                 -> Some ( CipherSuite13 AES128_GCM       SHA256)
  | TLS_AES_256_GCM_SHA384                 -> Some ( CipherSuite13 AES256_GCM       SHA384)
  | TLS_CHACHA20_POLY1305_SHA256           -> Some ( CipherSuite13 CHACHA20_POLY1305 SHA256)
  | TLS_AES_128_CCM_SHA256                 -> Some ( CipherSuite13 AES128_CCM       SHA256)
  | TLS_AES_128_CCM_8_SHA256               -> Some ( CipherSuite13 AES128_CCM8     SHA256)

  | TLS_RSA_WITH_NULL_MD5                  -> Some ( CipherSuite Kex_RSA None (MACOnly MD5))
  | TLS_RSA_WITH_NULL_SHA                  -> Some ( CipherSuite Kex_RSA None (MACOnly SHA1))
  | TLS_RSA_WITH_NULL_SHA256               -> Some ( CipherSuite Kex_RSA None (MACOnly SHA256))
  | TLS_RSA_WITH_RC4_128_MD5               -> Some ( CipherSuite Kex_RSA None (MtE (Stream RC4_128) MD5))
  | TLS_RSA_WITH_RC4_128_SHA               -> Some ( CipherSuite Kex_RSA None (MtE (Stream RC4_128) SHA1))
  | TLS_RSA_WITH_3DES_EDE_CBC_SHA          -> Some ( CipherSuite Kex_RSA None (MtE (Block TDES_EDE_CBC) SHA1))
  | TLS_RSA_WITH_AES_128_CBC_SHA           -> Some ( CipherSuite Kex_RSA None (MtE (Block AES128_CBC) SHA1))
  | TLS_RSA_WITH_AES_256_CBC_SHA           -> Some ( CipherSuite Kex_RSA None (MtE (Block AES256_CBC) SHA1))
  | TLS_RSA_WITH_AES_128_CBC_SHA256        -> Some ( CipherSuite Kex_RSA None (MtE (Block AES128_CBC) SHA256))
  | TLS_RSA_WITH_AES_256_CBC_SHA256        -> Some ( CipherSuite Kex_RSA None (MtE (Block AES256_CBC) SHA256))

  | TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA      -> Some ( CipherSuite Kex_DHE (Some DSA) (MtE (Block TDES_EDE_CBC) SHA1))
  | TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA      -> Some ( CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1))
  | TLS_DHE_DSS_WITH_AES_128_CBC_SHA       -> Some ( CipherSuite Kex_DHE (Some DSA) (MtE (Block AES128_CBC) SHA1))
  | TLS_DHE_RSA_WITH_AES_128_CBC_SHA       -> Some ( CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES128_CBC) SHA1))
  | TLS_DHE_DSS_WITH_AES_256_CBC_SHA       -> Some ( CipherSuite Kex_DHE (Some DSA) (MtE (Block AES256_CBC) SHA1))
  | TLS_DHE_RSA_WITH_AES_256_CBC_SHA       -> Some ( CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES256_CBC) SHA1))
  | TLS_DHE_DSS_WITH_AES_128_CBC_SHA256    -> Some ( CipherSuite Kex_DHE (Some DSA) (MtE (Block AES128_CBC) SHA256))
  | TLS_DHE_RSA_WITH_AES_128_CBC_SHA256    -> Some ( CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES128_CBC) SHA256))
  | TLS_DHE_DSS_WITH_AES_256_CBC_SHA256    -> Some ( CipherSuite Kex_DHE (Some DSA) (MtE (Block AES256_CBC) SHA256))
  | TLS_DHE_RSA_WITH_AES_256_CBC_SHA256    -> Some ( CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES256_CBC) SHA256))

  | TLS_ECDHE_RSA_WITH_RC4_128_SHA         -> Some ( CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1))
  | TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA    -> Some ( CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1))
  | TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA     -> Some ( CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES128_CBC) SHA1))
  | TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256  -> Some ( CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES128_CBC) SHA256))
  | TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA     -> Some ( CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES256_CBC) SHA1))
  | TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384  -> Some ( CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES256_CBC) SHA384))

  | TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 -> Some ( CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES128_GCM SHA256))
  | TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256  -> Some ( CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES128_GCM SHA256))
  | TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 -> Some ( CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES256_GCM SHA384))
  | TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384  -> Some ( CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES256_GCM SHA384))

  | TLS_DH_anon_WITH_RC4_128_MD5           -> Some ( CipherSuite Kex_DHE None (MtE (Stream RC4_128) MD5))
  | TLS_DH_anon_WITH_3DES_EDE_CBC_SHA      -> Some ( CipherSuite Kex_DHE None (MtE (Block TDES_EDE_CBC) SHA1))
  | TLS_DH_anon_WITH_AES_128_CBC_SHA       -> Some ( CipherSuite Kex_DHE None (MtE (Block AES128_CBC) SHA1))
  | TLS_DH_anon_WITH_AES_256_CBC_SHA       -> Some ( CipherSuite Kex_DHE None (MtE (Block AES256_CBC) SHA1))
  | TLS_DH_anon_WITH_AES_128_CBC_SHA256    -> Some ( CipherSuite Kex_DHE None (MtE (Block AES128_CBC) SHA256))
  | TLS_DH_anon_WITH_AES_256_CBC_SHA256    -> Some ( CipherSuite Kex_DHE None (MtE (Block AES256_CBC) SHA256))

  | TLS_RSA_WITH_AES_128_GCM_SHA256        -> Some ( CipherSuite Kex_RSA None          (AEAD AES128_GCM SHA256))
  | TLS_RSA_WITH_AES_256_GCM_SHA384        -> Some ( CipherSuite Kex_RSA None          (AEAD AES256_GCM SHA384))
  | TLS_DHE_RSA_WITH_AES_128_GCM_SHA256    -> Some ( CipherSuite Kex_DHE (Some RSASIG) (AEAD AES128_GCM SHA256))
  | TLS_DHE_RSA_WITH_AES_256_GCM_SHA384    -> Some ( CipherSuite Kex_DHE (Some RSASIG) (AEAD AES256_GCM SHA384))
  | TLS_DH_RSA_WITH_AES_128_GCM_SHA256     -> Some ( CipherSuite Kex_DH  (Some RSASIG) (AEAD AES128_GCM SHA256))
  | TLS_DH_RSA_WITH_AES_256_GCM_SHA384     -> Some ( CipherSuite Kex_DH  (Some RSASIG) (AEAD AES256_GCM SHA384))
  | TLS_DHE_DSS_WITH_AES_128_GCM_SHA256    -> Some ( CipherSuite Kex_DHE (Some DSA)    (AEAD AES128_GCM SHA256))
  | TLS_DHE_DSS_WITH_AES_256_GCM_SHA384    -> Some ( CipherSuite Kex_DHE (Some DSA)    (AEAD AES256_GCM SHA384))
  | TLS_DH_DSS_WITH_AES_128_GCM_SHA256     -> Some ( CipherSuite Kex_DH  (Some DSA)    (AEAD AES128_GCM SHA256))
  | TLS_DH_DSS_WITH_AES_256_GCM_SHA384     -> Some ( CipherSuite Kex_DH  (Some DSA)    (AEAD AES256_GCM SHA384))
  | TLS_DH_anon_WITH_AES_128_GCM_SHA256    -> Some ( CipherSuite Kex_DHE None          (AEAD AES128_GCM SHA256))
  | TLS_DH_anon_WITH_AES_256_GCM_SHA384    -> Some ( CipherSuite Kex_DHE None          (AEAD AES256_GCM SHA384))
  | TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256    -> Some ( CipherSuite Kex_ECDHE (Some RSASIG) (AEAD CHACHA20_POLY1305 SHA256))
  | TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256  -> Some ( CipherSuite Kex_ECDHE (Some ECDSA) (AEAD CHACHA20_POLY1305 SHA256))
  | TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256      -> Some ( CipherSuite Kex_DHE (Some RSASIG) (AEAD CHACHA20_POLY1305 SHA256))
  | TLS_PSK_WITH_CHACHA20_POLY1305_SHA256          -> Some ( CipherSuite Kex_PSK None (AEAD CHACHA20_POLY1305 SHA256))
  | TLS_ECDHE_PSK_WITH_CHACHA20_POLY1305_SHA256    -> Some ( CipherSuite Kex_PSK_ECDHE None (AEAD CHACHA20_POLY1305 SHA256))
  | TLS_DHE_PSK_WITH_CHACHA20_POLY1305_SHA256      -> Some ( CipherSuite Kex_PSK_DHE None (AEAD CHACHA20_POLY1305 SHA256))

  | _ -> None

(** Determine the name of a ciphersuite based on its construction *)
inline_for_extraction
let name_of_cipherSuite' =
  let open EverCrypt in 
  let open Hashing.Spec in function
  | NullCipherSuite                                                      -> Correct TLS_NULL_WITH_NULL_NULL

  | CipherSuite13 AES128_GCM SHA256                                     -> Correct TLS_AES_128_GCM_SHA256
  | CipherSuite13 AES256_GCM SHA384                                     -> Correct TLS_AES_256_GCM_SHA384
  | CipherSuite13 CHACHA20_POLY1305 SHA256                               -> Correct TLS_CHACHA20_POLY1305_SHA256
  | CipherSuite13 AES128_CCM SHA256                                     -> Correct TLS_AES_128_CCM_SHA256
  | CipherSuite13 AES128_CCM8 SHA256                                   -> Correct TLS_AES_128_CCM_8_SHA256

  | CipherSuite Kex_RSA None (MACOnly MD5)                               -> Correct TLS_RSA_WITH_NULL_MD5
  | CipherSuite Kex_RSA None (MACOnly SHA1)                              -> Correct TLS_RSA_WITH_NULL_SHA
  | CipherSuite Kex_RSA None (MACOnly SHA256)                            -> Correct TLS_RSA_WITH_NULL_SHA256
  | CipherSuite Kex_RSA None (MtE (Stream RC4_128) MD5)                  -> Correct TLS_RSA_WITH_RC4_128_MD5
  | CipherSuite Kex_RSA None (MtE (Stream RC4_128) SHA1)                 -> Correct TLS_RSA_WITH_RC4_128_SHA
  | CipherSuite Kex_RSA None (MtE (Block TDES_EDE_CBC) SHA1)             -> Correct TLS_RSA_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_RSA None (MtE (Block AES128_CBC) SHA1)              -> Correct TLS_RSA_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_RSA None (MtE (Block AES256_CBC) SHA1)              -> Correct TLS_RSA_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_RSA None (MtE (Block AES128_CBC) SHA256)            -> Correct TLS_RSA_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_RSA None (MtE (Block AES256_CBC) SHA256)            -> Correct TLS_RSA_WITH_AES_256_CBC_SHA256

  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block TDES_EDE_CBC) SHA1)    -> Correct TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)    -> Correct TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES128_CBC) SHA1)     -> Correct TLS_DHE_DSS_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES128_CBC) SHA1)     -> Correct TLS_DHE_RSA_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES256_CBC) SHA1)     -> Correct TLS_DHE_DSS_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES256_CBC) SHA1)     -> Correct TLS_DHE_RSA_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES128_CBC) SHA256)   -> Correct TLS_DHE_DSS_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES128_CBC) SHA256)   -> Correct TLS_DHE_RSA_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES256_CBC) SHA256)   -> Correct TLS_DHE_DSS_WITH_AES_256_CBC_SHA256
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES256_CBC) SHA256)   -> Correct TLS_DHE_RSA_WITH_AES_256_CBC_SHA256

  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1)      -> Correct TLS_ECDHE_RSA_WITH_RC4_128_SHA
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)  -> Correct TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES128_CBC) SHA1)   -> Correct TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES128_CBC) SHA256) -> Correct TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES256_CBC) SHA1)   -> Correct TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES256_CBC) SHA384) -> Correct TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384

  | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES128_GCM SHA256)        -> Correct TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES128_GCM SHA256)        -> Correct TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES256_GCM SHA384)        -> Correct TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES256_GCM SHA384)        -> Correct TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384

  | CipherSuite Kex_DHE None (MtE (Stream RC4_128) MD5)                  -> Correct TLS_DH_anon_WITH_RC4_128_MD5
  | CipherSuite Kex_DHE None (MtE (Block TDES_EDE_CBC) SHA1)             -> Correct TLS_DH_anon_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_DHE None (MtE (Block AES128_CBC) SHA1)              -> Correct TLS_DH_anon_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_DHE None (MtE (Block AES256_CBC) SHA1)              -> Correct TLS_DH_anon_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_DHE None (MtE (Block AES128_CBC) SHA256)            -> Correct TLS_DH_anon_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_DHE None (MtE (Block AES256_CBC) SHA256)            -> Correct TLS_DH_anon_WITH_AES_256_CBC_SHA256

  | CipherSuite Kex_RSA None          (AEAD AES128_GCM SHA256)          -> Correct TLS_RSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_RSA None          (AEAD AES256_GCM SHA384)          -> Correct TLS_RSA_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES128_GCM SHA256)          -> Correct TLS_DHE_RSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES256_GCM SHA384)          -> Correct TLS_DHE_RSA_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DH  (Some RSASIG) (AEAD AES128_GCM SHA256)          -> Correct TLS_DH_RSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DH  (Some RSASIG) (AEAD AES256_GCM SHA384)          -> Correct TLS_DH_RSA_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DHE (Some DSA)    (AEAD AES128_GCM SHA256)          -> Correct TLS_DHE_DSS_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DHE (Some DSA)    (AEAD AES256_GCM SHA384)          -> Correct TLS_DHE_DSS_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DH  (Some DSA)    (AEAD AES128_GCM SHA256)          -> Correct TLS_DH_DSS_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DH  (Some DSA)    (AEAD AES256_GCM SHA384)          -> Correct TLS_DH_DSS_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DHE None          (AEAD AES128_GCM SHA256)          -> Correct TLS_DH_anon_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DHE None          (AEAD AES256_GCM SHA384)          -> Correct TLS_DH_anon_WITH_AES_256_GCM_SHA384

  | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD CHACHA20_POLY1305 SHA256)  -> Correct TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256
  | CipherSuite Kex_ECDHE (Some ECDSA) (AEAD CHACHA20_POLY1305 SHA256)   -> Correct TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256
  | CipherSuite Kex_DHE (Some RSASIG) (AEAD CHACHA20_POLY1305 SHA256)    -> Correct TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256
  | CipherSuite Kex_PSK None (AEAD CHACHA20_POLY1305 SHA256)             -> Correct TLS_PSK_WITH_CHACHA20_POLY1305_SHA256
  | CipherSuite Kex_PSK_ECDHE None (AEAD CHACHA20_POLY1305 SHA256)       -> Correct TLS_ECDHE_PSK_WITH_CHACHA20_POLY1305_SHA256
  | CipherSuite Kex_PSK_DHE None (AEAD CHACHA20_POLY1305 SHA256)         -> Correct TLS_DHE_PSK_WITH_CHACHA20_POLY1305_SHA256

  | _ -> fatal Illegal_parameter (perror __SOURCE_FILE__ __LINE__ "Invoked on a unknown ciphersuite")

let name_of_cipherSuite_of_name_post (n: Parsers.CipherSuite.cipherSuite) : GTot Type0 = match cipherSuite'_of_name n with Some c -> name_of_cipherSuite' c == Correct n | _ -> True

val name_of_cipherSuite_of_name : (n: Parsers.CipherSuite.cipherSuite) -> Tot (squash (name_of_cipherSuite_of_name_post n))

val cipherSuite_of_name_of_cipherSuite (c: cipherSuite') : Lemma (match name_of_cipherSuite' c 
 with Correct n -> cipherSuite'_of_name n == Some c | _ -> True)

let validCipherSuite (c:cipherSuite') = Correct? (name_of_cipherSuite' c)

inline_for_extraction
let cipherSuite = c:cipherSuite' {validCipherSuite c} // we finally decide to shadow Parsers.CipherSuite.cipherSuite from now on
let valid_cipher_suite = cipherSuite // redundant, needed by HandshakeMessages for now

type cipherSuites = cs: list cipherSuite
 { let l = List.length cs in 0 <= l /\ l <= (65536/2 - 2)}

(** List of valid ciphersuite (redundant) *)
let valid_cipher_suites = cipherSuites

let name_of_cipherSuite_of_name' (n: cipherSuiteName) (c: cipherSuite') : Lemma
  (requires (cipherSuite'_of_name n == Some c))
  (ensures (name_of_cipherSuite' c == Correct n))
= let _ : squash (name_of_cipherSuite_of_name_post n) = name_of_cipherSuite_of_name n in
  assert (name_of_cipherSuite_of_name_post n);
  ()

inline_for_extraction
let cipherSuite_of_name (c: cipherSuiteName) : Tot (option cipherSuite) =
  match cipherSuite'_of_name c with
  | Some v -> [@inline_let] let _ = name_of_cipherSuite_of_name' c v in Some v
  | None -> None

inline_for_extraction
let name_of_cipherSuite (c: cipherSuite) : Tot cipherSuiteName =
  [@inline_let] let _ = cipherSuite_of_name_of_cipherSuite c in
  match name_of_cipherSuite' c with
  | Correct n -> n

(* TODO: rewrite this function using a loop *)

#reset-options "--using_facts_from '* -LowParse.Spec.Base'"

let rec cipherSuites_of_nameList_aux (l: list cipherSuiteName) (accu: list cipherSuite) : Tot (l' : list cipherSuite { List.Tot.length l' <= List.Tot.length l + List.Tot.length accu } ) (decreases l) =
  match l with
  | [] ->
    List.Tot.rev_length accu;
    List.Tot.rev accu
  | n :: q ->
    begin match cipherSuite_of_name n with
    | None -> cipherSuites_of_nameList_aux q accu
    | Some c -> cipherSuites_of_nameList_aux q (c :: accu)
    end

let cipherSuites_of_nameList (l: list cipherSuiteName) : Tot (l' : list cipherSuite { List.Tot.length l' <= List.Tot.length l } ) =
  cipherSuites_of_nameList_aux l []

let rec nameList_of_cipherSuites_aux (l: list cipherSuite) (accu: list cipherSuiteName) : Tot (l' : list cipherSuiteName { List.Tot.length l' == List.Tot.length l + List.Tot.length accu } ) (decreases l) =
  match l with
  | [] ->
    List.Tot.rev_length accu;
    List.Tot.rev accu
  | c :: q -> nameList_of_cipherSuites_aux q (name_of_cipherSuite c :: accu)

let nameList_of_cipherSuites (l: list cipherSuite) : Tot (l' : list cipherSuiteName { List.Tot.length l' == List.Tot.length l } ) =
  nameList_of_cipherSuites_aux l []

(* Parsers and serializers for cipherSuite *names* *)

#reset-options

let cipherSuiteNameBytes : cipherSuiteName -> Tot (lbytes 2) =
  LowParseWrappers.wrap_serializer32_constant_length cipherSuite_serializer32 2 ()

inline_for_extraction
let parse_cipherSuiteName_error_msg : string =
  FStar.Error.perror __SOURCE_FILE__ __LINE__ ""

let parseCipherSuiteName: b:lbytes 2
  -> Tot (cm:cipherSuiteName{cipherSuiteNameBytes cm == b}) =
  LowParseWrappers.wrap_parser32_total_constant_length cipherSuite_serializer32 cipherSuite_parser32 2 ()
