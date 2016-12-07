module TLSConstants

(**
This file implements type representations and parsing functions
for the different values negotiated during the TLS
handshake. For instance protocol version, key exchange mechanism,
hash algorithm etc.

@summary Module for main constants
*)

#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1"

open FStar.SeqProperties
open Platform.Bytes
open Platform.Error
open TLSError
open CoreCrypto

module HH = FStar.HyperHeap
module HS = FStar.HyperStack


(** Regions and colors for objects in memory *)
let tls_color = -1
let epoch_color = 1
let hs_color = 2

let is_tls_rgn r   = HH.color r = tls_color
let is_epoch_rgn r = HH.color r = epoch_color
let is_hs_rgn r    = HH.color r = hs_color

(*
 * AR: Adding the eternal region predicate.
 * Strengthening the predicate because at some places, the code uses HH.parent.
 *)
let rgn       = r:HH.rid{r<>HH.root
                         /\ (forall (s:HH.rid).{:pattern HS.is_eternal_region s} HS.is_above s r ==> HS.is_eternal_region s)}
let tls_rgn   = r:rgn{is_tls_rgn r}
let epoch_rgn = r:rgn{is_epoch_rgn r}
let hs_rgn    = r:rgn{is_hs_rgn r}

let tls_region : tls_rgn = new_colored_region HH.root tls_color

let tls_tables_region : (r:tls_rgn{HH.parent r = tls_region}) =
    new_region tls_region


(** Polarity for reading and writing *)
type rw =
  | Reader
  | Writer

(** Role of the library in current execution *)
type role =
  | Client
  | Server

(** Dual role *)
let dualRole = function
  | Client -> Server
  | Server -> Client

(** Protocol version negotiated values *)
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
  | Kex_PSK
  | Kex_PSK_DHE
  | Kex_PSK_ECDHE
  | Kex_DHE
  | Kex_ECDHE

(** Aliasing of cryptographic types from the CoreCrypto library *)
type blockCipher = block_cipher
type streamCipher = stream_cipher
type aeadAlg = aead_cipher

(** Modes for the initialization vectors *)
type ivMode =
  | Fresh
  | Stale

(** Encryption types *)
type encAlg =
  | Block of blockCipher
  | Stream of streamCipher

(** Hash algorithm types *)
type hashAlg =
  | NULL
  | MD5SHA1
  | Hash of hash_alg

(** MAC algorithm types *)
type macAlg =
  | HMAC     of hash_alg
  | SSLKHASH of hash_alg

(** Authenticated Encryption modes *)
type aeAlg =
  | MACOnly: hash_alg -> aeAlg
  | MtE: encAlg -> hash_alg -> aeAlg
  | AEAD: aeadAlg -> hash_alg -> aeAlg  // the hash algorithm is for the ciphersuite; it is not used by the record layer.

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

// -----------------------------------------------------------------------
// record-layer length constants [5.2.1]
// note that TLS 1.3 lowers a bit the upper bound of cipher lengths (Ok in principle)
// but still enables padding beyond plausible plaintext lengths.

(** Constants for API and protocol-level fragments are in [0..2^14] *)
let max_TLSPlaintext_fragment_length = 16384
let max_TLSCompressed_fragment_length = max_TLSPlaintext_fragment_length + 1024
let max_TLSCiphertext_fragment_length = max_TLSPlaintext_fragment_length + 2048
let max_TLSCiphertext_fragment_length_13 = max_TLSPlaintext_fragment_length + 256

//CF we leave these functions abstract for verification purposes
//CF we may need to be more negative on weak algorithms (so that we don't try to verify their use)
//CF and more precise/positive on algorithms we implement (so that we reflect lower assumptions)

(** Signature algorithms *)
type sigAlg = CoreCrypto.sig_alg


(** Hash algorithm minimum requirements *)
type hashAlg' = h:hashAlg{h <> NULL /\ h <> MD5SHA1 }

(** Encryption key sizes *)
let encKeySize = function
  | Stream RC4_128      -> 16
  | Block TDES_EDE_CBC  -> 24
  | Block AES_128_CBC   -> 16
  | Block AES_256_CBC   -> 32
  | Block TDES_EDE_CBC  -> 24
  | Block AES_128_CBC   -> 16
  | Block AES_256_CBC   -> 32

(** AEAD salt sizes *)
let aeadSaltSize = function // TLS 1.3 IV salt.
  | AES_128_GCM       -> 4
  | AES_256_GCM       -> 4
  | CHACHA20_POLY1305 -> 12
  | _                 -> 4 //recheck

(** AEAD *)
let aeadRecordIVSize = function // TLS 1.2 explicit IVs
  | AES_128_GCM       -> 8
  | AES_256_GCM       -> 8
  | CHACHA20_POLY1305 -> 0
  | _                 -> 8 //recheck

(** Hash sizes *)
val hashSize: h:hashAlg{h<>NULL} -> Tot nat
let hashSize = function
  | Hash h  -> CoreCrypto.hashSize h
  | MD5SHA1 -> 16 + 20

(** MAC key sizes *)
let macKeySize = function
  | HMAC alg
  | SSLKHASH alg -> hashSize (Hash alg)

(** MAC sizes *)
let macSize = function
  | HMAC alg
  | SSLKHASH alg -> hashSize (Hash alg)

(** Ciphersuite for SCSV *)
type scsv_suite =
  | TLS_EMPTY_RENEGOTIATION_INFO_SCSV

(** Ciphersuite definition *)
type cipherSuite =
  | NullCipherSuite: cipherSuite
  | CipherSuite    : kexAlg -> option sig_alg -> aeAlg -> cipherSuite
  | SCSV           : scsv_suite -> cipherSuite
  | UnknownCipherSuite: a:byte -> b:byte(* {not(List.Tot.contains (a,b) known_cs_list)}  *) -> cipherSuite // JK: incomplete spec

(** List of ciphersuite *)
type cipherSuites = list cipherSuite

(** Compression definition *)
type compression =
  | NullCompression
  | UnknownCompression of (b:byte{b <> 0z})

(** Determine the oldest protocol versions for TLS *)
let minPV (a:protocolVersion) (b:protocolVersion) =
  match a,b with
  | SSL_3p0, _  | _, SSL_3p0 -> SSL_3p0
  | TLS_1p0, _  | _, TLS_1p0 -> TLS_1p0
  | TLS_1p1, _  | _, TLS_1p1 -> TLS_1p1
  | TLS_1p2, _  | _, TLS_1p2 -> TLS_1p2
  | TLS_1p3, _  | _, TLS_1p3 -> TLS_1p3

let geqPV a b = (b = minPV a b)

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


(** Definition for the PRF label type *)
type prflabel = bytes

(** Key schedule labels *)
let extract_label          = utf8 "master secret"
let extended_extract_label = utf8 "extended master secret"
let kdf_label              = utf8 "key expansion"

(** PRF definitions based on the protocol version *)
type prePrfAlg =
  | PRF_SSL3_nested         // MD5(SHA1(...)) for extraction and keygen
  | PRF_SSL3_concat         // MD5 @| SHA1    for VerifyData tags
  | PRF_TLS_1p01 of prflabel                       // MD5 xor SHA1
  | PRF_TLS_1p2 : prflabel -> macAlg -> prePrfAlg  // typically SHA256 but may depend on CS
  | PRF_TLS_1p3 // TBC

(** PRF associations *)
//BB.TODO: Documentation ?
type kefAlg_t = prePrfAlg
type kdfAlg_t = prePrfAlg
type vdAlg_t = protocolVersion * cipherSuite

// Only to be invoked with TLS 1.2 (hardcoded in previous versions
// BB.TODO: Documentation ? Confirm that it is used with TLS 1.3 !
let verifyDataLen_of_ciphersuite (cs:cipherSuite) = 12

// Only to be invoked with TLS 1.2 (hardcoded in previous versions
// BB.TODO: Documentation ? Confirm that it is used with TLS 1.3 !
val prfMacAlg_of_ciphersuite_aux: cipherSuite -> Tot (option macAlg)
let prfMacAlg_of_ciphersuite_aux = function
  | CipherSuite  _ _  (MtE  _ _ )   -> Some (HMAC SHA256)
  | CipherSuite  _ _  (AEAD _ hAlg) -> Some (HMAC hAlg)
  | CipherSuite  _ _  (MACOnly _)   -> Some (HMAC SHA256) //MK was (MACOnly hAlg) should it also be be (HMAC hAlg)?
  | _                               -> None


(** Determine if the tuple PV and CS is the correct association with PRF *)
let pvcs (pv:protocolVersion) (cs:cipherSuite) =
  match pv with
  | TLS_1p2 | TLS_1p3 -> is_Some (prfMacAlg_of_ciphersuite_aux cs)
  | _                 -> true

unfold type require_some (#a:Type) (#b:Type) ($f:(a -> Tot (option b))) =
  x:a{is_Some (f x)} -> Tot b

let prfMacAlg_of_ciphersuite : require_some prfMacAlg_of_ciphersuite_aux =
  fun x -> Some.v (prfMacAlg_of_ciphersuite_aux x)

// PRF and verifyData hash algorithms are potentially independent in TLS 1.2,
// so we use two distinct functions. However, all currently defined ciphersuites
// use the same hash algorithm, so the current implementation of the two functions
// is the same.

// Only to be invoked with TLS 1.2 (hardcoded in previous versions
// BB.TODO: Documentation ? Confirm that it is used with TLS 1.3 !
let verifyDataHashAlg_of_ciphersuite_aux = function
  | CipherSuite _ _ (MtE  _ _)    -> Some SHA256
  | CipherSuite _ _ (AEAD _ hAlg) -> Some hAlg
  | CipherSuite _ _ (MACOnly hAlg) -> Some SHA256
  | _                               -> None

// BB.TODO: Documentation ?
let verifyDataHashAlg_of_ciphersuite : require_some verifyDataHashAlg_of_ciphersuite_aux =
  fun x -> Some.v (verifyDataHashAlg_of_ciphersuite_aux x)

(** Determine which session hash algorithm is to be used with the protocol version and ciphersuite *)
val sessionHashAlg: pv:protocolVersion -> cs:cipherSuite{pvcs pv cs} -> Tot hashAlg
let sessionHashAlg pv cs =
  match pv with
  | SSL_3p0 | TLS_1p0 | TLS_1p1 -> MD5SHA1
  | TLS_1p2 | TLS_1p3           -> Hash (verifyDataHashAlg_of_ciphersuite cs)
// TODO recheck this is the right hash for HKDF
// SZ: Right. The TLS 1.3 draft says "Where HMAC [RFC2104] uses
// the Hash algorithm for the handshake"

(** Determine the Authenticated Encryption algorithm associated with a ciphersuite *)
val get_aeAlg: cs:cipherSuite{ is_CipherSuite cs } -> Tot aeAlg
let get_aeAlg cs =
  match cs with
  | CipherSuite _ _ ae -> ae

(** Define the null authenticated encryption algorithm *)
// BB: Why does this default to MD5 ?
let null_aeAlg = MACOnly MD5

(** Determine Encryption type to be used with a chosen PV and AE algorithm *)
val encAlg_of_aeAlg: (pv:protocolVersion) -> (a:aeAlg { is_MtE a }) -> Tot (encAlg * ivMode)
let encAlg_of_aeAlg  pv ae =
  match pv,ae with
  | SSL_3p0, MtE (Block e) m -> (Block e),Stale
  | TLS_1p0, MtE (Block e) m -> (Block e),Stale
  | _, MtE e m -> e,Fresh

(** Determine MAC algorithm to be used with a chosen PV and AE algorithm *)
val macAlg_of_aeAlg: (pv:protocolVersion) -> (a:aeAlg { pv <> TLS_1p3 /\ ~(is_AEAD a) }) -> Tot macAlg
let macAlg_of_aeAlg pv ae =
  match pv,ae with
  | SSL_3p0,MACOnly alg -> SSLKHASH alg (* dropped pattern on the left to simplify refinements *)
  | _      ,MACOnly alg -> SSLKHASH alg
  | SSL_3p0,MtE _ alg   -> SSLKHASH alg
  | _      ,MtE _ alg   -> HMAC alg

(** Ciphersuite names definition *)
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

  | TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
  | TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
  | TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384
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


val known_cipher_suite: cipherSuite -> Tot bool 
let known_cipher_suite cs =
    match cs with
    | UnknownCipherSuite _ _
    | NullCipherSuite          
    | CipherSuite Kex_RSA None (MACOnly MD5) 
    | CipherSuite Kex_RSA None (MACOnly SHA1)
    | CipherSuite Kex_RSA None (MACOnly SHA256)
    | CipherSuite Kex_RSA None(MtE (Stream RC4_128) MD5)
    | CipherSuite Kex_RSA None(MtE (Stream RC4_128) SHA1)
    | CipherSuite Kex_RSA None(MtE (Block TDES_EDE_CBC) SHA1)  
    | CipherSuite Kex_RSA None(MtE (Block AES_128_CBC) SHA1)   
    | CipherSuite Kex_RSA None(MtE (Block AES_256_CBC) SHA1)   
    | CipherSuite Kex_RSA None(MtE (Block AES_128_CBC) SHA256) 
    | CipherSuite Kex_RSA None(MtE (Block AES_256_CBC) SHA256) 
    | CipherSuite Kex_DH (Some DSA)     (MtE (Block TDES_EDE_CBC) SHA1)  
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block TDES_EDE_CBC) SHA1)  
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block TDES_EDE_CBC) SHA1)  
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)  
    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_128_CBC) SHA1)   
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_128_CBC) SHA1)   
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_128_CBC) SHA1)   
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1)   
    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_256_CBC) SHA1)   
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_256_CBC) SHA1)   
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_256_CBC) SHA1)   
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1)   
    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_128_CBC) SHA256) 
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_128_CBC) SHA256) 
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_128_CBC) SHA256) 
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256) 
    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES_256_CBC) SHA256) 
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES_256_CBC) SHA256) 
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_256_CBC) SHA256) 
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA256) 
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1)      
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)  
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1)   
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1)   
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256) 
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA384) 
    | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_128_GCM SHA256)
    | CipherSuite Kex_ECDHE (Some ECDSA)  (AEAD AES_128_GCM SHA256)
    | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_256_GCM SHA384)
    | CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES_256_GCM SHA384) 
    | CipherSuite Kex_PSK_DHE None (AEAD AES_128_GCM SHA256) 
    | CipherSuite Kex_PSK_DHE None (AEAD AES_256_GCM SHA384) 
    | CipherSuite Kex_PSK_ECDHE None (AEAD AES_128_GCM SHA256)
    | CipherSuite Kex_PSK_ECDHE None (AEAD AES_256_GCM SHA384)
    | CipherSuite Kex_DHE None   (MtE (Stream RC4_128) MD5)       
    | CipherSuite Kex_DHE None   (MtE (Block TDES_EDE_CBC) SHA1)  
    | CipherSuite Kex_DHE None   (MtE (Block AES_128_CBC) SHA1)   
    | CipherSuite Kex_DHE None   (MtE (Block AES_256_CBC) SHA1)   
    | CipherSuite Kex_DHE None   (MtE (Block AES_128_CBC) SHA256) 
    | CipherSuite Kex_DHE None   (MtE (Block AES_256_CBC) SHA256) 
    | CipherSuite Kex_RSA None     (AEAD AES_128_GCM SHA256) 
    | CipherSuite Kex_RSA None     (AEAD AES_256_GCM SHA384) 
    | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_128_GCM SHA256)
    | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_256_GCM SHA384)
    | CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_128_GCM SHA256)
    | CipherSuite Kex_DH (Some RSASIG)  (AEAD AES_256_GCM SHA384)
    | CipherSuite Kex_DHE (Some DSA) (AEAD AES_128_GCM SHA256)
    | CipherSuite Kex_DHE (Some DSA) (AEAD AES_256_GCM SHA384)
    | CipherSuite Kex_DH (Some DSA)  (AEAD AES_128_GCM SHA256)
    | CipherSuite Kex_DH (Some DSA)  (AEAD AES_256_GCM SHA384)
    | CipherSuite Kex_DHE None (AEAD AES_128_GCM SHA256)
    | CipherSuite Kex_DHE None (AEAD AES_256_GCM SHA384)
    | SCSV (TLS_EMPTY_RENEGOTIATION_INFO_SCSV)        -> true
    | _ -> false

type valid_cipher_suite = c:cipherSuite{known_cipher_suite c}
type valid_cipher_suites = list valid_cipher_suite

(** Definition of a list of ciphersuite *)
type cipherSuiteNames = list cipherSuiteName

(** Determine the validity of a ciphersuite based on it's name *)
val cipherSuite_of_name: cipherSuiteName -> Tot valid_cipher_suite
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

  | TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 -> CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES_128_GCM SHA256)
  | TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256  -> CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_128_GCM SHA256)
  | TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 -> CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES_256_GCM SHA384)
  | TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384  -> CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_256_GCM SHA384)

  | TLS_DH_anon_WITH_RC4_128_MD5           -> CipherSuite Kex_DHE None (MtE (Stream RC4_128) MD5)
  | TLS_DH_anon_WITH_3DES_EDE_CBC_SHA      -> CipherSuite Kex_DHE None (MtE (Block TDES_EDE_CBC) SHA1)
  | TLS_DH_anon_WITH_AES_128_CBC_SHA       -> CipherSuite Kex_DHE None (MtE (Block AES_128_CBC) SHA1)
  | TLS_DH_anon_WITH_AES_256_CBC_SHA       -> CipherSuite Kex_DHE None (MtE (Block AES_256_CBC) SHA1)
  | TLS_DH_anon_WITH_AES_128_CBC_SHA256    -> CipherSuite Kex_DHE None (MtE (Block AES_128_CBC) SHA256)
  | TLS_DH_anon_WITH_AES_256_CBC_SHA256    -> CipherSuite Kex_DHE None (MtE (Block AES_256_CBC) SHA256)

  | TLS_RSA_WITH_AES_128_GCM_SHA256        -> CipherSuite Kex_RSA None          (AEAD AES_128_GCM SHA256)
  | TLS_RSA_WITH_AES_256_GCM_SHA384        -> CipherSuite Kex_RSA None          (AEAD AES_256_GCM SHA384)
  | TLS_DHE_RSA_WITH_AES_128_GCM_SHA256    -> CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_128_GCM SHA256)
  | TLS_DHE_RSA_WITH_AES_256_GCM_SHA384    -> CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_256_GCM SHA384)
  | TLS_DH_RSA_WITH_AES_128_GCM_SHA256     -> CipherSuite Kex_DH  (Some RSASIG) (AEAD AES_128_GCM SHA256)
  | TLS_DH_RSA_WITH_AES_256_GCM_SHA384     -> CipherSuite Kex_DH  (Some RSASIG) (AEAD AES_256_GCM SHA384)
  | TLS_DHE_DSS_WITH_AES_128_GCM_SHA256    -> CipherSuite Kex_DHE (Some DSA)    (AEAD AES_128_GCM SHA256)
  | TLS_DHE_DSS_WITH_AES_256_GCM_SHA384    -> CipherSuite Kex_DHE (Some DSA)    (AEAD AES_256_GCM SHA384)
  | TLS_DH_DSS_WITH_AES_128_GCM_SHA256     -> CipherSuite Kex_DH  (Some DSA)    (AEAD AES_128_GCM SHA256)
  | TLS_DH_DSS_WITH_AES_256_GCM_SHA384     -> CipherSuite Kex_DH  (Some DSA)    (AEAD AES_256_GCM SHA384)
  | TLS_DH_anon_WITH_AES_128_GCM_SHA256    -> CipherSuite Kex_DHE None          (AEAD AES_128_GCM SHA256)
  | TLS_DH_anon_WITH_AES_256_GCM_SHA384    -> CipherSuite Kex_DHE None          (AEAD AES_256_GCM SHA384)


(** Return valid ciphersuites according to a list of ciphersuite names *)
val cipherSuites_of_nameList: l1:list cipherSuiteName
  -> Tot (l2:valid_cipher_suites{List.Tot.length l2 = List.Tot.length l1})
let cipherSuites_of_nameList nameList =
  // REMARK: would trigger automatically if ListProperties is loaded
  ListProperties.map_lemma cipherSuite_of_name nameList;
  List.Tot.map cipherSuite_of_name nameList

(** Determine the name of a ciphersuite based on its construction *)
let name_of_cipherSuite cs =
  match cs with
  | NullCipherSuite                                                      -> Correct TLS_NULL_WITH_NULL_NULL

  | CipherSuite Kex_RSA None (MACOnly MD5)                               -> Correct TLS_RSA_WITH_NULL_MD5
  | CipherSuite Kex_RSA None (MACOnly SHA1)                              -> Correct TLS_RSA_WITH_NULL_SHA
  | CipherSuite Kex_RSA None (MACOnly SHA256)                            -> Correct TLS_RSA_WITH_NULL_SHA256
  | CipherSuite Kex_RSA None (MtE (Stream RC4_128) MD5)                  -> Correct TLS_RSA_WITH_RC4_128_MD5
  | CipherSuite Kex_RSA None (MtE (Stream RC4_128) SHA1)                 -> Correct TLS_RSA_WITH_RC4_128_SHA
  | CipherSuite Kex_RSA None (MtE (Block TDES_EDE_CBC) SHA1)             -> Correct TLS_RSA_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_RSA None (MtE (Block AES_128_CBC) SHA1)              -> Correct TLS_RSA_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_RSA None (MtE (Block AES_256_CBC) SHA1)              -> Correct TLS_RSA_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_RSA None (MtE (Block AES_128_CBC) SHA256)            -> Correct TLS_RSA_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_RSA None (MtE (Block AES_256_CBC) SHA256)            -> Correct TLS_RSA_WITH_AES_256_CBC_SHA256

  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block TDES_EDE_CBC) SHA1)    -> Correct TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)    -> Correct TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_128_CBC) SHA1)     -> Correct TLS_DHE_DSS_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1)     -> Correct TLS_DHE_RSA_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_256_CBC) SHA1)     -> Correct TLS_DHE_DSS_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1)     -> Correct TLS_DHE_RSA_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_128_CBC) SHA256)   -> Correct TLS_DHE_DSS_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256)   -> Correct TLS_DHE_RSA_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES_256_CBC) SHA256)   -> Correct TLS_DHE_DSS_WITH_AES_256_CBC_SHA256
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA256)   -> Correct TLS_DHE_RSA_WITH_AES_256_CBC_SHA256

  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1)      -> Correct TLS_ECDHE_RSA_WITH_RC4_128_SHA
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)  -> Correct TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA1)   -> Correct TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_128_CBC) SHA256) -> Correct TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA1)   -> Correct TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES_256_CBC) SHA384) -> Correct TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384

  | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_128_GCM SHA256)        -> Correct TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES_128_GCM SHA256)        -> Correct TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES_256_GCM SHA384)        -> Correct TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES_256_GCM SHA384)        -> Correct TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384

  | CipherSuite Kex_DHE None (MtE (Stream RC4_128) MD5)                  -> Correct TLS_DH_anon_WITH_RC4_128_MD5
  | CipherSuite Kex_DHE None (MtE (Block TDES_EDE_CBC) SHA1)             -> Correct TLS_DH_anon_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_DHE None (MtE (Block AES_128_CBC) SHA1)              -> Correct TLS_DH_anon_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_DHE None (MtE (Block AES_256_CBC) SHA1)              -> Correct TLS_DH_anon_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_DHE None (MtE (Block AES_128_CBC) SHA256)            -> Correct TLS_DH_anon_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_DHE None (MtE (Block AES_256_CBC) SHA256)            -> Correct TLS_DH_anon_WITH_AES_256_CBC_SHA256

  | CipherSuite Kex_RSA None          (AEAD AES_128_GCM SHA256)          -> Correct TLS_RSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_RSA None          (AEAD AES_256_GCM SHA384)          -> Correct TLS_RSA_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_128_GCM SHA256)          -> Correct TLS_DHE_RSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES_256_GCM SHA384)          -> Correct TLS_DHE_RSA_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DH  (Some RSASIG) (AEAD AES_128_GCM SHA256)          -> Correct TLS_DH_RSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DH  (Some RSASIG) (AEAD AES_256_GCM SHA384)          -> Correct TLS_DH_RSA_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DHE (Some DSA)    (AEAD AES_128_GCM SHA256)          -> Correct TLS_DHE_DSS_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DHE (Some DSA)    (AEAD AES_256_GCM SHA384)          -> Correct TLS_DHE_DSS_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DH  (Some DSA)    (AEAD AES_128_GCM SHA256)          -> Correct TLS_DH_DSS_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DH  (Some DSA)    (AEAD AES_256_GCM SHA384)          -> Correct TLS_DH_DSS_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DHE None          (AEAD AES_128_GCM SHA256)          -> Correct TLS_DH_anon_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DHE None          (AEAD AES_256_GCM SHA384)          -> Correct TLS_DH_anon_WITH_AES_256_GCM_SHA384

  | _ -> Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Invoked on a unknown ciphersuite")


#set-options "--max_ifuel 5 --initial_ifuel 5 --max_fuel 1 --initial_fuel 1"

(** Determine the names associated to a list of ciphersuite constructors *)
val names_of_cipherSuites : cipherSuites -> Tot (result cipherSuiteNames)
let rec names_of_cipherSuites css =
  match css with
  | [] -> Correct []
  | h::t ->
    begin
    match name_of_cipherSuite h with
    | Error(x,y) -> Error(x,y)
    | Correct n  ->
      begin
	match names_of_cipherSuites t with
        | Error(x,y)  -> Error(x,y)
        | Correct rem -> Correct (n::rem)
      end
    end


type cert = b:bytes {length b <= 16777215}
type chain = list cert


(** Certificate type definition *)
type certType =
  | RSA_sign
  | DSA_sign
  | RSA_fixed_dh
  | DSA_fixed_dh

#set-options "--max_ifuel 4 --initial_ifuel 1 --max_fuel 4 --initial_fuel 1"


(** Determine the certificate signature algorithms allowed according to the ciphersuite *)
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


#set-options "--max_ifuel 2 --initial_ifuel 2 --max_fuel 1 --initial_fuel 1"


(** Type definition of the Distinguished Name of a certificate *)
type dn = s:string{length(utf8 s) <= 256}

(** Determine if a ciphersuite list contains the SCSV ciphersuite *)
let contains_TLS_EMPTY_RENEGOTIATION_INFO_SCSV (css: list cipherSuite) =
  List.Tot.mem (SCSV (TLS_EMPTY_RENEGOTIATION_INFO_SCSV)) css


// TODO: move all the definitions below to a separate file / figure out whether
// they belong here ?
//
// TODO: all occurrences of [pinverse] from there on have been replaced by calls
// to [pinverse_t]; we should write corresponding inversion lemmas.


(** Finite Field Diffie-Hellman group definitions *)
type ffdhe =
  | FFDHE2048
  | FFDHE3072
  | FFDHE4096
  | FFDHE6144
  | FFDHE8192

// BB.TODO: Document this !
let _FFz = 0xFFz // Workaround for #514

(** TLS 1.3 named groups for (EC)DHE key exchanges *)
type namedGroup =
  | SEC of CoreCrypto.ec_curve
  | EC_UNSUPPORTED of (b:byte{b <> 0x17z /\ b <> 0x18z /\ b <> 0x19z})
  | FFDHE of ffdhe
  | FFDHE_PRIVATE_USE of (b:byte{b = 0xFCz \/ b = 0xFDz \/ b = 0xFEz \/ b = _FFz})
  | ECDHE_PRIVATE_USE of byte

(** Definition of the configuration identifier *)
type configurationId = b:bytes{0 < length b /\ length b < 65536}

(** EarlyData type definition *)
type earlyDataType =
  | ClientAuthentication
  | EarlyData
  | ClientAuthenticationAndData

// TODO: replace with more precise types when available
(** Configuration Extension definition *)
noeq type configurationExtension =
  | UnknownConfigurationExtension:
      typ:lbytes 2 -> payload: bytes { repr_bytes (length payload) <= 2 } -> configurationExtension

(** Tuple Signature Algorithm and Hash Algorithm type definition *)
type sigHashAlg = sigAlg * hashAlg'
type sigScheme = 
  | SigHashAlg of sigHashAlg
  | RSA_PSS_SHA256
  | RSA_PSS_SHA384
  | RSA_PSS_SHA512
  | ED25519	
  | ED448

// TODO: replace "bytes" by either DH or ECDH parameters
(** KeyShare entry definition *)
type keyShareEntry = namedGroup * b:bytes{repr_bytes (length b) <= 2}

(** ClientKeyShare definition *)
type clientKeyShare = l:list keyShareEntry{List.Tot.length l < 65536/4}

(** ServerKeyShare definition *)
type serverKeyShare = keyShareEntry


(** KeyShare definition *)
noeq type keyShare =
  | ClientKeyShare of clientKeyShare
  | ServerKeyShare of serverKeyShare

// TODO: give more precise type

(** PSK Identity definition *)
type pskIdentity = b:bytes{repr_bytes (length b) <= 2}

(** Client list of PSK identities *)
type clientPreSharedKey = l:list pskIdentity{List.Tot.length l >= 1 /\ List.Tot.length l < 65536/2}

(** Server list of PSK identities *)
type serverPreSharedKey = pskIdentity

(** PreSharedKey definition *)
noeq type preSharedKey =
  | ClientPreSharedKey of clientPreSharedKey
  | ServerPreSharedKey of serverPreSharedKey

