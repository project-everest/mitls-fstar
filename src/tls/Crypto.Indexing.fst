module Crypto.Indexing

open TLSConstants
open TLSInfo
open CoreCrypto

module CC = CoreCrypto

(**
miTLS-compatible definitions for running the low-level
record stack.

(see mitls-fstar/.fstar/examples/low-level/crypto/Crypto.Indexing.fst)
**)
type rw =
| Reader
| Writer

let rw2rw (r:TLSConstants.rw) : rw =
  match r with
  | TLSConstants.Reader -> Reader
  | TLSConstants.Writer -> Writer

type macAlg =
  | POLY1305
  | GHASH

type cipherAlg =
  | AES128
  | AES256
  | CHACHA20

type aesImpl =
  | SpartanAES
  | HaclAES

// References:
//  - RFC 7539 for the AEAD algorithm
//  - RFC 7905 for ChaCha20_Poly1305 TLS ciphersuites
type aeadAlg =
  | AES_128_GCM
  | AES_256_GCM
  | CHACHA20_POLY1305

type id =
  i:TLSInfo.id{~(is_PlaintextID i) /\ is_AEAD (aeAlg_of_id i)}

// ADL: TODO support in TLSInfo.id + mitls.exe
let aesImpl_of_id (i:id) = SpartanAES

let aeadAlg_of_id i =
  let AEAD aead _ = aeAlg_of_id i in
  match aead with
  | CC.AES_128_GCM -> AES_128_GCM
  | CC.AES_256_GCM -> AES_256_GCM
  | CC.CHACHA20_POLY1305 -> CHACHA20_POLY1305

let macAlg_of_id i =
  match aeadAlg_of_id i with
  | AES_128_GCM       -> GHASH
  | AES_256_GCM       -> GHASH
  | CHACHA20_POLY1305 -> POLY1305

let cipherAlg_of_id i =
  match aeadAlg_of_id i with
  | AES_128_GCM       -> AES128
  | AES_256_GCM       -> AES256
  | CHACHA20_POLY1305 -> CHACHA20

// controls abstraction of plaintexts
// (kept abstract, but requires all the crypto steps above)
let safeId = TLSInfo.safeId


