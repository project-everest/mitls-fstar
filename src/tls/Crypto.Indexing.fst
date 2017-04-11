module Crypto.Indexing

open TLSInfo

module CC = CoreCrypto

(**
miTLS-compatible definitions for running the low-level
record stack.

(see mitls-fstar/.fstar/examples/low-level/crypto/Crypto.Indexing.fst)
**)

let rw2rw (r:TLSConstants.rw) : rw =
  match r with
  | TLSConstants.Reader -> Reader
  | TLSConstants.Writer -> Writer

type id0 =
  i:TLSInfo.id{~(PlaintextID? i) /\ TLSConstants.AEAD? (aeAlg_of_id i)}
let id = id0

let aeadAlg_of_id i =
  let TLSConstants.AEAD aead _ = aeAlg_of_id i in
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

let aesImpl_of_id (i:id) = ValeAES

let aeadAlg_cipherAlg (i:id) = ()

let testId (a:aeadAlg) = admit()

