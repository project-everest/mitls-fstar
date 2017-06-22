module Crypto.Indexing

open TLSInfo

module CC = CoreCrypto

type rw =
  | Reader
  | Writer

let rw2rw = function
  | TLSConstants.Reader -> Reader
  | TLSConstants.Writer -> Writer

type macAlg =
  | POLY1305
  | GHASH

type cipherAlg =
  | AES128
  | AES256
  | CHACHA20

type aeadAlg =
  | AES_128_GCM
  | AES_256_GCM
  | CHACHA20_POLY1305

type aesImpl =
  | ValeAES
  | HaclAES

(**
miTLS-compatible definitions for running the low-level
record stack.

(see mitls-fstar/.fstar/examples/low-level/crypto/Crypto.Indexing.fst)
**)

type id =
  i:TLSInfo.id{~(PlaintextID? i) /\ TLSConstants.AEAD? (aeAlg_of_id i)}

let aeadAlg_of_id (i:id) =
  let TLSConstants.AEAD a _ = aeAlg_of_id i in
  match a with
  | CC.AES_128_GCM -> AES_128_GCM
  | CC.AES_256_GCM -> AES_256_GCM
  | CC.CHACHA20_POLY1305 -> CHACHA20_POLY1305
  | _ -> admit()

let macAlg_of_id (i:id) =
  match aeadAlg_of_id i with
  | AES_128_GCM       -> GHASH
  | AES_256_GCM       -> GHASH
  | CHACHA20_POLY1305 -> POLY1305

let cipherAlg_of_id (i:id) =
  match aeadAlg_of_id i with
  | AES_128_GCM       -> AES128
  | AES_256_GCM       -> AES256
  | CHACHA20_POLY1305 -> CHACHA20

let aesImpl_of_id (i:id) = ValeAES

let aeadAlg_cipherAlg (i:id) : Lemma
  (requires True)
  (ensures
    ((aeadAlg_of_id i == AES_128_GCM ==> cipherAlg_of_id i == AES128) /\
     (aeadAlg_of_id i == AES_256_GCM ==> cipherAlg_of_id i == AES256) /\
     (aeadAlg_of_id i == CHACHA20_POLY1305 ==> cipherAlg_of_id i == CHACHA20)))
  = ()

let testId (a:aeadAlg) = admit()
