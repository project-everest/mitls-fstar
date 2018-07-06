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

type aead_id (i:Idx.id) =
  Idx.Derive? i /\
  (let Idx.Derive _ _ ctx = i in
  Idx.ExpandLog? ctx /\
  ~(TLSInfo.LogInfo_CH? (Idx.ExpandLog?.info ctx)))

type id = i:Idx.id{aead_id i}

let aeadAlg_of_id (i:id) : GTot aeadAlg =
  let Idx.Derive _ _ (Idx.ExpandLog info _) = i in
  match TLSInfo.logInfo_ae info with
  | CC.AES_128_GCM -> AES_128_GCM
  | CC.AES_256_GCM -> AES_256_GCM
  | CC.CHACHA20_POLY1305 -> CHACHA20_POLY1305
  | _ -> admit()

let macAlg_of_aeadAlg = function
  | AES_128_GCM       -> GHASH
  | AES_256_GCM       -> GHASH
  | CHACHA20_POLY1305 -> POLY1305
  
let macAlg_of_id (i:id) : GTot macAlg =
  macAlg_of_aeadAlg (aeadAlg_of_id i)

let cipherAlg_of_aeadAlg = function
  | AES_128_GCM       -> AES128
  | AES_256_GCM       -> AES256
  | CHACHA20_POLY1305 -> CHACHA20

let cipherAlg_of_id (i:id) : GTot cipherAlg =
  cipherAlg_of_aeadAlg (aeadAlg_of_id i)
  
let aesImpl_of_id (i:id) = ValeAES

let aeadAlg_cipherAlg (i:id) : Lemma
  (requires True)
  (ensures
    ((aeadAlg_of_id i == AES_128_GCM ==> cipherAlg_of_id i == AES128) /\
     (aeadAlg_of_id i == AES_256_GCM ==> cipherAlg_of_id i == AES256) /\
     (aeadAlg_of_id i == CHACHA20_POLY1305 ==> cipherAlg_of_id i == CHACHA20)))
  = ()

private let name_convert = function
  | AES_128_GCM -> CC.AES_128_GCM
  | AES_256_GCM -> CC.AES_256_GCM
  | CHACHA20_POLY1305 -> CC.CHACHA20_POLY1305

let testId (a:aeadAlg) =
  assume false;
  Idx.Derive (Idx.Preshared Hashing.Spec.SHA256 0) "test"
    (Idx.ExpandLog (LogInfo_CH0 ({li_ch0_cr = Bytes.create 32ul 0uy; li_ch0_ed_psk = Bytes.empty_bytes; li_ch0_ed_ae = (name_convert a); li_ch0_ed_hash = Hashing.Spec.SHA256})) Bytes.empty_bytes)
