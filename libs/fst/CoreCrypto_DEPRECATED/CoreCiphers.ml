(* -------------------------------------------------------------------- *)
open Bytes
open CoreCrypto

(* -------------------------------------------------------------------- *)
type key = bytes
type iv  = bytes

(* -------------------------------------------------------------------- *)
let encrypt cipher omode key plain =
  let engine = blockcipher ForEncryption cipher omode (cbytes key) in
  abytes (engine.bc_process (cbytes plain))

(* -------------------------------------------------------------------- *)
let decrypt cipher omode key encrypted =
  let engine = CoreCrypto.blockcipher ForDecryption cipher omode (cbytes key) in
  abytes (engine.bc_process (cbytes encrypted))

(* -------------------------------------------------------------------- *)
let aes_cbc_encrypt key iv plain     = encrypt AES (Some (CBC (cbytes iv))) key plain
let aes_cbc_decrypt key iv encrypted = decrypt AES (Some (CBC (cbytes iv))) key encrypted

(* -------------------------------------------------------------------- *)
let des3_cbc_encrypt key iv plain     = encrypt DES3 (Some (CBC (cbytes iv))) key plain
let des3_cbc_decrypt key iv encrypted = decrypt DES3 (Some (CBC (cbytes iv))) key encrypted

(* -------------------------------------------------------------------- *)
type rc4engine = RC4Engine of streamcipher

let rc4create (key : key) =
  RC4Engine (CoreCrypto.streamcipher ForEncryption RC4 (cbytes key))

let rc4process (RC4Engine engine) (input : bytes) =
  abytes (engine.sc_process (cbytes input))

let aes_gcm_encrypt (key:key) (iv:iv) (ad:bytes) (plain:bytes) = failwith "unimplemented"
let aes_gcm_decrypt (key:key) (iv:iv) (ad:bytes) (plain:bytes) = failwith "unimplemented"