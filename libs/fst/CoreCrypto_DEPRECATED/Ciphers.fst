module CoreCrypto.Ciphers

(* -------------------------------------------------------------------- *)
open Platform.Bytes

type key = bytes
type iv  = bytes

assume val aes_cbc_encrypt : key -> iv -> bytes -> bytes
assume val aes_cbc_decrypt : key -> iv -> bytes -> bytes

assume val des3_cbc_encrypt : key -> iv -> bytes -> bytes
assume val des3_cbc_decrypt : key -> iv -> bytes -> bytes

type rc4engine

assume val rc4create  : key -> rc4engine
assume val rc4process : rc4engine -> bytes -> bytes

assume val aes_gcm_encrypt : key -> iv -> bytes -> bytes -> bytes
assume val aes_gcm_decrypt : key -> iv -> bytes -> bytes -> option bytes
