open Bytes

type key = bytes
type iv  = bytes

val aes_cbc_encrypt : key -> iv -> bytes -> bytes
val aes_cbc_decrypt : key -> iv -> bytes -> bytes

val des3_cbc_encrypt : key -> iv -> bytes -> bytes
val des3_cbc_decrypt : key -> iv -> bytes -> bytes

type rc4engine

val rc4create  : key -> rc4engine
val rc4process : rc4engine -> bytes -> bytes
