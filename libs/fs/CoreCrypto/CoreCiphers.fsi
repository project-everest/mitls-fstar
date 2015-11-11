(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module CoreCiphers
open Bytes

type key   = bytes
type iv    = bytes
type adata = bytes

val aes_cbc_encrypt : key -> iv -> bytes -> bytes
val aes_cbc_decrypt : key -> iv -> bytes -> bytes

val aes_gcm_encrypt : key -> iv -> adata -> bytes -> bytes
val aes_gcm_decrypt : key -> iv -> adata -> bytes -> bytes option

val des3_cbc_encrypt : key -> iv -> bytes -> bytes
val des3_cbc_decrypt : key -> iv -> bytes -> bytes

type rc4engine

val rc4create  : key -> rc4engine
val rc4process : rc4engine -> bytes -> bytes
