(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module Bytes

type nat = int 
type cbytes = byte[]
[<NoComparison>]
type bytes
type lbytes = bytes
val empty_bytes: bytes
val abytes: byte[] -> bytes
val abyte: byte -> bytes
val abyte2: (byte * byte) -> bytes
val cbytes: bytes -> byte[]
val cbyte: bytes -> byte
val cbyte2: bytes -> byte * byte 

val createBytes: int -> int -> bytes

val bytes_of_int: int -> int -> bytes

val int_of_bytes: bytes -> int

val length: bytes -> int

val equalBytes: bytes -> bytes -> bool
val xor: bytes -> bytes -> int -> bytes

(* append *)
val (@|): bytes -> bytes -> bytes
val split: bytes -> int -> (bytes * bytes)
val split2: bytes -> int -> int -> (bytes * bytes * bytes)
(* strings *)
val utf8: string -> bytes
val iutf8: bytes -> string

val hexString: bytes -> string
