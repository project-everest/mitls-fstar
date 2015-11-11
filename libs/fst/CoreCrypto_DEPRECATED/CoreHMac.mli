(* -------------------------------------------------------------------- *)
open Bytes

type engine
type key = bytes

val name   : engine -> string
val mac    : engine -> bytes -> bytes

val md5engine    : key -> engine
val sha1engine   : key -> engine
val sha256engine : key -> engine
val sha384engine : key -> engine
val sha512engine : key -> engine

val md5    : key -> bytes -> bytes
val sha1   : key -> bytes -> bytes
val sha256 : key -> bytes -> bytes
val sha384 : key -> bytes -> bytes
val sha512 : key -> bytes -> bytes
