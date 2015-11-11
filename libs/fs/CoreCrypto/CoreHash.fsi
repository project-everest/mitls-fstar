(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module CoreHash
open Bytes

type engine

val name   : engine -> string
val digest : engine -> bytes -> bytes

val md5engine    : unit -> engine
val sha1engine   : unit -> engine
val sha256engine : unit -> engine
val sha384engine : unit -> engine
val sha512engine : unit -> engine

val md5    : bytes -> bytes
val sha1   : bytes -> bytes
val sha256 : bytes -> bytes
val sha384 : bytes -> bytes
val sha512 : bytes -> bytes
