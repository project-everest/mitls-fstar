(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module MAC_SHA1

open Bytes
open TLSConstants
open TLSInfo

val a: macAlg
type text = bytes
type tag = bytes

type key

val mac:    id -> key -> text -> tag
val verify: id -> key -> text -> tag -> bool

val gen: id -> key
