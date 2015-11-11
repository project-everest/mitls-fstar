(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module MAC

open Bytes
open TLSConstants
open TLSInfo

type text = bytes
type tag = bytes

type key

val mac:    id -> key -> text -> tag
val verify: id -> key -> text -> tag -> bool

val gen: id -> key
val leak:   id -> key -> bytes
val coerce: id -> bytes -> key
