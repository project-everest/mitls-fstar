(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module HSFragment
open Bytes
open TLSInfo
open Range
open Error
open TLSError

type stream

type fragment
type plain = fragment

val fragmentRepr: id -> range -> fragment -> bytes
val fragmentPlain: id -> range -> bytes -> fragment

val extend: id -> stream -> range -> fragment -> stream
val init: id -> stream

val reStream: id -> stream -> range -> plain -> stream -> plain

val makeExtPad:  id -> range -> fragment -> fragment
val parseExtPad: id -> range -> fragment -> Result<fragment>

#if ideal
val widen: id -> range -> range -> fragment -> fragment
#endif

 
