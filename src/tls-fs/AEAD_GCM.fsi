(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module AEAD_GCM

open Bytes
open TLSInfo
open Range
open TLSError

type cipher = bytes
type state
type encryptor = state
type decryptor = state

val gen: id -> encryptor * decryptor
val coerce: id -> rw -> bytes -> bytes -> state
val leak: id -> rw -> state -> bytes

val enc: id -> encryptor -> LHAEPlain.adata -> range -> 
  LHAEPlain.plain -> (encryptor * bytes)

val dec: id -> decryptor -> LHAEPlain.adata -> range -> 
  bytes -> Result<(decryptor * LHAEPlain.plain)>
