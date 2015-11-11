(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module StatefulLHAE

open Bytes
open Error
open TLSError
open TLSInfo
open Range
open StatefulPlain 

type state
type reader = state
type writer = state

val gen:     id -> reader * writer
val coerce:  id -> rw -> bytes -> state
val leak:    id -> rw -> state -> bytes

val history: id -> rw -> state -> history

type cipher = LHAE.cipher

val encrypt: id -> writer ->  adata -> range -> plain -> (writer * cipher)
val decrypt: id -> reader ->  adata -> cipher -> Result<(reader * range * plain)>
