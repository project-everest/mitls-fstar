(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module ENC

open Bytes
open TLSInfo

type state
type encryptor = state
type decryptor = state

val gen:    id -> encryptor * decryptor
val leak:   id -> rw -> state -> bytes * bytes
val coerce: id -> rw -> bytes -> bytes-> state

type cipher = bytes

val enc: id -> encryptor -> LHAEPlain.adata -> Range.range -> Encode.plain -> (encryptor * cipher)
val dec: id -> decryptor -> LHAEPlain.adata -> cipher -> (decryptor * Encode.plain)

