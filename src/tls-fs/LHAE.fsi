(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module LHAE

open Bytes
open Error
open TLSError
open TLSInfo
open LHAEPlain
open Range

type LHAEKey
type encryptor = LHAEKey
type decryptor = LHAEKey

type cipher = bytes

val gen:     id -> encryptor * decryptor
val coerce:  id -> rw -> bytes -> LHAEKey
val leak:    id -> rw -> LHAEKey -> bytes

val encrypt: id -> encryptor -> adata -> range -> plain -> (encryptor * cipher)
val decrypt: id -> decryptor -> adata -> cipher -> Result<(decryptor * range * plain)>
