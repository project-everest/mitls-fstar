(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module Hashing

open Platform.Bytes
open CoreCrypto
open TLSConstants


(* Parametric hash algorithm (implements interface) *)
// FIXME: had to add a type annotation to make this go through
val hash': hashAlg -> bytes -> Tot bytes
let hash' alg data =
    match alg with
    | NULL    -> data
    | MD5SHA1 -> (CoreCrypto.hash MD5 data) @| (CoreCrypto.hash SHA1 data)
    | Hash h  -> (CoreCrypto.hash h  data)

// FIXME: same here
val hash: hashAlg -> bytes -> Tot bytes
let hash alg data =
  let h = hash' alg data in
  let l = length h in
    h
(*
  let exp = hashSize alg in
  if l = exp then h
  else Platform.Error.unexpected "CoreCrypto.Hash returned a hash of an unexpected size"
*)
