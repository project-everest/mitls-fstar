(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module HASH

open Platform.Bytes
open CoreCrypto
open TLSConstants

(* Parametric hash algorithm (implements interface) *)
let hash' alg data =
    match alg with
    | NULL    -> data
    | MD5SHA1 -> (CoreCrypto.hash MD5 data) @| (CoreCrypto.hash SHA1 data)
    | Hash h  -> (CoreCrypto.hash h  data)

let hash alg data =
  let h = hash' alg data in
  let l = length h in
  let exp = hashSize alg in
  if l = exp then h
  else Platform.Error.unexpected "CoreCrypto.Hash returned a hash of an unexpected size"
