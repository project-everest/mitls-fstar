(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module HASH

open Bytes
open TLSConstants
//open Seq 

(* Parametric hash algorithm (implements interface) *)
let hash' alg data =
    match alg with
    | NULL    -> data
    | MD5SHA1 -> (CoreHash.md5 data) @| (CoreHash.sha1 data)
    | MD5     -> (CoreHash.md5    data)
    | SHA     -> (CoreHash.sha1   data)
    | SHA256  -> (CoreHash.sha256 data)
    | SHA384  -> (CoreHash.sha384 data)

let hash alg data = 
  let h = hash' alg data in
  let l = length h in
  let exp = hashSize alg in
  if l = exp then h 
  else Error.unexpected "CoreHash returned a hash of an unexpected size"
