(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)
module RSAKey

module HS = FStar.HyperStack //Added automatically

open FStar.Bytes
open FStar.HyperStack.All

module TC = TLSConstants

type pk = bytes
type sk = bytes

type pred = | SK_PK of sk * pk

(* TODO: use the following to idealize *)
//let honest_log = FStar.Error.if_ideal (fun _ -> ref [])

//let honest (pk:pk): bool = failwith "only used in ideal implementation, unverified"
let honest (pk:pk): bool = false

//let strong (pv:TLSConstants.protocolVersion): bool = failwith "only used in ideal implementation, unverified"
let strong (pv:TC.protocolVersion): bool = false


type modulus  = bytes
type exponent = bytes

let gen () : ML (pk * sk) = admit()
(* Removed as CoreCrypto is deprecated
    let sk = CoreCrypto.rsa_gen_key 2048 in
    let pk = {sk with rsa_prv_exp = None} in
    pk, sk
*)

let coerce (k:pk) (s:bytes) = s

let repr_of_rsapkey (p) = p
let repr_of_rsaskey (s) = s

let create_rsapkey ((m, e) : modulus * exponent) =
  empty_bytes, empty_bytes
  //{rsa_mod = m; rsa_pub_exp = e; rsa_prv_exp = None}
