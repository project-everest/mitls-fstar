(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module RSAKey
open CoreCrypto

open Platform.Bytes

type pk = (k:CoreCrypto.rsa_key{None? k.rsa_prv_exp})
type sk = CoreCrypto.rsa_key

type pred = | SK_PK of sk * pk

//let honest_log = Platform.Error.if_ideal (fun _ -> ref [])
let honest (pk:pk): bool = failwith "only used in ideal implementation, unverified"
let strong (pv:TLSConstants.protocolVersion): bool = failwith "only used in ideal implementation, unverified"

type modulus  = bytes
type exponent = bytes

let gen () : (pk * sk) =
    let sk = CoreCrypto.rsa_gen_key 2048 in
    let pk = {sk with rsa_prv_exp = None} in
    pk, sk

let coerce (k:pk) (s:CoreCrypto.rsa_key) =
    s

let repr_of_rsapkey (p) = p
let repr_of_rsaskey (s) = s

let create_rsapkey ((m, e) : modulus * exponent) = {rsa_mod = m; rsa_pub_exp = e; rsa_prv_exp = None}
