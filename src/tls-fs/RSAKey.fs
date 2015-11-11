(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"


module RSAKey


open Bytes

type pk = { pk : CoreACiphers.pk }
type sk = { sk : CoreACiphers.sk }

type pred = | SK_PK of sk * pk

(* TODO: use the following to idealize *)
let honest_log = Error.if_ideal (fun _ -> ref [])
let honest (pk:pk): bool = failwith "only used in ideal implementation, unverified"
let strong (pv:TLSConstants.ProtocolVersion): bool = failwith "only used in ideal implementation, unverified"

type modulus  = bytes
type exponent = bytes

let gen () : (pk * sk) =
    let csk, cpk = CoreACiphers.gen_key () in
    let sk = {sk = csk} in
    let pk = {pk = cpk} in
(*
    assume(SK_PK(sk,pk));
*)
    pk, sk 

let coerce (pk:pk) (csk:CoreACiphers.sk) = 
    let sk= {sk = csk} in
(*
    assume(SK_PK(sk,pk));
*)
    sk

let repr_of_rsapkey ({ pk = pk }) = pk
let repr_of_rsaskey ({ sk = sk }) = sk

let create_rsapkey ((m, e) : modulus * exponent) = { pk = CoreACiphers.RSAPKey(m, e) } 
//let create_rsaskey ((m, e) : modulus * exponent) = { sk = CoreACiphers.RSASKey(m, e) }
