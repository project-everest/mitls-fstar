(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)
module Cert

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants

type hint = string
type cert = b:bytes {length b <= 16777215}
type chain = list cert

abstract val certificateListBytes: chain -> Tot bytes
let rec certificateListBytes l =
  match l with
  | [] -> empty_bytes
  | c::r -> (vlbytes 3 c) @| (certificateListBytes r)

abstract val parseCertificateList: bytes -> Tot (result chain)
let rec parseCertificateList b =
  if length b >= 3 then
    match vlsplit 3 b with
    | Correct (c,r) ->
        let rl = parseCertificateList r in
        (match rl with
        | Correct x -> Correct (c::x)
        | e -> e)
    | _ -> Error(AD_bad_certificate_fatal, perror __SOURCE_FILE__ __LINE__ "Badly encoded certificate list")
  else Correct []

val validate_chain : chain -> option sigAlg -> option string -> string -> Tot bool
let validate_chain c sigalg host cafile =
  let for_signing = match sigalg with | None -> false | _ -> false in
  CoreCrypto.validate_chain c for_signing host cafile

val verify_signature : chain -> protocolVersion -> bytes -> sigAlg -> option (list sigHashAlg) -> bytes -> bytes -> Tot bool
let verify_signature c pv nonces_or_log csa sigalgs tbs sigv =
  match pv with
  | TLS_1p0 | TLS_1p1 | TLS_1p2 ->
    if length sigv > 2 then
     let (h, r) = split sigv 1 in
     let (sa, sigv) = split r 1 in
     // TLS <= 1.2: sign cr+sr+ServerDHPArams
     let tbs = nonces_or_log @| tbs in
     (match (parseSigAlg sa, parseHashAlg h) with
     | Correct sa, Correct (Hash h) ->
        let algs : list sigHashAlg =
          match sigalgs with
          | Some l -> l
          | None -> [(sa, Hash CoreCrypto.SHA1)] in
        if List.Tot.existsb (fun (xs,xh)->(xs=sa && xh=Hash h)) algs then
          CoreCrypto.cert_verify_sig (List.Tot.hd c) sa h tbs sigv
        else false
     | _ -> false)
    else false
  | _ -> false // TODO!!

(*
type sign_cert = option (chain * Sig.alg * Sig.skey)
type enc_cert  = option (chain * RSAKey.sk)

abstract val for_signing : list Sig.alg -> hint -> list Sig.alg -> sign_cert
let for_signing l h l2 = failwith "Not implemented"

abstract val for_key_encryption : list Sig.alg -> hint -> enc_cert
let for_key_encryption l h = failwith "Not implemented"

abstract val get_public_signing_key : cert -> Sig.alg -> result Sig.pkey
let get_public_signing_key c a = failwith "Not implemented"

abstract val get_public_encryption_key : cert -> result RSAKey.pk
let get_public_encryption_key c = failwith "Not implemented"

abstract val get_chain_public_signing_key : chain -> Sig.alg -> result Sig.pkey
let get_chain_public_signing_key c a = failwith "Not implemented"

abstract val get_chain_public_encryption_key : chain -> result RSAKey.pk
let get_chain_public_encryption_key c = failwith "Not implemented"

abstract val is_chain_for_signing : chain -> bool
let is_chain_for_signing c = failwith "Not implemented"

abstract val is_chain_for_key_encryption : chain -> bool
let is_chain_for_key_encryption c = failwith "Not implemented"

abstract val get_hint : chain -> option hint
let get_hint c = failwith "Not implemented"

abstract val validate_cert_chain : list Sig.alg  -> chain -> bool
let validate_cert_chain l c = failwith "Not implemented"
*)
