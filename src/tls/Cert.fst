(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)
module Cert

open Platform.Bytes
open Platform.Error
open TLSError

type hint = UntrustedCert.hint
type cert = UntrustedCert.cert
type chain = UntrustedCert.chain

type sign_cert = option (chain * Sig.alg * Sig.skey)
type enc_cert  = option (chain * RSAKey.sk)

val for_signing : list Sig.alg -> hint -> list Sig.alg -> sign_cert
let for_signing l h l2 = failwith "Not implemented"
val for_key_encryption : list Sig.alg -> hint -> enc_cert
let for_key_encryption l h = failwith "Not implemented"

val get_public_signing_key : cert -> Sig.alg -> Result Sig.pkey
let get_public_signing_key c a = failwith "Not implemented"

val get_public_encryption_key : cert -> Result RSAKey.pk
let get_public_encryption_key c = failwith "Not implemented"

val get_chain_public_signing_key : chain -> Sig.alg -> Result Sig.pkey
val get_chain_public_encryption_key : chain -> Result RSAKey.pk
let get_chain_public_signing_key c a = failwith "Not implemented"
let get_chain_public_encryption_key c = failwith "Not implemented"

val is_chain_for_signing : chain -> bool
val is_chain_for_key_encryption : chain -> bool
let is_chain_for_signing c = failwith "Not implemented"
let is_chain_for_key_encryption c = failwith "Not implemented"

val get_hint : chain -> option hint
val validate_cert_chain : list Sig.alg  -> chain -> bool
val parseCertificateList: bytes -> Result chain
val certificateListBytes: chain -> Tot (b:bytes{length b < (3 * 65536)})
let get_hint c = failwith "Not implemented"
let validate_cert_chain l c = failwith "Not implemented"
let parseCertificateList b = failwith "Not implemented"
let certificateListBytes c = magic()
