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

abstract val parseCertificateList: bytes -> Tot (result chain)
// Dummy implementation while certificate parsing is not implemented
let parseCertificateList b = Correct ([b]) //TODO: known to be unverified

abstract val certificateListBytes: chain -> Tot (b:bytes{length b < (op_Multiply 3 65536)})
let certificateListBytes c = magic()
