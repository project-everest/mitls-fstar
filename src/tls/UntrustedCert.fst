(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module UntrustedCert

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants

val oid_RSAEncryption : string
let oid_RSAEncryption = ""
val oid_SHAWithRSAEncryption : string
let oid_SHAWithRSAEncryption = ""
val oid_SHA256WithRSAEncryption : string
let oid_SHA256WithRSAEncryption = ""
val oid_DSASignatureKey : string
let oid_DSASignatureKey = ""

val oid_of_keyalg: sigAlg -> string
let oid_of_keyalg salg = ""

type X509Certificate2
type hint = string
type cert = b:bytes{length b < 65536}
type chain = l:list cert{List.length l < 4}

val x509_is_for_signing: X509Certificate2 -> bool
let x509_is_for_signing x = failwith "Not implemented"

val x509_verify: X509Certificate2 -> bool
let x509_verify x = failwith "Not implemented"

val x509_chain: X509Certificate2 -> list X509Certificate2
let x509_chain x = failwith "Not implemented"

val x509_check_key_sig_alg_one: list Sig.alg -> X509Certificate2 -> bool
let x509_check_key_sig_alg_one l x = failwith "Not implemented"

val x509_to_secret_key: X509Certificate2 -> option Sig.skey
val x509_to_public_key: X509Certificate2 -> option Sig.pkey
let x509_to_secret_key x = failwith "Not implemented"
let x509_to_public_key x = failwith "Not implemented"

val x509_is_for_key_encryption: X509Certificate2 -> bool
let x509_is_for_key_encryption x = failwith "Not implemented"

val x509_export_public: X509Certificate2 -> bytes
let x509_export_public x = failwith "Not implemented"

val cert_to_x509: cert -> option X509Certificate2
let cert_to_x509 c = failwith "Not implemented"

val chain_to_x509list: chain -> option (list X509Certificate2)
let chain_to_x509list c  = failwith "Not implemented"

val x509list_to_chain: list X509Certificate2 -> chain
let x509list_to_chain l = failwith "Not implemented"

(* First argument (list Sig.alg>) gives the allowed signing alg. used for
 * signing the keys of the chain.
 *)

val validate_x509_chain: list Sig.alg -> chain -> bool
let validate_x509_chain l c  = failwith "Not implemented"

val validate_x509list: X509Certificate2 -> list X509Certificate2 -> bool
let validate_x509list x l = failwith "Not implemented"

val is_for_signing:        cert -> bool
let is_for_signing c = failwith "Not implemented"
val is_for_key_encryption: cert -> bool
let is_for_key_encryption c = failwith "Not implemented"

val find_sigcert_and_alg: list Sig.alg -> hint -> list Sig.alg -> option (X509Certificate2 * Sig.alg)
let find_sigcert_and_alg l h l2 = failwith "Not implemented"

val find_enccert: list Sig.alg -> hint -> option X509Certificate2
let find_enccert l h = failwith "Not implemented"

val get_chain_key_algorithm: chain -> option sigAlg
let get_chain_key_algorithm c = failwith "Not implemented"

val get_name_info: X509Certificate2 -> string
let get_name_info x = failwith "Not implemented"
