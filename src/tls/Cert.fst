(* Copyright (C) 2012--2018 Microsoft Research and INRIA *)
module Cert

open FStar.Bytes

open TLS.Result
open TLSConstants
open Parse
 
(* The chain format changes between TLS 1.2 and TLS 1.3; we separate
then in messages, but at least for now, we merge the two in
Negotiation and in the main TLS API (with no extensions when using TLS
1.2 *)

include Parsers.Certificate13
include Parsers.CertificateEntry13
include Parsers.Certificate13_certificate_list

include Parsers.Certificate12
include Parsers.ASN1Cert

type cert = aSN1Cert
type certes = certificateEntry13

type chain = certificate12
type chain13 = certificate13_certificate_list

// we may use these types to keep track of un-extended chains,
// e.g. to prove that their formatting is injective
let is_classic_chain_aux (ces:certes) = List.Tot.isEmpty (ces.extensions)
let is_classic_chain (l:chain13): bool =
  List.Tot.for_all #certes is_classic_chain_aux l
type chain12 = l:chain13 {is_classic_chain l}

// 2018.03.10 SZ: The types in Extensions.fsti are too weak to prove the refinement in [certes]
#set-options "--admit_smt_queries true"
let chain_up_aux (c:cert) : certes = {cert_data = c; extensions=[]}
let chain_up (l:chain) : chain13 = List.Tot.map #cert #certes chain_up_aux l
let chain_down_aux (c:certes) : cert = c.cert_data
let chain_down (l:chain13): chain = List.Tot.map #certes #cert chain_down_aux l
#reset-options

(* ------------------------------------------------------------------------ *)

abstract val certificateListBytes: chain -> Tot bytes
let certificateListBytes c = certificate12_serializer32 c

abstract val certificateListBytes13: chain13 -> Tot bytes
let certificateListBytes13 c = certificate13_certificate_list_serializer32 c

val certificateListBytes_is_injective: c1:chain -> c2:chain ->
  Lemma (Bytes.equal (certificateListBytes c1) (certificateListBytes c2) ==> c1 == c2)

#set-options "--admit_smt_queries true"
let rec certificateListBytes_is_injective c1 c2 = admit() // LowParserWrappers
#reset-options

val certificateListBytes13_is_injective: c1:chain13 -> c2:chain13 ->
  Lemma (Bytes.equal (certificateListBytes13 c1) (certificateListBytes13 c2) ==> c1 == c2)
let rec certificateListBytes13_is_injective c1 c2 = admit()

abstract val parseCertificateList: b:bytes -> Tot (result chain) (decreases (length b))
let parseCertificateList b =
  [@inline_let] let _ = assume (FStar.Bytes.repr_bytes (FStar.Bytes.length b) <= 3) in
  let err = perror __SOURCE_FILE__ __LINE__ "bad certificate 1.2 chain" in
  LowParseWrappers.wrap_parser32 certificate12_parser32 err (vlbytes 3 b)

abstract val parseCertificateList13: b:bytes -> Tot (result chain13) (decreases (length b))
let parseCertificateList13 b =
  let err = perror __SOURCE_FILE__ __LINE__ "bad certificate 1.3 chain" in
  LowParseWrappers.wrap_parser32 certificate13_certificate_list_parser32 err b
  
val lemma_parseCertificateList_length: b:bytes ->
  Lemma (ensures (match parseCertificateList b with
      | Correct ces -> length (certificateListBytes ces) == length b
      | _ -> True))
  (decreases (length b))
let rec lemma_parseCertificateList_length b = admit()
