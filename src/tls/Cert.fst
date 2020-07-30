(* Copyright (C) 2012--2018 Microsoft Research and INRIA *)
module Cert

open FStar.Bytes

open TLS.Result
open TLSConstants
open Parse

let certificateListBytes c = certificate12_serializer32 c

let certificateListBytes13 c = certificate13_certificate_list_serializer32 c

let certificateListBytes_is_injective c1 c2 = admit() // LowParserWrappers

let certificateListBytes13_is_injective c1 c2 = admit()

let parseCertificateList b =
  [@inline_let] let _ = assume (FStar.Bytes.repr_bytes (FStar.Bytes.length b) <= 3) in
  let err = perror __SOURCE_FILE__ __LINE__ "bad certificate 1.2 chain" in
  LowParseWrappers.wrap_parser32 certificate12_parser32 err (vlbytes 3 b)

let parseCertificateList13 b =
  let err = perror __SOURCE_FILE__ __LINE__ "bad certificate 1.3 chain" in
  LowParseWrappers.wrap_parser32 certificate13_certificate_list_parser32 err b
  
let lemma_parseCertificateList_length b = admit()
