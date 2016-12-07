(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)
module Cert

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSFormats
open CoreCrypto

let endpoint_keytype (c:chain) : Tot (option CoreCrypto.key) =
  match c with
  | [] -> None
  | h::_ -> CoreCrypto.get_key_from_cert h


(* ------------------------------------------------------------------------ *)
(* JK: why is that necessary ? *)
(* SZ: proving that `chain` is a subtype of `list bytes` requires a positivity check *)
private let rec list_chain_is_list_bytes (c:chain) : Tot (list bytes) =
  match c with
  | [] -> []
  | hd::tl -> hd::(list_chain_is_list_bytes tl)

val validate_chain: chain -> bool -> option string -> string -> Tot bool
let validate_chain c for_signing host cafile =
  let c = list_chain_is_list_bytes c in
  CoreCrypto.validate_chain c for_signing host cafile

private val check_length: list bytes -> chain -> Tot (option chain)
let rec check_length cs acc =
  match cs with
  | [] -> Some (List.Tot.rev acc)
  | c::cs' ->
    if length c < 16777216 then check_length cs' (c::acc)
    else None

// TODO: we could retrieve sa from the subjectPublicKey field of
// the end certificate. We could also honor any hash algorithm
// specified in the params, if present.
val lookup_chain: pemfile:string -> Tot (result chain)
let lookup_chain pemfile =
  match CoreCrypto.load_chain pemfile with
  | Some chain ->
    begin
    match check_length chain [] with
    | Some chain -> Correct chain
    | None -> Error(AD_no_certificate, perror __SOURCE_FILE__ __LINE__ "cannot find suitable server certificate")
    end
  | None -> Error(AD_no_certificate, perror __SOURCE_FILE__ __LINE__ "cannot find suitable server certificate")
