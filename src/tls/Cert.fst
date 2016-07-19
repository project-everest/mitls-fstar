(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)
module Cert

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open CoreCrypto

type cert = b:bytes {length b <= 16777215}
type chain = list cert

(* ------------------------------------------------------------------------ *)

(* TODO: AR *)
assume HasEq_bytes: hasEq bytes

abstract val certificateListBytes: chain -> Tot bytes
let rec certificateListBytes l =
  match l with
  | [] -> empty_bytes
  | c::r -> 
    lemma_repr_bytes_values (length c);
    (vlbytes 3 c) @| (certificateListBytes r)

val certificateListBytes_is_injective: c1:chain -> c2:chain ->
  Lemma (Seq.equal (certificateListBytes c1) (certificateListBytes c2) ==> c1 == c2)
let rec certificateListBytes_is_injective c1 c2 =
  match c1, c2 with
  | [], [] -> ()
  | hd::tl, hd'::tl' ->
    if certificateListBytes c1 = certificateListBytes c2 then
      begin
      lemma_repr_bytes_values (length hd); lemma_repr_bytes_values (length hd');
      cut(Seq.equal ((vlbytes 3 hd) @| (certificateListBytes tl)) ((vlbytes 3 hd') @| (certificateListBytes tl')));
      lemma_repr_bytes_values (length hd);
      lemma_repr_bytes_values (length hd');
      cut(Seq.equal (Seq.slice (vlbytes 3 hd) 0 3) (Seq.slice (certificateListBytes c1) 0 3));
      cut(Seq.equal (Seq.slice (vlbytes 3 hd') 0 3) (Seq.slice (certificateListBytes c1) 0 3));
      vlbytes_length_lemma 3 hd hd';
      lemma_append_inj (vlbytes 3 hd) (certificateListBytes tl) (vlbytes 3 hd') (certificateListBytes tl');
      lemma_vlbytes_inj 3 hd hd';
      certificateListBytes_is_injective tl tl'
      end
  | [], hd::tl ->
    begin
    cut (length (certificateListBytes c1) = 0);
    lemma_repr_bytes_values (length hd);
    cut (Seq.equal (certificateListBytes c2) ((vlbytes 3 hd) @| (certificateListBytes tl)));
    lemma_vlbytes_len 3 hd
    end
  | hd::tl, [] ->
    begin
    cut (length (certificateListBytes c2) = 0);
    lemma_repr_bytes_values (length hd);
    cut (Seq.equal (certificateListBytes c1) ((vlbytes 3 hd) @| (certificateListBytes tl)));
    lemma_vlbytes_len 3 hd
    end

let endpoint_keytype (c:chain) : Tot (option CoreCrypto.key) =
  match c with
  | [] -> None
  | h::_ -> CoreCrypto.get_key_from_cert h

abstract val parseCertificateList: b:bytes -> Tot (result chain) (decreases (length b))
let rec parseCertificateList b =
  if length b >= 3 then
    match vlsplit 3 b with
    | Correct (c,r) ->
      cut (repr_bytes (length c) <= 3);
      let rl = parseCertificateList r in
      begin
      match rl with
      | Correct x -> (lemma_repr_bytes_values (length c); Correct (c::x))
      | e -> e
      end
    | _ -> Error(AD_bad_certificate_fatal, perror __SOURCE_FILE__ __LINE__ "Badly encoded certificate list")
  else if length b = 0 then Correct []
  else Error(AD_bad_certificate_fatal, perror __SOURCE_FILE__ __LINE__ "Badly encoded certificate list")

val lemma_parseCertificateList_length: b:bytes -> 
  Lemma (ensures (match parseCertificateList b with
		  | Correct ces -> length (certificateListBytes ces) = length b
		  | _ -> True))
	(decreases (length b))
let rec lemma_parseCertificateList_length b = 
  match parseCertificateList b with
  | Correct [] -> ()
  | Correct (hd::tl) ->
    begin
    cut(length b >= 3);
    match vlsplit 3 b with
    | Correct (c, r) -> lemma_parseCertificateList_length r
    | _ -> ()
    end
  | Error _ -> ()


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
