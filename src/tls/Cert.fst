(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)
module Cert

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open CoreCrypto

// CertificateEntry in https://tlswg.github.io/tls13-spec/#rfc.section.4.4.2
//17-05-04  we miss some length bounds and extensions (presumed empty for now)

type cert = b:bytes {length b <= 16777215 } 
type chain = list (list extension * cert)

(* ------------------------------------------------------------------------ *)

abstract val certificateListBytes: protocolVersion -> chain -> Tot bytes
let rec certificateListBytes pv = function
  | [] -> empty_bytes
  | c::r -> 
    lemma_repr_bytes_values (length c);
    if pv = TLSConstants.TLS_1p3 then (
      lemma_repr_bytes_values 0;
      vlbytes 3 c @| (vlbytes 2 empty_bytes @| certificateListBytes pv r))
    else (
      vlbytes 3 c @| certificateListBytes pv r)
    

val certificateListBytes_is_injective: pv:protocolVersion -> c1:chain -> c2:chain ->
  Lemma (Seq.equal (certificateListBytes pv c1) (certificateListBytes pv c2) ==> c1 == c2)
let rec certificateListBytes_is_injective pv c1 c2 =
  let b1 = certificateListBytes pv c1 in
  let b2 = certificateListBytes pv c2 in
  match c1, c2 with
  | [], [] -> ()
  | hd::tl, hd'::tl' ->
    if b1 = b2 then
      begin
      lemma_repr_bytes_values (length hd);
      lemma_repr_bytes_values (length hd');
      lemma_repr_bytes_values 0;
      assert(Seq.equal (Seq.slice (vlbytes 3 hd) 0 3) (Seq.slice b1 0 3));
      assert(Seq.equal (Seq.slice (vlbytes 3 hd') 0 3) (Seq.slice b1 0 3));
      vlbytes_length_lemma 3 hd hd';
      // TLS 1p3
      lemma_append_inj (vlbytes 3 hd)  (vlbytes 2 empty_bytes @| certificateListBytes pv tl) (vlbytes 3 hd') (vlbytes 2 empty_bytes @| certificateListBytes pv tl');
      lemma_append_inj (vlbytes 2 empty_bytes) (certificateListBytes pv tl) (vlbytes 2 empty_bytes) (certificateListBytes pv tl');
      lemma_vlbytes_inj 3 hd hd';
      // TLS classic
      lemma_append_inj (vlbytes 3 hd) (certificateListBytes pv tl) (vlbytes 3 hd') (certificateListBytes pv tl');
      certificateListBytes_is_injective pv tl tl';
      assert(c1 == c2)
      end
  | [], hd::tl ->
    begin
    assert_norm (length b1 == 0);
    lemma_repr_bytes_values (length hd);
    lemma_repr_bytes_values 0;
    lemma_vlbytes_len 3 hd;
    assert(c1 == c2)

    end
  | hd::tl, [] ->
    begin
    assert_norm (length b2 == 0);
    lemma_repr_bytes_values (length hd);
    lemma_repr_bytes_values 0;
    lemma_vlbytes_len 3 hd;
    assert (c1 == c2)
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
      begin
      cut (repr_bytes (length c) <= 3);
      if length r >= 2 then
        match vlsplit 2 r with
        | Correct (e,r) ->
          let rl = parseCertificateList r in
          begin
          match rl with
          | Correct x -> (lemma_repr_bytes_values (length c); Correct (c::x))
          | e -> e
          end
        | _ -> Error(AD_bad_certificate_fatal, perror __SOURCE_FILE__ __LINE__ "Badly encoded certificate list")
      else Error(AD_bad_certificate_fatal, perror __SOURCE_FILE__ __LINE__ "Badly encoded certificate list")
      end
    | _ -> Error(AD_bad_certificate_fatal, perror __SOURCE_FILE__ __LINE__ "Badly encoded certificate list")
  else if length b = 0 then Correct []
  else Error(AD_bad_certificate_fatal, perror __SOURCE_FILE__ __LINE__ "Badly encoded certificate list")

#set-options "--max_ifuel 4"

val lemma_parseCertificateList_length: b:bytes -> 
  Lemma (ensures (match parseCertificateList b with
		  | Correct ces -> length (certificateListBytes ces) == length b
		  | _ -> True))
	(decreases (length b))
let rec lemma_parseCertificateList_length b =
  if length b < 3 then ()
  else
    match parseCertificateList b with
    | Correct (hd::tl) ->
      begin
      match vlsplit 3 b with
      | Correct (c, r) ->
        begin
        if length r < 2 then ()
        else
          match vlsplit 2 r with
          | Correct (e, r) ->
            begin
            assume (e == empty_bytes); // FIXME: we don't parse cert. extensions yet
            lemma_parseCertificateList_length r
            end
          | _ -> ()
        end
      | _ -> ()
      end
    | _ -> ()


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
