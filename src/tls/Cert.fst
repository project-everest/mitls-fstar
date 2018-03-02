(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)
module Cert

open FStar.Bytes
open FStar.Error

open TLSError
open TLSConstants
open CoreCrypto
open Extensions // defining cert, cert13, chain

(* The chain format changes between TLS 1.2 and TLS 1.3; we separate
then in messages, but at least for now, we merge the two in
Negotiation and in the main TLS API (with no extensions when using TLS
1.2 *)

// opaque cert_data<1..2^24-1>
type cert = b:bytes {length b < 16777216}
type certes = cert * (exts:extensions{length (extensionListBytes exts) < 65536 /\ bindersLen exts == 0})
// CertificateEntry certificate_list<0..2^24-1>;
// See https://tlswg.github.io/tls13-spec/#rfc.section.4.4.2
type chain = l:list cert // { ... }
type chain13 = l:list certes // { ... }

// we may use these types to keep track of un-extended chains,
// e.g. to prove that their formatting is injective
let is_classic_chain_aux ces = List.Tot.isEmpty (snd ces)
let is_classic_chain (l:chain13): bool =
  List.Tot.for_all #certes is_classic_chain_aux l
type chain12 = l:chain13 {is_classic_chain l}

// todo: prove it is a chain12
let chain_up_aux c = c, []
let chain_up (l:chain): chain13= List.Tot.map #cert #certes chain_up_aux l
let chain_down (l:chain13): chain = List.Tot.map #certes #cert fst l

(* ------------------------------------------------------------------------ *)

abstract val certificateListBytes: chain -> Tot bytes
let rec certificateListBytes = function
  | [] -> empty_bytes
  | crt :: rest ->
    lemma_repr_bytes_values (length crt);
    vlbytes 3 crt @| certificateListBytes rest

abstract val certificateListBytes13: chain13 -> Tot bytes
let rec certificateListBytes13 = function
  | [] -> empty_bytes
  | (crt, exts) :: rest ->
    lemma_repr_bytes_values (length crt);
    vlbytes 3 crt @| extensionsBytes exts @| certificateListBytes13 rest

val certificateListBytes_is_injective: c1:chain -> c2:chain ->
  Lemma (Bytes.equal (certificateListBytes c1) (certificateListBytes c2) ==> c1 == c2)
let rec certificateListBytes_is_injective c1 c2 =
  match c1, c2 with
  | [], [] -> ()
  | hd::tl, hd'::tl' ->
    if certificateListBytes c1 = certificateListBytes c2 then
      begin
      lemma_repr_bytes_values (length hd); lemma_repr_bytes_values (length hd');
      cut(Bytes.equal ((vlbytes 3 hd) @| (certificateListBytes tl)) ((vlbytes 3 hd') @| (certificateListBytes tl')));
      lemma_repr_bytes_values (length hd);
      lemma_repr_bytes_values (length hd');
      cut(Bytes.equal (Bytes.slice (vlbytes 3 hd) 0ul 3ul) (Bytes.slice (certificateListBytes c1) 0ul 3ul));
      cut(Bytes.equal (Bytes.slice (vlbytes 3 hd') 0ul 3ul) (Bytes.slice (certificateListBytes c1) 0ul 3ul));
      vlbytes_length_lemma 3 hd hd';
      //lemma_append_inj (vlbytes 3 hd) (certificateListBytes tl) (vlbytes 3 hd') (certificateListBytes tl'); //TODO bytes NS 09/27
      lemma_vlbytes_inj 3 hd hd';
      certificateListBytes_is_injective tl tl'
      end
  | [], hd::tl ->
    begin
    cut (length (certificateListBytes c1) = 0);
    lemma_repr_bytes_values (length hd);
    cut (Bytes.equal (certificateListBytes c2) ((vlbytes 3 hd) @| (certificateListBytes tl)));
    lemma_vlbytes_len 3 hd
    end
  | hd::tl, [] ->
    begin
    cut (length (certificateListBytes c2) = 0);
    lemma_repr_bytes_values (length hd);
    cut (Bytes.equal (certificateListBytes c1) ((vlbytes 3 hd) @| (certificateListBytes tl)));
    lemma_vlbytes_len 3 hd
    end

val certificateListBytes13_is_injective: c1:chain13 -> c2:chain13 ->
  Lemma (Bytes.equal (certificateListBytes13 c1) (certificateListBytes13 c2) ==> c1 == c2)
let rec certificateListBytes13_is_injective c1 c2 =
  // TODO: need injectivity lemmas for extensions
  admit()

abstract val parseCertificateList: b:bytes -> Tot (result chain) (decreases (length b))
let rec parseCertificateList b =
  if length b = 0 then Correct [] else
  if length b < 3 then Error(AD_bad_certificate_fatal, "not enough bytes (certificate length)") else
  match vlsplit 3 b with
  | Error _ -> Error(AD_bad_certificate_fatal, "not enough bytes (certificate)")
  | Correct (x) -> (
    let c, r = x in
    match parseCertificateList r with
    | Error z -> Error z
    | Correct cs -> lemma_repr_bytes_values (length c); Correct (c::cs) )

#set-options "--z3rlimit 50" 
abstract val parseCertificateList13: b:bytes -> Tot (result chain13) (decreases (length b))
let rec parseCertificateList13 b =
  if length b = 0 then Correct [] else
  if length b < 3 then Error(AD_bad_certificate_fatal, "not enough bytes (certificate length)") else
  match vlsplit 3 b with
  | Error _ -> Error(AD_bad_certificate_fatal, "not enough bytes (certificate)")
  | Correct (x) -> (
    let c, r = x in 
    if length r < 2 then Error(AD_bad_certificate_fatal, "not enough bytes (extension length") else
    match vlsplit 2 r with
    | Error _ -> Error(AD_bad_certificate_fatal, "not enough bytes (extension list)")
    | Correct (x) -> (
      let e, r = x in
      match parseExtensions EM_Certificate (vlbytes 2 e) with
      | Error z -> Error z
      | Correct (exts,_) -> (
        match parseCertificateList13 r with
        | Error z -> Error z
        | Correct x ->
          if bindersLen exts = 0 then
          begin
            lemma_repr_bytes_values (length c);
            lemma_repr_bytes_values (length (extensionListBytes exts));
            Correct ((c,exts) :: x)
          end
          else Error(AD_bad_certificate_fatal, "unexpected extension") )))

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
      | Correct (x) -> 
        let c, r = x in
        lemma_parseCertificateList_length r
      | _ -> ()
      end
    | _ -> ()
