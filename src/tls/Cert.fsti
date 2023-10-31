(* Copyright (C) 2012--2018 Microsoft Research and INRIA *)
module Cert

open FStar.Bytes
open FStar.Error

open TLSError
open TLSConstants
open Extensions // defining cert, cert13, chain
module Parse = Parse
 
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
let is_classic_chain_aux (ces:certes) = List.Tot.isEmpty (snd ces)
let is_classic_chain (l:chain13): bool =
  List.Tot.for_all #certes is_classic_chain_aux l
type chain12 = l:chain13 {is_classic_chain l}

// 2018.03.10 SZ: The types in Extensions.fsti are too weak to prove the refinement in [certes]
// todo: prove it is a chain12
let chain_up_aux (c:cert) : certes = admit (); c, []  //AR: 04/08: moving admit inside
#reset-options

let chain_up (l:chain): chain13= List.Tot.map #cert #certes chain_up_aux l
let chain_down (l:chain13): chain = List.Tot.map #certes #cert fst l

(* ------------------------------------------------------------------------ *)

val certificateListBytes: chain -> Tot bytes

val certificateListBytes13: chain13 -> Tot bytes

#push-options "--admit_smt_queries true"
let rec certificateListBytes_is_injective: c1:chain -> c2:chain ->
  Lemma (Bytes.equal (certificateListBytes c1) (certificateListBytes c2) ==> c1 == c2) =

// 2018.03.10: Lax-typecheck for now; this will be reimplemented in LowParse anyway
  fun c1 c2 -> admit ()  //AR: 04/08: this lemma is anyway admitted, commenting the body below
  // match c1, c2 with
  // | [], [] -> ()
  // | hd::tl, hd'::tl' ->
  //   if certificateListBytes c1 = certificateListBytes c2 then
  //     begin
  //     lemma_repr_bytes_values (length hd); lemma_repr_bytes_values (length hd');
  //     cut(Bytes.equal ((vlbytes 3 hd) @| (certificateListBytes tl)) ((vlbytes 3 hd') @| (certificateListBytes tl')));
  //     lemma_repr_bytes_values (length hd);
  //     lemma_repr_bytes_values (length hd');
  //     cut(Bytes.equal (Bytes.slice (vlbytes 3 hd) 0ul 3ul) (Bytes.slice (certificateListBytes c1) 0ul 3ul));
  //     cut(Bytes.equal (Bytes.slice (vlbytes 3 hd') 0ul 3ul) (Bytes.slice (certificateListBytes c1) 0ul 3ul));
  //     vlbytes_length_lemma 3 hd hd';
  //     //lemma_append_inj (vlbytes 3 hd) (certificateListBytes tl) (vlbytes 3 hd') (certificateListBytes tl'); //TODO bytes NS 09/27
  //     lemma_vlbytes_inj 3 hd hd';
  //     certificateListBytes_is_injective tl tl'
  //     end
  // | [], hd::tl ->
  //   begin
  //   cut (length (certificateListBytes c1) = 0);
  //   lemma_repr_bytes_values (length hd);
  //   cut (Bytes.equal (certificateListBytes c2) ((vlbytes 3 hd) @| (certificateListBytes tl)));
  //   lemma_vlbytes_len 3 hd
  //   end
  // | hd::tl, [] ->
  //   begin
  //   cut (length (certificateListBytes c2) = 0);
  //   lemma_repr_bytes_values (length hd);
  //   cut (Bytes.equal (certificateListBytes c1) ((vlbytes 3 hd) @| (certificateListBytes tl)));
  //   lemma_vlbytes_len 3 hd
  //   end
#pop-options

let rec certificateListBytes13_is_injective: c1:chain13 -> c2:chain13 ->
  Lemma (Bytes.equal (certificateListBytes13 c1) (certificateListBytes13 c2) ==> c1 == c2) = fun c1 c2 -> admit ()

val parseCertificateList: b:bytes -> Tot (result chain) (decreases (length b))

val parseCertificateList13: b:bytes -> Tot (result chain13) (decreases (length b))

val lemma_parseCertificateList_length: b:bytes ->
  Lemma (ensures (match parseCertificateList b with
      | Correct ces -> length (certificateListBytes ces) == length b
      | _ -> True))
  (decreases (length b))
