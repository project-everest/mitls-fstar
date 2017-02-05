(* TLS 1.3 HKDF extract and expand constructions, parametrized by their hash algorithm *) 
module HKDF

open Platform.Bytes
open TLSConstants
open Hashing.Spec

private let max (a:int) (b:int) = if a < b then b else a

let hkdf_extract ha salt ikm = HashMAC.hmac ha salt ikm

private val hkdf_expand_int: ha:hash_alg
  -> prk: hkey ha //was: bytes{tagLen ha <= length prk}
  -> info:bytes
  -> len:nat{len <= op_Multiply 255 (tagLen ha)}
  -> count:nat{count < 256 }
  -> curr:nat{curr = op_Multiply count (tagLen ha)}
  -> prev:bytes
  -> ST (b:bytes{len - curr <= length b}) (decreases (max 0 (len - curr)))
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))

let rec hkdf_expand_int ha prk info len count curr prev =
  if curr < len && count + 1 < 256 then
    let count = count + 1 in
    let curr = curr + tagLen ha in
    lemma_repr_bytes_values count;
    let prev = HashMAC.hmac ha prk (prev @| info @| bytes_of_int 1 count) in
    let next = hkdf_expand_int ha prk info len count curr prev in
    prev @| next
  else empty_bytes

let hkdf_expand ha prk info len =
  lemma_repr_bytes_values len;
  let raw = hkdf_expand_int ha prk info len 0 0 empty_bytes in
  fst(split raw len)  // possibly chopping off the end of the last hash

let tls13_prefix =
  let s = abytes "TLS 1.3, " in
  assume(length s = 9);
  //if length s <> 9 then Platform.Error.unexpected "Cannot be proved statically because abytes is underspecified";
  s

let hkdf_expand_label ha prk label hv len =
  let label_bytes = tls13_prefix @| abytes label in
  lemma_repr_bytes_values len;
  lemma_repr_bytes_values (length label_bytes);
  lemma_repr_bytes_values (length hv);
  let info = bytes_of_int 2 len @| 
	     vlbytes 1 label_bytes @|
	     vlbytes 1 hv in
  hkdf_expand ha prk info len
