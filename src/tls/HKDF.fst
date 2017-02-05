(* TLS 1.3 HKDF extract and expand constructions, parametrized by their hash algorithm *) 
module HKDF

open Platform.Bytes
open TLSConstants
open Hashing.Spec

private let max (a:int) (b:int) = if a < b then b else a

(*-------------------------------------------------------------------*)
(*
From https://tools.ietf.org/html/rfc5869

HKDF-Extract(salt, IKM) -> PRK
   Options:
      Hash     a hash function; HashLen denotes the length of the
               hash function output in octets
   Inputs:
      salt     optional salt value (a non-secret random value);
               if not provided, it is set to a string of HashLen zeros.
      IKM      input keying material
   Output:
      PRK      a pseudorandom key (of HashLen octets)

   PRK = HMAC-Hash(salt, IKM)
*)

val hkdf_extract: ha:hash_alg -> salt:hkey ha -> ikm:bytes -> ST (tag ha)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))

let hkdf_extract ha salt ikm = HashMAC.hmac ha salt ikm


(*-------------------------------------------------------------------*)
(*
HKDF-Expand(PRK, info, L) -> OKM
   Options:
      Hash     a hash function; HashLen denotes the length of the
               hash function output in octets
   Inputs:
      PRK      a pseudorandom key of at least HashLen octets
               (usually, the output from the extract step)
      info     optional context and application specific information
               (can be a zero-length string)
      L        length of output keying material in octets (<= 255*HashLen)
   Output:
      OKM      output keying material (of L octets)

   N = ceil(L/HashLen)
   T = T(1) | T(2) | T(3) | ... | T(N)

   OKM = first L octets of T

   where:
   T(0) = empty string
   T(1) = HMAC-Hash(PRK, T(0) | info | 0x01)
   T(2) = HMAC-Hash(PRK, T(1) | info | 0x02)
   ...
*)

// we take a stricter approach and require that the secret and the hash have the same size.
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

val hkdf_expand: ha:hash_alg
  -> prk: hkey ha
  -> info: bytes
  -> len: nat{len <= op_Multiply 255 (tagLen ha)}
  -> ST (lbytes len)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))

let hkdf_expand ha prk info len =
  lemma_repr_bytes_values len;
  let raw = hkdf_expand_int ha prk info len 0 0 empty_bytes in
  fst(split raw len)  // possibly chopping off the end of the last hash


(*-------------------------------------------------------------------*)
(*
HKDF-Expand-Label(Secret, Label, Messages, Length) =
       HKDF-Expand(Secret, HkdfLabel, Length)

  Where HkdfLabel is specified as:

  struct HkdfLabel {
    uint16 length;
    opaque label<9..255>;
    opaque hash_value<0..255>;
  };

  - HkdfLabel.length is Length
  - HkdfLabel.label is "TLS 1.3, " + Label
  - HkdfLabel.hash_value is HashValue.
*)

val tls13_prefix: lbytes 9
let tls13_prefix =
  let s = abytes "TLS 1.3, " in
  assume(length s = 9);
  //if length s <> 9 then Platform.Error.unexpected "Cannot be proved statically because abytes is underspecified";
  s

val hkdf_expand_label: ha: hash_alg
  -> prk: hkey ha
  -> label: string{length (abytes label) < 256 - 9}
  -> hv: bytes{length hv < 256}
  -> len: nat{len <= op_Multiply 255 (tagLen ha)}
  -> ST (lbytes len)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))

let hkdf_expand_label ha prk label hv len =
  let label_bytes = tls13_prefix @| abytes label in
  lemma_repr_bytes_values len;
  lemma_repr_bytes_values (length label_bytes);
  lemma_repr_bytes_values (length hv);
  let info = bytes_of_int 2 len @| 
	     vlbytes 1 label_bytes @|
	     vlbytes 1 hv in
  hkdf_expand ha prk info len
