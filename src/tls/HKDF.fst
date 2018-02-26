(**
TLS 1.3 HKDF extract and expand constructions, parametrized by their hash algorithm
*)
module HKDF

open FStar.UInt32
open FStar.Bytes
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

val extract: 
  #ha: hash_alg -> salt: hkey ha -> 
  ikm: macable ha -> 
  ST (hkey ha)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))

let extract #ha salt ikm = HMAC.hmac ha salt ikm


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

/// Generates enough bytes by concatenating HMAC blocks;
/// no truncation yet.
///
/// Simple reduction to fixed-length PRF: if (info: bytes) is fresh,
/// then the successive HMAC inputs are also fresh (by case on the
/// *last* byte of the concatenated input of HMAC, separating the
/// domain of the PRF into first blocks and others). On the other
/// hand, the truncation length is not explicitly encoded here.
/// 
private val expand_int: 
  #ha: hash_alg -> prk: hkey ha ->
  info: bytes ->
  len: UInt32.t {UInt32.v len <= op_Multiply 255 (tagLength ha)} ->
  count: UInt8.t ->
//  curr: UInt32.t {curr = Int.Cast.uint8_to_uint32 count *^ tagLen ha} ->
  curr: UInt32.t {v curr = op_Multiply (UInt8.v count) (tagLength ha)} ->
  previous: lbytes32 (if count = 0uy then 0ul else tagLen ha) -> 
  ST (b: bytes{
    v len - v curr <= length b /\
    length b <= op_Multiply (UInt8.v count) (blockLength ha)
    }) (decreases (max 0 (v len - v curr)))
  (requires fun h0 -> length previous + length info + 1 + Hashing.blockLength ha <= Hashing.maxLength ha)
  (ensures (fun h0 t h1 -> modifies_none h0 h1))

#set-options "--z3rlimit 50"
let rec expand_int #ha prk info len count curr previous =
  if curr <^ len && FStar.UInt8.(count <^ 255uy) then
    let count = FStar.UInt8.(count +^ 1uy) in
    let curr = curr +^ tagLen ha in
    lemma_repr_bytes_values (UInt8.v count);
    let block = HMAC.hmac ha prk (previous @| info @| bytes_of_int8 count) in
    let next = expand_int prk info len count curr block in
    block @| next
  else empty_bytes
#reset-options

/// Final truncation, possibly chopping of the end of the last block. 
val expand: 
  #ha:hash_alg -> prk: hkey ha ->
  info: bytes -> 
  len: nat{len <= op_Multiply 255 (tagLen ha)} ->
  ST (lbytes len)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))

let expand #ha prk info len =
  lemma_repr_bytes_values len;
  let rawbytes = expand_int prk info len 0 0 empty_bytes in
  fst (split rawbytes len) 


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

let tls13_prefix : lbytes 6 =
  let s = bytes_of_string "tls13 " in 
  assume(length s = 6); s

val format:
  ha: hash_alg -> 
  label: string{length (bytes_of_string label) < 256 - 6} -> 
  hv: bytes{length hv < 256} -> 
  len: nat{len <= op_Multiply 255 (tagLen ha)} ->
  Tot bytes

let format ha label hv len = 
  let label_bytes = tls13_prefix @| bytes_of_string label in
  lemma_repr_bytes_values len;
  lemma_repr_bytes_values (length label_bytes);
  lemma_repr_bytes_values (length hv);
  bytes_of_int 2 len @|
  vlbytes 1 label_bytes @|
  vlbytes 1 hv 

/// since derivations depend on the concrete info,
/// we will need to prove format injective. 

val expand_label: 
  #ha: hash_alg
  -> prk: hkey ha
  -> label: string{length (bytes_of_string label) < 256 - 6} // -9?
  -> hv: bytes{length hv < 256}
  -> len: nat{len <= op_Multiply 255 (tagLen ha)}
  -> ST (lbytes len)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies_none h0 h1))

let expand_label #ha prk label hv len =
  expand prk (format ha label hv len) len

(*-------------------------------------------------------------------*)
(*
  Derive-Secret(Secret, Label, Messages) =
    HKDF-Expand-Label(Secret, Label,
       Transcript-Hash(Messages), Hash.length)
*)
/// renamed to expand_secret for uniformity

val expand_secret:
  #ha:hash_alg ->
  secret: hkey ha ->
  label: string{length (bytes_of_string label) < 256-6} ->
  hs_hash: bytes{length hs_hash < 256} ->
  ST (hkey ha)
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)

let expand_secret #ha prk label hv =
  expand_label prk label hv (Hashing.Spec.tagLen ha)
  
