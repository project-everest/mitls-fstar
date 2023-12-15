(**
TLS 1.3 HKDF extract and expand constructions, parametrized by their hash algorithm
*)
module MiTLS.HKDF
open MiTLS

open MiTLS.Mem

open FStar.UInt32
// open FStar.Integers
// 18-09-24 still triggering extraction error

open MiTLS.Hashing.Spec
open FStar.Bytes

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

inline_for_extraction
let extract:
  #ha: Hashing.Spec.tls_macAlg ->
  salt: hkey ha ->
  ikm: macable ha ->
  ST (hkey ha)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))
  = fun #ha salt ikm -> HMAC.hmac ha salt ikm

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

val expand_spec:
  #ha:Hashing.alg ->
  prk: Hashing.Spec.tag ha ->
  info: bytes {Bytes.length info < 1024 (* somewhat arbitrary *) } ->
  len: UInt32.t {0 < v len /\ v len <= op_Multiply 255 (hash_length ha)} ->
  GTot (lbytes32 len)

val expand:
  #ha:Hashing.Spec.tls_macAlg ->
  prk: lbytes (Spec.Hash.Definitions.hash_length ha) ->
  info: bytes {Bytes.length info < 1024 (* somewhat arbitrary *) } ->
  len: UInt32.t {0 < v len /\ v len <= op_Multiply 255 (hash_length ha)} ->
  ST (lbytes32 len)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies_none h0 h1 /\
    t == expand_spec #ha prk info len))

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

/// used for computing all derived keys; 

val expand_label:
  #ha: Hashing.Spec.tls_macAlg ->
  secret: lbytes (Spec.Hash.Definitions.hash_length ha) ->
  label: string{length (bytes_of_string label) < 256 - 6} -> // -9?
  hv: bytes{length hv < 256} ->
  len: UInt32.t {0 < v len /\ v len <= op_Multiply 255 (hash_length ha)} ->
  ST (lbytes32 len)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies_none h0 h1))

(*-------------------------------------------------------------------*)
(*
  Derive-Secret(Secret, Label, Messages) =
    HKDF-Expand-Label(Secret, Label,
       Transcript-Hash(Messages), Hash.length)
*)

/// used in both hanshakes for deriving intermediate HKDF keys.

val derive_secret:
  ha: Hashing.Spec.tls_macAlg ->
  secret: lbytes (Spec.Hash.Definitions.hash_length ha) ->
  label: string{length (bytes_of_string label) < 256-6} ->
  digest: bytes{length digest < 256} ->
  ST (lbytes32 (Hacl.Hash.Definitions.hash_len ha))
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)

