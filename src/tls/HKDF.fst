(**
TLS 1.3 HKDF extract and expand constructions, parametrized by their hash algorithm
*)
module HKDF

open Mem

open FStar.UInt32
// open FStar.Integers
// 18-09-24 still triggering extraction error

open Hashing.Spec
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
val extract:
  #ha: EverCrypt.HMAC.ha ->
  salt: hkey ha ->
  ikm: macable ha ->
  ST (hkey ha)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))

inline_for_extraction
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

val expand:
  #ha:Hashing.alg ->
  prk: lbytes (EverCrypt.Hash.tagLength ha) ->
  info: bytes {Bytes.length info < 1024 (* somewhat arbitrary *) } ->
  len: UInt32.t {0 < v len /\ v len <= op_Multiply 255 (tagLength ha)} ->
  ST (lbytes32 len)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies_none h0 h1))

#set-options "--z3rlimit 100" 
let expand #ha prk info len =
  let h00 = HyperStack.ST.get() in
  push_frame();
  let tlen = EverCrypt.Hash.tagLen ha in
  let prk_p = LowStar.Buffer.alloca 0uy tlen in
  store_bytes prk prk_p;
  assert_norm(EverCrypt.HMAC.keysized ha (EverCrypt.Hash.tagLength ha));

  let tag_p = LowStar.Buffer.alloca 0uy len in
  let infolen = Bytes.len info in

  if infolen = 0ul then (
    let info_p = LowStar.Buffer.null in
    EverCrypt.HKDF.hkdf_expand ha tag_p prk_p tlen info_p infolen len
  )
  else (
    push_frame();
    let info_p = LowStar.Buffer.alloca 0uy infolen in
    store_bytes info info_p;
    assert(tagLength ha + v infolen + 1 + blockLength ha < pow2 32);
    EverCrypt.HKDF.hkdf_expand ha tag_p prk_p tlen info_p infolen len;
    pop_frame ()
  );
  // FIXME(adl) a functional spec would have helped here

  let tag = of_buffer len tag_p in
  pop_frame();
  let h11 = HyperStack.ST.get() in
  //18-09-01 todo, as in Hashing.compute; similarly missing Stack vs ST. 
  assume(modifies_none h00 h11);
  tag
#reset-options ""

(* earlier, bytes-level implementation:

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
  #ha: Hashing.alg -> prk: hkey ha ->
  info: bytes ->
  len: UInt32.t {UInt32.v len <= op_Multiply 255 (tagLength ha)} ->
  count: UInt8.t ->
//curr: UInt32.t {curr = Int.Cast.uint8_to_uint32 count *^ tagLen ha} ->
  curr: UInt32.t {v curr = op_Multiply (UInt8.v count) (tagLength ha)} ->
  previous: lbytes32 (if count = 0uy then 0ul else tagLen ha) ->
  ST (b: bytes{
    v len - v curr <= length b /\
    length b <= op_Multiply (UInt8.v count) (blockLength ha)
    }) (decreases (max 0 (v len - v curr)))
  (requires fun h0 -> length previous + length info + 1 + Hashing.blockLength ha <= Hashing.maxLength ha)
  (ensures (fun h0 t h1 -> modifies_none h0 h1))

#set-options "--z3rlimit 10 --admit_smt_queries true"
let rec expand_int #ha prk info len count curr previous =
  if curr <^ len && FStar.UInt8.(count <^ 255uy) then (
    assert(FStar.UInt8.(count <^ 255uy));
    assert(UInt8.v count < 255);
    let count = FStar.UInt8.(count +^ 1uy) in
    let curr = curr +^ tagLen ha in
    lemma_repr_bytes_values (UInt8.v count);
    assume (UInt.fits (length previous + length info + 1) 32);
    let block = HMAC.hmac ha prk (previous @| info @| bytes_of_int8 count) in
    assume (v curr = Mul.op_Star (FStar.UInt8.v count) (tagLength ha));
    let next = expand_int prk info len count curr block in
    block @| next )
  else empty_bytes
#reset-options


// let c32 = FStar.Int.Cast.uint8_to_uint32 count in
//assert (c32 <^ 256ul)

/// Final truncation, possibly chopping of the end of the last block.
val expand2:
  #ha:Hashing.alg -> prk: hkey ha ->
  info: bytes ->
  len: UInt32.t {v len <= op_Multiply 255 (tagLength ha)} ->
  ST (lbytes32 len)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))

#reset-options "--admit_smt_queries true"
let expand2 #ha prk info len =
  lemma_repr_bytes_values (v len);
  let rawbytes = expand_int prk info len 0uy 0ul empty_bytes in
  fst (split rawbytes len)
#reset-options
*)


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

let quic_prefix : lbytes 5 =
  let s = bytes_of_string "quic " in
  assume(length s = 5); s

inline_for_extraction private 
val format:
  ha: Hashing.alg ->
  label: string{length (bytes_of_string label) < 256 - 6} ->
  digest: bytes{length digest < 256} ->
  len: UInt32.t {v len <= op_Multiply 255 (tagLength ha)} ->
  is_quic: bool ->
  Tot bytes

/// since derivations depend on the concrete info, we will need to
/// prove format injective on (at least) label digest is_quic.

// RFC-like grammar: 
// struct {
//   uint16 len; 
//   opaque label<0..255>;
//   opaque digest<0..255>;
// } Info;


inline_for_extraction private 
let format ha label digest len is_quic =
  let prefix = if is_quic then quic_prefix else tls13_prefix in
  let label_bytes = prefix @| bytes_of_string label in
  lemma_repr_bytes_values (v len);
  lemma_repr_bytes_values (length label_bytes);
  lemma_repr_bytes_values (length digest);
  bytes_of_int 2 (v len) @|
  Parse.vlbytes 1 label_bytes @|
  Parse.vlbytes 1 digest

/// used for computing all derived keys; 

val expand_label:
  #ha: HMAC.ha ->
  secret: lbytes (EverCrypt.Hash.tagLength ha) ->
  label: string{length (bytes_of_string label) < 256 - 6} -> // -9?
  hv: bytes{length hv < 256} ->
  len: UInt32.t {0 < v len /\ v len <= op_Multiply 255 (tagLength ha)} ->
  is_quic: bool ->
  ST (lbytes32 len)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies_none h0 h1))

let expand_label #ha secret label digest len is_quic =
  let info = format ha label digest len is_quic in 
  expand #ha secret info len

(*-------------------------------------------------------------------*)
(*
  Derive-Secret(Secret, Label, Messages) =
    HKDF-Expand-Label(Secret, Label,
       Transcript-Hash(Messages), Hash.length)
*)

/// used in both hanshakes for deriving intermediate HKDF keys.

val derive_secret:
  ha: EverCrypt.HMAC.ha ->
  secret: lbytes (EverCrypt.Hash.tagLength ha) ->
  label: string{length (bytes_of_string label) < 256-6} ->
  digest: bytes{length digest < 256} ->
  is_quic: bool ->
  ST (lbytes32 (Hashing.Spec.tagLen ha))
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)

let derive_secret ha secret label digest is_quic =
  let len = Hashing.Spec.tagLen ha in
  expand_label secret label digest len is_quic

(*
/// renamed to expand_secret for uniformity
/// not used anymore? 

val expand_secret:
  #ha: EverCrypt.HMAC.ha ->
  secret: hkey ha ->
  label: string{length (bytes_of_string label) < 256-6} ->
  hs_hash: bytes{length hs_hash < 256} ->
  ST (hkey ha)
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)

let expand_secret #ha prk label hv =
  expand_label prk label hv (Hashing.Spec.tagLen ha) false
*)

