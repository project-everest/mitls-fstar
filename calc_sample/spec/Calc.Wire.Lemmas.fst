module Calc.Wire.Lemmas

open Calc.Wire

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

open FStar.Math.Lemmas

(** Lemma: U32 arithmetic with constants doesn't overflow for byte values **)
let lemma_u32_no_overflow (v0 v1 v2 v3: nat{v0 < 256 /\ v1 < 256 /\ v2 < 256 /\ v3 < 256})
  : Lemma (v0 * 16777216 + v1 * 65536 + v2 * 256 + v3 < 4294967296)
  = assert (v0 * 16777216 <= 255 * 16777216);
    assert (v1 * 65536 <= 255 * 65536);
    assert (v2 * 256 <= 255 * 256);
    assert (v3 <= 255);
    assert (255 * 16777216 + 255 * 65536 + 255 * 256 + 255 == 4294967295);
    assert (v0 * 16777216 + v1 * 65536 + v2 * 256 + v3 <= 4294967295)

(** Lemma: U32 modular arithmetic equals mathematical for non-overflowing values **)
let lemma_u32_arithmetic_correspondence
  (v0 v1 v2 v3: U32.t)
  : Lemma 
      (requires 
        U32.v v0 < 256 /\ U32.v v1 < 256 /\ U32.v v2 < 256 /\ U32.v v3 < 256)
      (ensures (
        let math_result = U32.v v0 * 16777216 + U32.v v1 * 65536 + U32.v v2 * 256 + U32.v v3 in
        let u32_result = U32.add (U32.add (U32.mul v0 16777216ul) 
                                           (U32.add (U32.mul v1 65536ul) 
                                                    (U32.mul v2 256ul))) v3 in
        U32.v u32_result == math_result))
  = lemma_u32_no_overflow (U32.v v0) (U32.v v1) (U32.v v2) (U32.v v3);
    // Since the result < 2^32, modular arithmetic is identity
    assert (U32.v (U32.mul v0 16777216ul) == (U32.v v0 * 16777216) % 4294967296);
    assert (U32.v (U32.mul v1 65536ul) == (U32.v v1 * 65536) % 4294967296);
    assert (U32.v (U32.mul v2 256ul) == (U32.v v2 * 256) % 4294967296);
    // Addition modular arithmetic
    ()

(** Non-refined version of be_to_n for use in Pulse postconditions **)
let be_to_n_unrefined (b0 b1 b2 b3: U8.t) : int =
  U8.v b0 * 16777216 + U8.v b1 * 65536 + U8.v b2 * 256 + U8.v b3

(** Lemma connecting unrefined to refined be_to_n **)
let lemma_be_to_n_equiv
  (bytes: bytes{Seq.length bytes == 4})
  : Lemma (be_to_n bytes == be_to_n_unrefined 
            (Seq.index bytes 0)
            (Seq.index bytes 1)
            (Seq.index bytes 2)
            (Seq.index bytes 3))
  = ()

(** Lemma: parse_push_value computes be_to_n correctly **)
let lemma_parse_push_value_correct
  (b1 b2 b3 b4: U8.t)
  (bytes: bytes{Seq.length bytes == 4})
  : Lemma
      (requires
        Seq.index bytes 0 == b1 /\
        Seq.index bytes 1 == b2 /\
        Seq.index bytes 2 == b3 /\
        Seq.index bytes 3 == b4)
      (ensures (
        U32.v (Cast.uint8_to_uint32 b1) * 16777216 +
        U32.v (Cast.uint8_to_uint32 b2) * 65536 +
        U32.v (Cast.uint8_to_uint32 b3) * 256 +
        U32.v (Cast.uint8_to_uint32 b4) ==
        be_to_n bytes))
  = let v0 = U32.v (Cast.uint8_to_uint32 b1) in
    let v1 = U32.v (Cast.uint8_to_uint32 b2) in
    let v2 = U32.v (Cast.uint8_to_uint32 b3) in
    let v3 = U32.v (Cast.uint8_to_uint32 b4) in
    
    // From Cast postconditions: uint8_to_uint32 preserves value
    assert (v0 == U8.v b1);
    assert (v1 == U8.v b2);
    assert (v2 == U8.v b3);
    assert (v3 == U8.v b4);
    
    // be_to_n definition
    assert (be_to_n bytes == U8.v b1 * 16777216 + U8.v b2 * 65536 + U8.v b3 * 256 + U8.v b4)

(** Non-refined big-endian encoder components **)
let n_to_be_b0 (value: nat{value < 4294967296}) : int = (value / 16777216) % 256
let n_to_be_b1 (value: nat{value < 4294967296}) : int = (value / 65536) % 256
let n_to_be_b2 (value: nat{value < 4294967296}) : int = (value / 256) % 256
let n_to_be_b3 (value: nat{value < 4294967296}) : int = value % 256

(** Lemma: shift_right extracts the right byte **)
let lemma_shift_right_byte
  (value: U32.t)
  (shift: nat{shift <= 24 /\ shift % 8 == 0})
  : Lemma (U32.v (U32.shift_right value (U32.uint_to_t shift)) == U32.v value / pow2 shift)
  = ()

(** Lemma: uint32_to_uint8 gets the low byte **)
let lemma_uint32_to_uint8_mod
  (value: U32.t)
  : Lemma (U8.v (Cast.uint32_to_uint8 value) == U32.v value % 256)
  = ()

(** Lemma: n_to_be components reconstruct the original value **)
let lemma_n_to_be_correct
  (value: nat{value < 4294967296})
  : Lemma (
      n_to_be_b0 value * 16777216 + 
      n_to_be_b1 value * 65536 + 
      n_to_be_b2 value * 256 + 
      n_to_be_b3 value == value)
  = lemma_div_mod value 16777216;
    lemma_div_mod (value % 16777216) 65536;
    lemma_div_mod (value % 65536) 256

(** Lemma: write_result_response produces bytes matching n_to_be **)
let lemma_write_result_bytes
  (value: U32.t)
  : Lemma (
      let b1 = U8.v (Cast.uint32_to_uint8 (U32.shift_right value 24ul)) in
      let b2 = U8.v (Cast.uint32_to_uint8 (U32.shift_right value 16ul)) in
      let b3 = U8.v (Cast.uint32_to_uint8 (U32.shift_right value 8ul)) in
      let b4 = U8.v (Cast.uint32_to_uint8 value) in
      b1 == n_to_be_b0 (U32.v value) /\ 
      b2 == n_to_be_b1 (U32.v value) /\ 
      b3 == n_to_be_b2 (U32.v value) /\ 
      b4 == n_to_be_b3 (U32.v value))
  = lemma_shift_right_byte value 24;
    lemma_shift_right_byte value 16;
    lemma_shift_right_byte value 8;
    lemma_uint32_to_uint8_mod (U32.shift_right value 24ul);
    lemma_uint32_to_uint8_mod (U32.shift_right value 16ul);
    lemma_uint32_to_uint8_mod (U32.shift_right value 8ul);
    lemma_uint32_to_uint8_mod value;
    assert (pow2 24 == 16777216);
    assert (pow2 16 == 65536);
    assert (pow2 8 == 256)


