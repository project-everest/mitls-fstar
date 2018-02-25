module LowParse.SLow.VLData.Proof
include LowParse.SLow.VLData.Code

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = LowParse.BigEndian
module Cast = FStar.Int.Cast
module B32 = FStar.Bytes

val serialize32_bounded_integer_1_correct
  (buf: B32.lbytes 1)
  (input: bounded_integer 1)
: Lemma
  (serializer32_correct (serialize_bounded_integer 1) input (serialize32_bounded_integer_1' buf input))

val serialize32_bounded_integer_2_correct
  (buf: B32.lbytes 2)
  (input: bounded_integer 2)
: Lemma
  (serializer32_correct (serialize_bounded_integer 2) input (serialize32_bounded_integer_2' buf input))

val serialize32_bounded_integer_3_correct
  (buf: B32.lbytes 3)
  (input: bounded_integer 3)
: Lemma
  (serializer32_correct (serialize_bounded_integer 3) input (serialize32_bounded_integer_3' buf input))

val decode32_bounded_integer_1_correct
 (b: B32.lbytes 1)
: Lemma
  (let y : U32.t = decode32_bounded_integer_1' b in
   U32.v y < pow2 (Prims.op_Multiply 8 1) /\
   (y <: bounded_integer 1) == decode_bounded_integer 1 (B32.reveal b))

let synth_bounded_integer_2
  (x: U16.t)
: GTot (bounded_integer 2)
= Cast.uint16_to_uint32 x

val parse_bounded_integer_2_spec
: unit ->
  Lemma
  (forall (input: bytes) . parse (parse_bounded_integer 2) input == parse (parse_u16 `parse_synth` synth_bounded_integer_2) input)

val decode32_bounded_integer_3_correct
 (b: B32.lbytes 3)
: Lemma
  (let y = decode32_bounded_integer_3' b in
   U32.v y < pow2 (Prims.op_Multiply 8 3) /\
   (y <: bounded_integer 3) == decode_bounded_integer 3 (B32.reveal b))

let synth_bounded_integer_4
  (x: U32.t)
: GTot (bounded_integer 4)
= x

val parse_bounded_integer_4_spec
: unit ->
  Lemma
  (forall (input: bytes) . parse (parse_bounded_integer 4) input == parse (parse_u32 `parse_synth` synth_bounded_integer_4) input)
