module LowParse.SLow.Int.Proof
include LowParse.Spec.Int
include LowParse.SLow.Int.Code

module Seq = FStar.Seq
module E = LowParse.BigEndian
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B32 = FStar.Bytes
module Cast = FStar.Int.Cast

val serialize32_u8_correct
  (input: U8.t)
: Lemma
  (serializer32_correct #_ #_ #parse_u8 serialize_u8 input (serialize32_u8' input))

val serialize32_u16_correct
  (buf: B32.lbytes 2)
  (input: U16.t)
: Lemma
  (serializer32_correct #_ #_ #parse_u16 serialize_u16 input (serialize32_u16' buf input))

val serialize32_u32_correct
  (buf: B32.lbytes 4)
  (input: U32.t)
: Lemma
  (serializer32_correct #_ #_ #parse_u32 serialize_u32 input (serialize32_u32' buf input))

val decode32_u16_correct
  (b: B32.lbytes 2)
: Lemma (decode32_u16' b == decode_u16 (B32.reveal b))

val decode32_u32_correct
  (b: B32.lbytes 4)
: Lemma (decode32_u32' b == decode_u32 (B32.reveal b))
