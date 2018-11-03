module LowParse.Spec.Int.Unique

module Aux = LowParse.Spec.Int.Aux
module I = LowParse.Spec.Int
module Seq = FStar.Seq

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

open LowParse.Spec.Base

val parse_u8_unique
  (b: bytes)
: Lemma
  (parse Aux.parse_u8 b == parse I.parse_u8 b)

val serialize_u8_unique
  (x: U8.t)
: Lemma
  (serialize Aux.serialize_u8 x == serialize I.serialize_u8 x)

val parse_u16_unique
  (b: bytes)
: Lemma
  (parse Aux.parse_u16 b == parse I.parse_u16 b)

val serialize_u16_unique
  (x: U16.t)
: Lemma
  (serialize #_ #_ #Aux.parse_u16 Aux.serialize_u16 x == serialize I.serialize_u16 x)

val parse_u32_unique
  (b: bytes)
: Lemma
  (parse Aux.parse_u32 b == parse I.parse_u32 b)

val serialize_u32_unique
  (x: U32.t)
: Lemma
  (serialize #_ #_ #Aux.parse_u32 Aux.serialize_u32 x == serialize I.serialize_u32 x)
