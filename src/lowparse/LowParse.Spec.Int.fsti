module LowParse.Spec.Int
include LowParse.Spec.Combinators

module Seq = FStar.Seq
// module E = LowParse.BigEndian
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

let parse_u8_kind : parser_kind = total_constant_size_parser_kind 1

val parse_u8: parser parse_u8_kind U8.t

val serialize_u8 : serializer parse_u8

let parse_u16_kind : parser_kind =
  total_constant_size_parser_kind 2

val parse_u16: parser parse_u16_kind U16.t

val serialize_u16 : serializer parse_u16

let parse_u32_kind : parser_kind =
  total_constant_size_parser_kind 4

val parse_u32: parser parse_u32_kind U32.t

val serialize_u32 : serializer parse_u32
