module LowParse.Low.Int
include LowParse.Spec.Int
include LowParse.Low.Combinators

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module I32 = FStar.Int32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies

inline_for_extraction
val parse32_u8: leaf_reader parse_u8

inline_for_extraction
val parse32_u16: leaf_reader parse_u16

inline_for_extraction
val parse32_u32: leaf_reader parse_u32

inline_for_extraction
let validate_u8 [| validator_cls |] () : validator parse_u8 =
  validate_total_constant_size parse_u8 1ul ()

inline_for_extraction
let validate_u16 [| validator_cls |] () : validator parse_u16 =
  validate_total_constant_size parse_u16 2ul ()

inline_for_extraction
let validate_u32 [| validator_cls |] () : validator parse_u32 =
  validate_total_constant_size parse_u32 4ul ()

inline_for_extraction
let jump_u8 : jumper parse_u8 =
  jump_constant_size parse_u8 1ul ()

inline_for_extraction
let jump_u16 : jumper parse_u16 =
  jump_constant_size parse_u16 2ul ()

inline_for_extraction
let jump_u32 : jumper parse_u32 =
  jump_constant_size parse_u32 4ul ()

inline_for_extraction
val emit_u8 : leaf_writer_strong serialize_u8

inline_for_extraction
let emit_u8_weak : leaf_writer_weak serialize_u8 =
  leaf_writer_weak_of_strong_constant_size emit_u8 1ul ()

inline_for_extraction
val emit_u16 : leaf_writer_strong serialize_u16

inline_for_extraction
let emit_u16_weak : leaf_writer_weak serialize_u16 =
  leaf_writer_weak_of_strong_constant_size emit_u16 2ul ()

inline_for_extraction
val emit_u32 : leaf_writer_strong serialize_u32

inline_for_extraction
let emit_u32_weak : leaf_writer_weak serialize_u32 =
  leaf_writer_weak_of_strong_constant_size emit_u32 4ul ()
