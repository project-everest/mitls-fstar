module LowParse.Low.Int
include LowParse.Spec.Int
include LowParse.Low.Combinators

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies

inline_for_extraction
val parse32_u8: parser32 parse_u8

inline_for_extraction
val parse32_u16: parser32 parse_u16

inline_for_extraction
val parse32_u32: parser32 parse_u32

inline_for_extraction
let validate32_u8 : validator32 parse_u8 =
  validate32_total_constant_size parse_u8 1l ()

inline_for_extraction
let validate32_u16 : validator32 parse_u16 =
  validate32_total_constant_size parse_u16 2l ()

inline_for_extraction
let validate32_u32 : validator32 parse_u32 =
  validate32_total_constant_size parse_u32 4l ()

inline_for_extraction
let validate_nochk32_u8 : validator_nochk32 parse_u8 =
  validate_nochk32_constant_size parse_u8 1ul ()

inline_for_extraction
let validate_nochk32_u16 : validator_nochk32 parse_u16 =
  validate_nochk32_constant_size parse_u16 2ul ()

inline_for_extraction
let validate_nochk32_u32 : validator_nochk32 parse_u32 =
  validate_nochk32_constant_size parse_u32 4ul ()

val serialize32_u16
  (b: buffer8)
  (lo: U32.t)
  (v: U16.t)
: HST.Stack unit
  (requires (fun h -> B.live h b /\ U32.v lo + 2 <= B.length b))
  (ensures (fun h _ h' ->
    M.modifies (M.loc_buffer (B.gsub b lo (2ul))) h h' /\
    B.live h' b /\
    exactly_contains_valid_data h' parse_u16 b lo v (U32.add lo 2ul)
  ))

val serialize32_u32
  (b: buffer8)
  (lo: U32.t)
  (v: U32.t)
: HST.Stack unit
  (requires (fun h -> B.live h b /\ U32.v lo + 4 <= B.length b))
  (ensures (fun h _ h' ->
    M.modifies (M.loc_buffer (B.gsub b lo (4ul))) h h' /\
    B.live h' b /\
    exactly_contains_valid_data h' parse_u32 b lo v (U32.add lo 4ul)
  ))
