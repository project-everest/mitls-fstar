module LowParse.Low.Int
include LowParse.Spec.Int
include LowParse.Low.Base

inline_for_extraction
val parse32_u8: parser32 parse_u8

inline_for_extraction
val parse32_u16: parser32 parse_u16

inline_for_extraction
val parse32_u32: parser32 parse_u32

inline_for_extraction
val validate32_u8: validator32 parse_u8

inline_for_extraction
val validate32_u16: validator32 parse_u16

inline_for_extraction
val validate32_u32: validator32 parse_u32

inline_for_extraction
val validate_nochk32_u8: validator_nochk32 parse_u8

inline_for_extraction
val validate_nochk32_u16: validator_nochk32 parse_u16

inline_for_extraction
val validate_nochk32_u32: validator_nochk32 parse_u32
