module LowParse.Low.Int
include LowParse.Spec.Int
include LowParse.Low.Base

inline_for_extraction
val parse32_u8: parser32 parse_u8

inline_for_extraction
val parse32_u16: parser32 parse_u16

inline_for_extraction
val parse32_u32: parser32 parse_u32
