module LowParse.SLow.Int
include LowParse.Spec.Int
include LowParse.SLow.Base

inline_for_extraction
val parse32_u8: parser32 parse_u8

inline_for_extraction
val serialize32_u8 : serializer32 serialize_u8

inline_for_extraction
val parse32_u16: parser32 parse_u16

inline_for_extraction
val serialize32_u16 : serializer32 serialize_u16

inline_for_extraction
val parse32_u32: parser32 parse_u32

inline_for_extraction
val serialize32_u32 : serializer32 serialize_u32
