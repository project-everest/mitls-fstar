module Format.ECCurveType

module B = FStar.Bytes
module L = FStar.List
module U8 = FStar.UInt8
module LP = LowParse.SLow.Base

type byte = B.byte

noeq type ecCurveType = 
  | EXPLICIT_PRIME
  | EXPLICIT_CHAR2
  | NAMED_CURVE
  | RESERVED of (r:byte{U8.(248uy <=^ r && r <=^ 255uy)})
  | UNKNOWN of (r:byte{not U8.(248uy <=^ r && r <=^ 255uy) /\
                       not U8.(r =^ 1uy) /\
                       not U8.(r =^ 2uy) /\
                       not U8.(r =^ 3uy)})

inline_for_extraction
val ecCurveType_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction
let ecCurveType_parser_kind =
  LP.strong_parser_kind 1 1 ecCurveType_parser_kind_metadata

val ecCurveType_parser: LP.parser ecCurveType_parser_kind ecCurveType

inline_for_extraction
val ecCurveType_parser32: LP.parser32 ecCurveType_parser

val ecCurveType_serializer: LP.serializer ecCurveType_parser

inline_for_extraction
val ecCurveType_serializer32: LP.serializer32 ecCurveType_serializer
