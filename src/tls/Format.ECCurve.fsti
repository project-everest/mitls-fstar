module Format.ECCurve

module B = FStar.Bytes
module LP = LowParse.SLow.Base
module U8 = FStar.UInt8
module U16 = FStar.UInt16

open Format.LBytes1

noeq type ecCurve = {
  a : lbytes_1;
  b : lbytes_1;
}

inline_for_extraction
val ecCurve_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction
let ecCurve_parser_kind =
  LP.strong_parser_kind 4 512 ecCurve_parser_kind_metadata

val ecCurve_parser : LP.parser ecCurve_parser_kind ecCurve

inline_for_extraction
val ecCurve_parser32 : LP.parser32 ecCurve_parser

val ecCurve_serializer: LP.serializer ecCurve_parser

inline_for_extraction
val ecCurve_serializer32: LP.serializer32 ecCurve_serializer
