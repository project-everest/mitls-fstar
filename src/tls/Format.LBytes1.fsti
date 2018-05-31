module Format.LBytes1

module B = FStar.Bytes
module LP = LowParse.SLow.Base

let is_lbytes_1 (b: B.bytes) = 0 < B.length b && B.length b < 256

type lbytes_1 = b: B.bytes{is_lbytes_1 b}

inline_for_extraction
val lbytes_1_parser_kind_metadata: LP.parser_kind_metadata_t

inline_for_extraction
let lbytes_1_parser_kind =
  LP.strong_parser_kind 2 256 lbytes_1_parser_kind_metadata

val lbytes_1_parser : LP.parser lbytes_1_parser_kind lbytes_1

inline_for_extraction
val lbytes_1_parser32 : LP.parser32 lbytes_1_parser

val lbytes_1_serializer : LP.serializer lbytes_1_parser

inline_for_extraction
val lbytes_1_serializer32 : LP.serializer32 lbytes_1_serializer

