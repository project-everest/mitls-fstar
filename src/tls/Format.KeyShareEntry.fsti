module Format.KeyShareEntry

open Format.NamedGroup

module B = FStar.Bytes
module LP = LowParse.SLow.Base
module U32 = FStar.UInt32

type keyShareEntry = {
  group        : namedGroup; 
  key_exchange : B.bytes; // (bs:B.bytes{1 <= B.length bs && B.length bs <= 65535});
}

inline_for_extraction
val keyShareEntry_parser_kind_metadata : LP.parser_kind_metadata_t

inline_for_extraction
let keyShareEntry_parser_kind =
  LP.strong_parser_kind 5 65539 keyShareEntry_parser_kind_metadata

val keyShareEntry_parser: LP.parser keyShareEntry_parser_kind keyShareEntry

inline_for_extraction
val keyShareEntry_parser32: LP.parser32 keyShareEntry_parser

val keyShareEntry_serializer: LP.serializer keyShareEntry_parser

inline_for_extraction
val keyShareEntry_serializer32: LP.serializer32 keyShareEntry_serializer
