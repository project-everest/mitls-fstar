module Format.Constants

open FStar.Bytes

module LP = LowParse.SLow.Base
module U8 = FStar.UInt8

inline_for_extraction
let is_constantByte (c:byte) (x:byte): Tot bool = x = c

type constantByte (c:byte) = b:byte{is_constantByte c b}

inline_for_extraction
val constantByte_parser_kind_metadata: LP.parser_kind_metadata_t

inline_for_extraction
let constantByte_parser_kind =
  LP.strong_parser_kind 1 1 constantByte_parser_kind_metadata

val constantByte_parser (c: byte) : Tot (LP.parser constantByte_parser_kind (constantByte c))

inline_for_extraction
val constantByte_parser32 (c:byte): Tot (LP.parser32 (constantByte_parser c))

val constantByte_serializer (c:byte)
  : Tot (LP.serializer #constantByte_parser_kind #(constantByte c) (constantByte_parser c))

inline_for_extraction
val constantByte_serializer32 (c:byte)
  : Tot (LP.serializer32 #constantByte_parser_kind #(constantByte c) #(constantByte_parser c) (constantByte_serializer c))


(* Lemmas *)

val lemma_constantByte_parser_is_strong (b:byte): 
  Lemma (LP.is_strong (constantByte_parser b) /\
         constantByte_parser_kind.LP.parser_kind_subkind == Some (LowParse.Spec.Base.ParserStrong))
