module Format.Constants

open FStar.Bytes

module LP = LowParse.SLow
module U8 = FStar.UInt8


let is_constantByte (c:byte) (x:byte): Tot bool = x = c

type constantByte (c:byte) = b:byte{is_constantByte c b}

let constantByte_parser_kind = LP.parse_filter_kind LP.parse_u8_kind

let constantByte_parser (c:byte): LP.parser constantByte_parser_kind (constantByte c) =
  LP.parse_filter LP.parse_u8 (is_constantByte c)

inline_for_extraction
let constantByte_parser32 (c:byte): LP.parser32 (constantByte_parser c) =
  LP.parse32_filter LP.parse32_u8 (is_constantByte c) (fun x -> is_constantByte c x)

let constantByte_serializer (c:byte)
  : LP.serializer #constantByte_parser_kind #(constantByte c) (constantByte_parser c)
  = LP.serialize_filter 
      #LP.parse_u8_kind #U8.t #LP.parse_u8
      LP.serialize_u8 
      (is_constantByte c)

inline_for_extraction
let constantByte_serializer32 (c:byte)
  : LP.serializer32 #constantByte_parser_kind #(constantByte c) #(constantByte_parser c) (constantByte_serializer c) 
  = LP.serialize32_filter 
      #LP.parse_u8_kind #U8.t #LP.parse_u8 #LP.serialize_u8
      LP.serialize32_u8
      (is_constantByte c)
