module Format.Constants

open FStar.Bytes

module LP = LowParse.SLow
module U8 = FStar.UInt8

let constantByte_parser_kind' = LP.parse_filter_kind LP.parse_u8_kind

let constantByte_parser_kind_metadata = constantByte_parser_kind'.LP.parser_kind_metadata

let constantByte_parser c =
  LP.parse_filter LP.parse_u8 (is_constantByte c)

let constantByte_parser32 c =
  LP.parse32_filter LP.parse32_u8 (is_constantByte c) (fun x -> is_constantByte c x)

let constantByte_serializer c
  = LP.serialize_filter 
      #LP.parse_u8_kind #U8.t #LP.parse_u8
      LP.serialize_u8 
      (is_constantByte c)

let constantByte_serializer32 c
  = LP.serialize32_filter 
      #LP.parse_u8_kind #U8.t #LP.parse_u8 #LP.serialize_u8
      LP.serialize32_u8
      (is_constantByte c)
