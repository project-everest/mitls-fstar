module TLS.HSL.Msg

open FStar.Bytes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow.Base
module L = FStar.List.Tot

type msg = {
  x : U32.t;
  y : U32.t;
}

inline_for_extraction noextract let msg_parser_kind = LP.strong_parser_kind 8 8 ({ LP.parser_kind_metadata_total = true })

noextract val msg_parser: LP.parser msg_parser_kind msg

noextract val msg_serializer: LP.serializer msg_parser

noextract let msg_bytesize (x:msg) : GTot nat = Seq.length (msg_serializer x)

inline_for_extraction val msg_parser32: LP.parser32 msg_parser

inline_for_extraction val msg_serializer32: LP.serializer32 msg_serializer

inline_for_extraction val msg_size32: LP.size32 msg_serializer

