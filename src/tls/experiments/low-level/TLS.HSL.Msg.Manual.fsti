module TLS.HSL.Msg.Manual

module LP = LowParse.Low.Base

open FStar.BaseTypes

type msg = {
  x : uint32;
  y : uint32;
}

inline_for_extraction noextract let msg_parser_kind = LP.strong_parser_kind 8 8 ({ LP.parser_kind_metadata_total = true })

noextract val msg_parser : LP.parser msg_parser_kind msg

inline_for_extraction val msg_validator32 : LP.validator32 msg_parser
inline_for_extraction val msg_parser32 : LP.parser32 msg_parser



