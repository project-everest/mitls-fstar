module LowParse.Low.Option
include LowParse.Spec.Option
include LowParse.Low.Base

module I32 = FStar.Int32

inline_for_extraction
let validate32_option (#k: parser_kind) (#t: Type) (#p: parser k t) (v: validator32 p) : Tot (validator32 (parse_option p)) =
  fun input len ->
  let r = v input len in
  if r `I32.lt` 0l
  then len
  else r
