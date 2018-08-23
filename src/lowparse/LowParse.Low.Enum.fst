module LowParse.Low.Enum
include LowParse.Spec.Enum
include LowParse.Low.Combinators

module T = LowParse.SLow.Tac.Sum

inline_for_extraction
let validate32_maybe_enum_key (#key #repr: eqtype) (#k: parser_kind) (#p: parser k repr) (v: validator32 p) (e: enum key repr) : Tot (validator32 (parse_maybe_enum_key p e)) =
  validate32_synth v (maybe_enum_key_of_repr e) ()

module I32 = FStar.Int32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

inline_for_extraction
let validate32_enum_key (#key #repr: eqtype) (#k: parser_kind) (#p: parser k repr) (v: validator32 p) (p32: parser32 p) (e: enum key repr) (destr: T.maybe_enum_destr_t bool e) : Tot (validator32 (parse_enum_key p e)) =
  fun input sz ->
    let h = HST.get () in
    parse_enum_key_eq p e (B.as_seq h input);
    let consumed = v input sz in
    if consumed `I32.lt` 0l
    then consumed
    else
      let r = p32 input in
      if destr eq2 (T.default_if bool) (fun _ -> ()) (fun _ _ _ -> ()) (Known?) r
      then consumed
      else (-1l)
