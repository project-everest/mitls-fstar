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

(* QuackyDucky-specific: "flat" enums with baked-in Unknown case *)

inline_for_extraction
let validate32_flat_maybe_enum_key
  (#key #repr: eqtype)
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k repr)
  (v: validator32 p)
  (p32: parser32 p)
  (e: enum key repr)
  (f: (maybe_enum_key e -> GTot t))
  (unknown: (t -> GTot bool))
  (destr: T.maybe_enum_destr_t bool e)
  (u: squash (
    synth_injective f
  ))
  (lemma: (
    (k: maybe_enum_key e) -> 
    Lemma
    (Unknown? k <==> unknown (f k))
  ))
: Tot (validator32 ((parse_maybe_enum_key p e `parse_synth` f) `parse_filter` (fun x -> not (unknown x))))
= fun input sz ->
  let h = HST.get () in
  parse_synth_eq (parse_maybe_enum_key p e) f (B.as_seq h input);
  parse_filter_eq (parse_maybe_enum_key p e `parse_synth` f) (fun x -> not (unknown x)) (B.as_seq h input);
  let consumed = v input sz in
  if consumed `I32.lt` 0l
  then consumed
  else begin
    Classical.forall_intro lemma;
    let r = p32 input in
    if destr eq2 (T.default_if bool) (fun _ -> ()) (fun _ _ _ -> ()) (Known?) r
    then consumed
    else (-1l)
  end
