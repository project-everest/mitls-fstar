module LowParse.Low.VLGen
include LowParse.Spec.VLGen
include LowParse.Low.FLData

module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

#push-options "--z3rlimit 16"

inline_for_extraction
let validate_bounded_vlgen
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 (U32.v min) (U32.v max)))
  (vk: validator pk)
  (rk: leaf_reader pk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (v: validator p)
: Tot (validator (parse_bounded_vlgen (U32.v min) (U32.v max) pk s))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts (parse_bounded_vlgen (U32.v min) (U32.v max) pk s) h input pos;
    parse_bounded_vlgen_unfold (U32.v min) (U32.v max) pk s (bytes_of_slice_from h input pos);
    valid_facts pk h input pos
  in
  let n = vk input pos in
  if validator_max_length `U32.lt` n
  then n
  else
    let len = rk input pos in
    [@inline_let]
    let _ = valid_facts (parse_fldata_strong s (U32.v len)) h input n in
    validate_fldata_strong s v (U32.v len) len input n

inline_for_extraction
let validate_vlgen
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 (U32.v min) (U32.v max)))
  (vk: validator pk)
  (rk: leaf_reader pk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond (U32.v min) (U32.v max) k })
  (v: validator p)
: Tot (validator (parse_vlgen (U32.v min) (U32.v max) pk s))
= validate_synth
    (validate_bounded_vlgen min max pk vk rk s v)
    (synth_vlgen (U32.v min) (U32.v max) s)
    ()

inline_for_extraction
let jump_bounded_vlgen
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 (U32.v min) (U32.v max)))
  (vk: jumper pk)
  (rk: leaf_reader pk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond (U32.v min) (U32.v max) k })
  (v: jumper p)
: Tot (jumper (parse_bounded_vlgen (U32.v min) (U32.v max) pk s))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts (parse_bounded_vlgen (U32.v min) (U32.v max) pk s) h input pos;
    parse_bounded_vlgen_unfold (U32.v min) (U32.v max) pk s (bytes_of_slice_from h input pos);
    valid_facts pk h input pos
  in
  let n = vk input pos in
  let len = rk input pos in
  [@inline_let]
  let _ = valid_facts (parse_fldata_strong s (U32.v len)) h input n in
  jump_fldata_strong s (U32.v len) len input n

inline_for_extraction
let jump_vlgen
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 (U32.v min) (U32.v max)))
  (vk: jumper pk)
  (rk: leaf_reader pk)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond (U32.v min) (U32.v max) k })
  (v: jumper p)
: Tot (jumper (parse_vlgen (U32.v min) (U32.v max) pk s))
= jump_synth
    (jump_bounded_vlgen min max pk vk rk s v)
    (synth_vlgen (U32.v min) (U32.v max) s)
    ()
