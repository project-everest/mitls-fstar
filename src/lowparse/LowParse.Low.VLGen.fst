module LowParse.Low.VLGen
include LowParse.Spec.VLGen
include LowParse.Low.VLData

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

let gaccessor_bounded_vlgen_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 ( min) ( max)))
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot (gaccessor (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s))
= fun input ->
  parse_bounded_vlgen_unfold min max pk s input;
  let res =
    match parse pk input with
    | None -> (0, 0) // dummy
    | Some (len, sz)  ->
      (sz, Seq.length input - sz)
  in
  (res <: (res : _ { gaccessor_post' (parse_bounded_vlgen min max pk s) p (clens_bounded_vldata_strong_payload min max s) input res } ))

module B = LowStar.Buffer

inline_for_extraction
let accessor_bounded_vlgen_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 ( min) ( max)))
  (jk: jumper pk)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot (accessor (gaccessor_bounded_vlgen_payload min max pk s))
= fun input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ =
    slice_access_eq_inv h (gaccessor_bounded_vlgen_payload min max pk s) input pos;
    valid_facts (parse_bounded_vlgen min max pk s) h input pos;
    parse_bounded_vlgen_unfold_aux min max pk s (bytes_of_slice_from h input pos);
    valid_facts pk h input pos;
    parse_strong_prefix pk (bytes_of_slice_from h input pos) (B.as_seq h (B.gsub input.base pos (U32.uint_to_t (content_length (parse_bounded_vlgen min max pk s) h input pos))))
  in
  jk input pos

let gaccessor_vlgen_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 ( min) ( max)))
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond min max k } )
: Tot (gaccessor (parse_vlgen min max pk s) p (clens_id _))
= fun input ->
  parse_vlgen_unfold min max pk s input;
  let res =
    match parse pk input with
    | None -> (0, 0) // dummy
    | Some (len, sz)  ->
      (sz, Seq.length input - sz)
  in
  (res <: (res : _ { gaccessor_post' (parse_vlgen min max pk s) p (clens_id _) input res } ))

inline_for_extraction
let accessor_vlgen_payload
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#sk: parser_kind)
  (#pk: parser sk (bounded_int32 ( min) ( max)))
  (jk: jumper pk { sk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p { parse_vlgen_precond min max k } )
: Tot (accessor (gaccessor_vlgen_payload min max pk s))
= fun input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ =
    slice_access_eq_inv h (gaccessor_vlgen_payload min max pk s) input pos;
    valid_facts (parse_vlgen min max pk s) h input pos;
    parse_vlgen_unfold min max pk s (bytes_of_slice_from h input pos);
    valid_facts pk h input pos;
    parse_strong_prefix pk (bytes_of_slice_from h input pos) (B.as_seq h (B.gsub input.base pos (U32.uint_to_t (content_length (parse_vlgen min max pk s) h input pos))))
  in
  jk input pos

#pop-options
