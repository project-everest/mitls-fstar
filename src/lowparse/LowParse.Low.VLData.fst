module LowParse.Low.VLData
include LowParse.Spec.VLData
include LowParse.Low.Combinators

module B = LowStar.Buffer
module E = LowParse.BigEndianImpl.Low
module HST = FStar.HyperStack.ST

inline_for_extraction
let parse32_bounded_integer_1 : (parser32 (parse_bounded_integer 1)) =
  decode_bounded_integer_injective 1;
  make_total_constant_size_parser32 1 1ul #(bounded_integer 1) (decode_bounded_integer 1) () (fun input ->
    let h = HST.get () in
    let r = E.be_to_n_1 _ _ (E.u32 ()) input in
    E.lemma_be_to_n_is_bounded (B.as_seq h input);
    r
  )

inline_for_extraction
let parse32_bounded_integer_2 : (parser32 (parse_bounded_integer 2)) =
  decode_bounded_integer_injective 2;
  make_total_constant_size_parser32 2 2ul #(bounded_integer 2) (decode_bounded_integer 2) () (fun input ->
    let h = HST.get () in
    let r = E.be_to_n_2 _ _ (E.u32 ()) input in
    E.lemma_be_to_n_is_bounded (B.as_seq h input);
    r
  )

inline_for_extraction
let parse32_bounded_integer_3 : (parser32 (parse_bounded_integer 3)) =
  decode_bounded_integer_injective 3;
  make_total_constant_size_parser32 3 3ul #(bounded_integer 3) (decode_bounded_integer 3) () (fun input ->
    let h = HST.get () in
    let r = E.be_to_n_3 _ _ (E.u32 ()) input in
    E.lemma_be_to_n_is_bounded (B.as_seq h input);
    r
  )

inline_for_extraction
let parse32_bounded_integer_4 : (parser32 (parse_bounded_integer 4)) =
  decode_bounded_integer_injective 4;
  make_total_constant_size_parser32 4 4ul #(bounded_integer 4) (decode_bounded_integer 4) () (fun input ->
    let h = HST.get () in
    let r = E.be_to_n_4 _ _ (E.u32 ()) input in
    E.lemma_be_to_n_is_bounded (B.as_seq h input);
    r
  )

inline_for_extraction
let parse32_bounded_integer
  (i: integer_size)
: Tot (parser32 (parse_bounded_integer i))
= [@inline_let]
  let _ = integer_size_values i in
  match i with
  | 1 -> parse32_bounded_integer_1
  | 2 -> parse32_bounded_integer_2
  | 3 -> parse32_bounded_integer_3
  | 4 -> parse32_bounded_integer_4

module U32 = FStar.UInt32

(*
inline_for_extraction
let validate32_bounded_vldata_strong
  (min: nat)
  (min32: U32.t)
  (max: nat)
  (max32: U32.t)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: validator32 p)
  (sz32: I32.t)
  (u: unit {
    U32.v min32 == min /\
    U32.v max32 == max /\
    min <= max /\ max > 0 /\ max < 4294967296 /\
    I32.v sz32 == log256' max
  })
: Tot (validator32 (parse_bounded_vldata_strong min max s))
= [@inline_let]
  let _ = parse_bounded_vldata_correct min max p in
  [@inline_let]
  let sz : integer_size = (log256' max) in
  fun input len ->
  let res1 = validate32_total_constant_size (parse_bounded_integer sz) sz' () in
  if res1 `I32.lt` 0l
  then res1
  else
    let v1 = parse32_bounded_integer sz input in
    
