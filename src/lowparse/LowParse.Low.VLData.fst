module LowParse.Low.VLData
include LowParse.Spec.VLData
include LowParse.Low.FLData

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

module I32 = FStar.Int32

inline_for_extraction
let validate32_bounded_integer
  (i: integer_size)
  (i32: I32.t { I32.v i32 == i } )
: Tot (validator32 (parse_bounded_integer i))
= validate32_total_constant_size (parse_bounded_integer i) i32 ()

module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

inline_for_extraction
let validate32_vldata_payload
  (sz: integer_size)
  (f: ((x: bounded_integer sz) -> GTot bool))
  (f_lemma: ((x: bounded_integer sz) -> Lemma (f x == true ==> U32.v x < 2147483648)))
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator32 p)
  (i: bounded_integer sz { f i == true } )
: Tot (validator32 (parse_vldata_payload sz f p i))
= (* eta expansion needed because of `weaken` *)
  fun input len ->
    Classical.forall_intro f_lemma;
    validate32_fldata v (U32.v i) (Cast.uint32_to_int32 i) input len

inline_for_extraction
let validate32_vldata_gen
  (sz: integer_size)
  (sz32: I32.t { I32.v sz32 == sz } )
  (f: ((x: bounded_integer sz) -> GTot bool))
  (f_lemma: ((x: bounded_integer sz) -> Lemma (f x == true ==> U32.v x < 2147483648)))
  (f' : ((x: bounded_integer sz) -> Tot (y: bool { y == f x })))
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v32: validator32 p)
: Tot (validator32 (parse_vldata_gen sz f p))
= parse_fldata_and_then_cases_injective sz f p;
  parse_vldata_gen_kind_correct sz;
  validate32_filter_and_then
    (validate32_bounded_integer sz sz32)
    (parse32_bounded_integer sz)
    f
    f'
    #_ #_ #(parse_vldata_payload sz f p)
    (validate32_vldata_payload sz f f_lemma v32)
    ()

#set-options "--z3rlimit 32"

inline_for_extraction
let validate32_bounded_vldata
  (min: nat)
  (min32: U32.t)
  (max: nat)
  (max32: U32.t)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator32 p)
  (sz32: I32.t)
  (u: unit {
    U32.v min32 == min /\
    U32.v max32 == max /\
    min <= max /\ max > 0 /\ max < 2147483648 /\
    I32.v sz32 == log256' max
  })
: Tot (validator32 (parse_bounded_vldata min max p))
= [@inline_let]
  let sz : integer_size = log256' max in
  fun input len ->
    validate32_vldata_gen sz sz32 (in_bounds min max) (fun _ -> ()) (fun i -> not (U32.lt i min32 || U32.lt max32 i)) v input len

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
    min <= max /\ max > 0 /\ max < 2147483648 /\
    I32.v sz32 == log256' max
  })
: Tot (validator32 (parse_bounded_vldata_strong min max s))
= fun input len ->
  validate32_bounded_vldata min min32 max max32 v sz32 () input len

#set-options "--z3rlimit 64"

let accessor_bounded_vldata_payload
  (min: nat)
  (max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz32: U32.t)
  (u: unit {
    min <= max /\ max > 0 /\ max < 4294967296 /\
    U32.v sz32 == log256' max
  })
: Tot (accessor (parse_bounded_vldata min max p) p (fun x y -> y == x))
= [@inline_let]
  let sz = log256' max in
  fun input ->
  let h = HST.get () in
  parse_bounded_vldata_elim_forall min max p (B.as_seq h input);
  let len = parse32_bounded_integer sz input in
  B.sub (B.offset input sz32) 0ul len

let accessor_bounded_vldata_strong_payload
  (min: nat)
  (max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz32: U32.t)
  (u: unit {
    min <= max /\ max > 0 /\ max < 4294967296 /\
    U32.v sz32 == log256' max
  })
: Tot (accessor (parse_bounded_vldata_strong min max s) p (fun x y -> y == x))
= fun input -> accessor_bounded_vldata_payload min max p sz32 () input
