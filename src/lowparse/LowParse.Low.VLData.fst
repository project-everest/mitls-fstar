module LowParse.Low.VLData
include LowParse.Low.VLData.Aux
include LowParse.Low.FLData

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST

inline_for_extraction
let parse32_bounded_integer
  (i: integer_size)
: Tot (parser32 (parse_bounded_integer i))
= [@inline_let]
  let _ = integer_size_values i in
  match i with
  | 1 -> parse32_bounded_integer_1 ()
  | 2 -> parse32_bounded_integer_2 ()
  | 3 -> parse32_bounded_integer_3 ()
  | 4 -> parse32_bounded_integer_4 ()

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

inline_for_extraction
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

inline_for_extraction
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

#reset-options

module HS = FStar.HyperStack

assume
val contains_valid_serialized_data_or_fail_serialize_bounded_vldata_strong_intro
  (h: HS.mem)
  (min: nat)
  (max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (b: buffer8)
  (lo: I32.t)
  (hi: I32.t)
  (x: t)
: Lemma
  (requires (
    min <= max /\ max > 0 /\ max < 4294967296 /\ (
    let sz : integer_size = log256' max in
    I32.v lo >= sz /\ I32.v lo <= I32.v hi /\ (
      let hilo = I32.v hi - I32.v lo in
      min <= hilo /\ hilo <= max /\
      contains_valid_serialized_data_or_fail h s b lo x hi /\
      contains_valid_serialized_data_or_fail h (serialize_bounded_integer sz) b (I32.sub lo (I32.int_to_t sz)) (U32.uint_to_t hilo) lo
  ))))
  (ensures (
    let sz : integer_size = log256' max in
    parse_bounded_vldata_strong_pred min max s x /\
    contains_valid_serialized_data_or_fail h (serialize_bounded_vldata_strong min max s) b (I32.sub lo (I32.int_to_t sz)) x hi
  ))

assume
val serialize32_bounded_integer
  (min: nat)
  (max: nat)
  (u: unit {
    min <= max /\ max > 0 /\ max < 4294967296
  })
: Tot (serializer32 (serialize_bounded_integer (log256' max)))

#set-options "--z3rlimit 16"

inline_for_extraction
let serialize32_bounded_vldata_strong_size
  (min: nat)
  (max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (b: buffer8)
  (lo: I32.t)
  (hi: I32.t)
: HST.Stack bool
  (requires (fun h ->
    min <= max /\ max > 0 /\ max < 4294967296 /\ (
    let sz : integer_size = log256' max in
    B.live h b /\ I32.v lo <= B.length b
  )))
  (ensures (fun h res h' ->
    let sz : integer_size = log256' max in
    res == (I32.v lo >= sz && I32.v lo <= I32.v hi && (let hilo = I32.v hi - I32.v lo in min <= hilo && hilo <= max)) /\ (
    if res
    then (
      forall (x: t) .  {:pattern (contains_valid_serialized_data_or_fail h s b lo x hi) }
        contains_valid_serialized_data_or_fail h s b lo x hi ==> (
        B.modifies (loc_ibuffer b (I32.sub lo (I32.int_to_t sz)) hi) h h' /\
        (parse_bounded_vldata_strong_pred min max s x /\
          contains_valid_serialized_data_or_fail h' (serialize_bounded_vldata_strong min max s) b (I32.sub lo (I32.int_to_t sz)) x hi)
    ))
    else
      B.modifies B.loc_none h h'
  )))
= let h0 = HST.get () in
  [@inline_let]
  let sz : integer_size = log256' max in
  FStar.Int.pow2_values 31;
  [@inline_let]
  let sz32i = I32.int_to_t sz in
  if lo `I32.gte` sz32i && lo `I32.lte` hi
  then
    let hilo = Cast.int32_to_uint32 (hi `I32.sub` lo) in
    if U32.uint_to_t min `U32.lte` hilo && hilo `U32.lte` U32.uint_to_t max
    then begin
      serialize32_bounded_integer min max () b (Cast.int32_to_uint32 (lo `I32.sub` sz32i)) hilo;
      let h = HST.get () in
      let f
        (x: t)
      : Lemma
        (requires (contains_valid_serialized_data_or_fail h0 s b lo x hi))
        (ensures (
          B.modifies (loc_ibuffer b (I32.sub lo (I32.int_to_t sz)) hi) h0 h /\
          parse_bounded_vldata_strong_pred min max s x /\
          contains_valid_serialized_data_or_fail h (serialize_bounded_vldata_strong min max s) b (I32.sub lo (I32.int_to_t sz)) x hi
        ))
      = contains_valid_serialized_data_or_fail_elim h0 s b lo x hi;
        exactly_contains_valid_data_contains_valid_serialized_data_or_fail h (serialize_bounded_integer sz) b (Cast.int32_to_uint32 (I32.sub lo (I32.int_to_t sz))) hilo (Cast.int32_to_uint32 lo);
        loc_ibuffer_eq b (I32.sub lo (I32.int_to_t sz)) lo;
        contains_valid_serialized_data_or_fail_serialize_bounded_vldata_strong_intro h min max s b lo hi x;
        ()
      in
      Classical.forall_intro (Classical.move_requires f);
      true
    end
    else false
  else
    false

#reset-options
