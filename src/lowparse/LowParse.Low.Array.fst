module LowParse.Low.Array
include LowParse.Spec.Array
include LowParse.Low.List
include LowParse.Low.VLData

module L = FStar.List.Tot
module M = LowParse.Math
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module I32 = FStar.Int32

#reset-options "--z3cliopt smt.arith.nl=false"

val list_nth_constant_size_parser_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
  (i: nat)
: Lemma
  (requires (
    k.parser_kind_high == Some k.parser_kind_low /\
    Some? (parse (parse_list p) b) /\ (
    let (Some (l, _)) = parse (parse_list p) b in
    i < L.length l
  )))
  (ensures (
    let j = i `Prims.op_Multiply` k.parser_kind_low in
    0 <= j /\
    j <= Seq.length b /\ (
    let b' = Seq.slice b j (Seq.length b) in
    Some? (parse p b') /\ (
    let (Some (l, _)) = parse (parse_list p) b in
    let (Some (x, _)) = parse p b' in
    x == L.index l i
  ))))
  (decreases (Seq.length b))

let rec list_nth_constant_size_parser_correct #k #t p b i =
  if i = 0
  then ()
  else begin
    M.mult_decomp i k.parser_kind_low;
    list_nth_constant_size_parser_correct p (Seq.slice b k.parser_kind_low (Seq.length b)) (i - 1)
  end

inline_for_extraction
val array_nth
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (array_byte_size32: U32.t)
  (elem_byte_size32: U32.t)
  (i: U32.t)
  (u: unit {
    fldata_array_precond p array_byte_size elem_count == true /\
    U32.v elem_byte_size32 == k.parser_kind_low /\
    U32.v array_byte_size32 == array_byte_size /\
    U32.v i < elem_count
  })
: Tot (accessor (parse_array s array_byte_size elem_count) p (fun x y -> y == L.index x (U32.v i)))

module B = LowStar.Buffer

#set-options "--z3rlimit 16"

let array_nth #k #t #p s array_byte_size elem_count array_byte_size32 elem_byte_size32 i u =
  fun input ->
  let h = HST.get () in
  list_nth_constant_size_parser_correct p (B.as_seq h (gsub input 0ul array_byte_size32)) (U32.v i);
  B.offset (B.sub input 0ul array_byte_size32) (i `U32.mul` elem_byte_size32) <: buffer8

#reset-options

// FIXME: WHY WHY WHY does tc inference not work here?

inline_for_extraction
let validate32_array
  [| cls: validator32_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  [| error_fldata_cls |]
  (s: serializer p)
  (v: validator32 #cls p)
  (array_byte_size: nat)
  (array_byte_size32: I32.t)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond p array_byte_size elem_count == true /\
    I32.v array_byte_size32 == array_byte_size
  })
: Tot (validator32 (parse_array s array_byte_size elem_count))
= validate32_synth
    (validate32_fldata_strong (serialize_list _ s) (validate32_list v) array_byte_size array_byte_size32)
    (fldata_to_array s array_byte_size elem_count ())
    ()

inline_for_extraction
let validate_nochk32_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (array_byte_size32: U32.t)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond p array_byte_size elem_count == true /\
    U32.v array_byte_size32 == array_byte_size
  })
: Tot (validator_nochk32 (parse_array s array_byte_size elem_count))
= validate_nochk32_constant_size (parse_array s array_byte_size elem_count) array_byte_size32 ()

inline_for_extraction
let validate32_vlarray
  [| cls: validator32_cls |]
  (array_byte_size_min: nat)
  (array_byte_size_min32: U32.t { U32.v array_byte_size_min32 = array_byte_size_min } )
  (array_byte_size_max: nat)
  (array_byte_size_max32: U32.t { U32.v array_byte_size_max32 = array_byte_size_max /\ array_byte_size_max < 2147483648 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  [| error_vldata_cls |]
  (s: serializer p)
  (v: validator32 #cls p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true
  })
  (sz32: I32.t { I32.v sz32 == log256' array_byte_size_max } )
: Tot (validator32 (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u))
= vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u;
  validate32_synth
    (validate32_bounded_vldata_strong array_byte_size_min array_byte_size_min32 array_byte_size_max array_byte_size_max32 (serialize_list _ s) (validate32_list v) sz32 ())
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ())
    ()

