module LowParse.Low.Array

include LowParse.Spec.Array
include LowParse.Low.List
include LowParse.Low.VLData

module L = FStar.List.Tot
module M = LowParse.Math
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 16"

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
  (decreases i)

let rec list_nth_constant_size_parser_correct #k #t p b i =
  parse_list_eq p b;
  if i = 0
  then ()
  else begin
    M.mult_decomp i k.parser_kind_low;
    list_nth_constant_size_parser_correct p (Seq.slice b k.parser_kind_low (Seq.length b)) (i - 1)
  end

let clens_array_nth
  (t: Type)
  (elem_count: nat)
  (i: nat { i < elem_count } )
: Tot (clens (array t elem_count) t)
= {
  clens_cond = (fun _ -> True);
  clens_get = (fun (l: array t elem_count) -> L.index l i);
}

#reset-options "--z3rlimit 16"

abstract
let array_nth_ghost'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (i: nat {
    fldata_array_precond p array_byte_size elem_count == true /\
    array_byte_size < 4294967296 /\
    elem_count < 4294967296 /\
    i < elem_count
  })
  (input: bytes)
: GTot (nat * nat)
= if (i `Prims.op_Multiply` k.parser_kind_low) + k.parser_kind_low <= Seq.length input
  then (i `Prims.op_Multiply` k.parser_kind_low, k.parser_kind_low)
  else (0, 0) // dummy

abstract
let array_nth_ghost_correct'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (i: nat {
    fldata_array_precond p array_byte_size elem_count == true /\
    array_byte_size < 4294967296 /\
    elem_count < 4294967296 /\
    i < elem_count
  })
  (input: bytes)
: Lemma
  (requires (gaccessor_pre (parse_array s array_byte_size elem_count) p (clens_array_nth t elem_count i) input))
  (ensures (gaccessor_post' (parse_array s array_byte_size elem_count) p (clens_array_nth t elem_count i) input (array_nth_ghost' s array_byte_size elem_count i input)))
= fldata_to_array_inj s array_byte_size elem_count ();
  parse_synth_eq (parse_fldata_strong (serialize_list _ s) array_byte_size) (fldata_to_array s array_byte_size elem_count ()) input;
  list_nth_constant_size_parser_correct p input i;
  let off = i `Prims.op_Multiply` k.parser_kind_low in
  parse_strong_prefix p (Seq.slice input off (Seq.length input)) (Seq.slice input off (off + k.parser_kind_low))

abstract
let array_nth_ghost_correct
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (i: nat {
    fldata_array_precond p array_byte_size elem_count == true /\
    array_byte_size < 4294967296 /\
    elem_count < 4294967296 /\
    i < elem_count
  })
  (input: bytes)
: Lemma
  (gaccessor_post' (parse_array s array_byte_size elem_count) p (clens_array_nth t elem_count i) input (array_nth_ghost' s array_byte_size elem_count i input))
= Classical.move_requires (array_nth_ghost_correct' s array_byte_size elem_count i) input

abstract
let array_nth_ghost
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (i: nat {
    fldata_array_precond p array_byte_size elem_count == true /\
    array_byte_size < 4294967296 /\
    elem_count < 4294967296 /\
    i < elem_count
  })
: Tot (gaccessor (parse_array s array_byte_size elem_count) p (clens_array_nth t elem_count i))
= fun input -> ((
  array_nth_ghost_correct s array_byte_size elem_count i input;
  array_nth_ghost' s array_byte_size elem_count i input) <: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' (parse_array s array_byte_size elem_count) p (clens_array_nth t elem_count i) input res)))

module B = LowStar.Buffer

inline_for_extraction
let array_nth
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (array_byte_size: nat)
  (elem_count: nat)
  (i: U32.t {
    fldata_array_precond p (array_byte_size) (elem_count) == true /\
    array_byte_size < 4294967296 /\
    elem_count < 4294967296 /\
    U32.v i < elem_count
  })
: Tot (accessor (array_nth_ghost s (array_byte_size) (elem_count) (U32.v i)))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts (parse_array s (array_byte_size) (elem_count)) h input pos;
    slice_access_eq h (array_nth_ghost s (array_byte_size) (elem_count) (U32.v i)) input pos;
    fldata_to_array_inj s (array_byte_size) (elem_count) ();
    parse_synth_eq (parse_fldata_strong (serialize_list _ s) (array_byte_size)) (fldata_to_array s array_byte_size elem_count ()) (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos)));
    list_nth_constant_size_parser_correct p (B.as_seq h (B.gsub (B.gsub input.base pos (input.len `U32.sub` pos)) 0ul (U32.uint_to_t array_byte_size))) (U32.v i)
  in
  pos `U32.add` (i `U32.mul` U32.uint_to_t k.parser_kind_low)

inline_for_extraction
let validate_array
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: validator p)
  (array_byte_size: nat)
  (array_byte_size32: U32.t)
  (elem_count: nat)
  (u: unit {
    fldata_array_precond p array_byte_size elem_count == true /\
    U32.v array_byte_size32 == array_byte_size
  })
: Tot (validator (parse_array s array_byte_size elem_count))
= validate_synth
    (validate_fldata_strong (serialize_list _ s) (validate_list v ()) array_byte_size array_byte_size32)
    (fldata_to_array s array_byte_size elem_count ())
    ()

inline_for_extraction
let jump_array
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
: Tot (jumper (parse_array s array_byte_size elem_count))
= jump_constant_size (parse_array s array_byte_size elem_count) array_byte_size32 ()

inline_for_extraction
let validate_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: validator p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true
  })
  (sz32: U32.t { U32.v sz32 == log256' array_byte_size_max /\ array_byte_size_max <= U32.v validator_max_length } )
: Tot (validator (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u))
= vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u;
  validate_synth
    (validate_bounded_vldata_strong array_byte_size_min array_byte_size_max (serialize_list _ s) (validate_list v ()) ())
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ())
    ()

inline_for_extraction
let jump_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true
  })
  (sz32: U32.t { U32.v sz32 == log256' array_byte_size_max } )
: Tot (jumper (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u))
= vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u;
  jump_synth
    (jump_bounded_vldata_strong array_byte_size_min array_byte_size_max (serialize_list _ s) ())
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ())
    ()

inline_for_extraction
let finalize_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (sl: slice)
  (pos pos' : U32.t)
: HST.Stack unit
  (requires (fun h ->
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true /\ (
    let vpos1 = U32.v pos + log256' array_byte_size_max in
    vpos1 < 4294967296 /\ (
    let pos1 = U32.uint_to_t vpos1 in
    let len = U32.v pos' - vpos1 in
    valid_list p h sl pos1 pos' /\ (
    let count = L.length (contents_list p h sl pos1 pos') in
    ((array_byte_size_min <= len /\ len <= array_byte_size_max) \/ (elem_count_min <= count /\ count <= elem_count_max))
  )))))
  (ensures (fun h _ h' ->
    let pos1 = (U32.uint_to_t (U32.v pos + log256' array_byte_size_max)) in
    let l = contents_list p h sl pos1 pos' in
    B.modifies (loc_slice_from_to sl pos pos1) h h' /\
    elem_count_min <= L.length l /\ L.length l <= elem_count_max /\
    valid_content_pos (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ()) h' sl pos l pos'
  ))
= let h = HST.get () in
  let pos1 = pos `U32.add` U32.uint_to_t (log256' array_byte_size_max) in
  valid_list_valid_exact_list p h sl pos1 pos';
  let l = Ghost.hide (contents_list p h sl pos1 pos') in
  let _ : squash (let count = L.length (Ghost.reveal l) in elem_count_min <= count /\ count <= elem_count_max) =
    valid_exact_serialize (serialize_list _ s) h sl pos1 pos' ;
    Classical.move_requires (vldata_to_vlarray_correct array_byte_size_min array_byte_size_max s elem_count_min elem_count_max) (Ghost.reveal l) 
  in
  vlarray_to_vldata_correct array_byte_size_min array_byte_size_max s elem_count_min elem_count_max (Ghost.reveal l);
  finalize_bounded_vldata_strong array_byte_size_min array_byte_size_max (serialize_list _ s) sl pos pos' ;
  let h = HST.get () in
  valid_synth h (parse_bounded_vldata_strong array_byte_size_min array_byte_size_max (serialize_list _ s)) (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max ())  sl pos
