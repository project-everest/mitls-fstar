module LowParse.Low.VLData
include LowParse.Low.VLData.Aux
include LowParse.Low.FLData

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32

inline_for_extraction
let read_bounded_integer
  (i: integer_size)
: Tot (leaf_reader (parse_bounded_integer i))
= [@inline_let]
  let _ = integer_size_values i in
  match i with
  | 1 -> read_bounded_integer_1 ()
  | 2 -> read_bounded_integer_2 ()
  | 3 -> read_bounded_integer_3 ()
  | 4 -> read_bounded_integer_4 ()

inline_for_extraction
let validate_bounded_integer
  [| validator_cls |]
  (i: integer_size) // must be a constant
: Tot (validator (parse_bounded_integer i))
= validate_total_constant_size (parse_bounded_integer i) (U32.uint_to_t i) ()

inline_for_extraction
let validate_vldata_payload
  [| validator_cls |]
  (sz: integer_size)
  (f: ((x: bounded_integer sz) -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator p)
  (i: bounded_integer sz { f i == true } )
: Tot (validator (parse_vldata_payload sz f p i))
= validate_weaken (parse_vldata_payload_kind sz) (validate_fldata v (U32.v i) i) ()

inline_for_extraction
let validate_vldata_gen
  [| validator_cls |]
  (sz: integer_size) // must be a constant
  (f: ((x: bounded_integer sz) -> GTot bool))
  (f' : ((x: bounded_integer sz) -> Tot (y: bool { y == f x })))
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator p)
: Tot (validator (parse_vldata_gen sz f p))
= parse_fldata_and_then_cases_injective sz f p;
  parse_vldata_gen_kind_correct sz;
  validate_filter_and_then
    (validate_bounded_integer sz)
    (read_bounded_integer sz)
    f
    f'
    #_ #_ #(parse_vldata_payload sz f p)
    (validate_vldata_payload sz f v)
    ()

#push-options "--z3rlimit 32 --initial_ifuel 4 --max_ifuel 4"

module HS = FStar.HyperStack

let valid_vldata_gen_elim
  (h: HS.mem)
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: slice)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_vldata_gen sz f p) h input pos
  ))
  (ensures (
    valid (parse_bounded_integer sz) h input pos /\ (
    let len_payload = contents (parse_bounded_integer sz) h input pos in
    f len_payload == true /\
    sz + U32.v len_payload == content_length (parse_vldata_gen sz f p) h input pos /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_pos (parse_vldata_gen sz f p) h input pos (pos_payload `U32.add` len_payload) /\
    valid_exact p h input pos_payload (pos_payload `U32.add` len_payload) /\
    contents_exact p h input pos_payload (pos_payload `U32.add` len_payload) == contents (parse_vldata_gen sz f p) h input pos
  ))))
= valid_facts (parse_vldata_gen sz f p) h input pos;
  valid_facts (parse_bounded_integer sz) h input pos;
  parse_vldata_gen_eq sz f p (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos)));
  let len_payload = contents (parse_bounded_integer sz) h input pos in
  let pos_payload = pos `U32.add` U32.uint_to_t sz in
  valid_exact_equiv p h input pos_payload (pos_payload `U32.add` len_payload);
  contents_exact_eq p h input pos_payload (pos_payload `U32.add` len_payload)

#pop-options

inline_for_extraction
let jump_vldata_gen
  (sz: integer_size) // must be a constant
  (f: ((x: bounded_integer sz) -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (jumper (parse_vldata_gen sz f p))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_vldata_gen_elim h sz f p input pos in
  pos `U32.add` (U32.uint_to_t sz `U32.add` read_bounded_integer sz input pos)

inline_for_extraction
let validate_bounded_vldata
  [| validator_cls |]
  (min: nat) // must be a constant
  (max: nat) // must be a constant
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator p)
  (u: unit {
    min <= max /\
    max > 0 /\
    max <= U32.v validator_max_length
  })
: Tot (validator (parse_bounded_vldata min max p))
= [@inline_let]
  let sz : integer_size = log256' max in
  [@inline_let]
  let _ = parse_bounded_vldata_correct min max p in
  validate_strengthen
    (parse_bounded_vldata_kind min max)
    (validate_vldata_gen sz (in_bounds min max) (fun i -> not (U32.lt i (U32.uint_to_t min) || U32.lt (U32.uint_to_t max) i)) v)
    ()

inline_for_extraction
let jump_bounded_vldata
  (min: nat) // must be a constant
  (max: nat) // must be a constant
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (u: unit {
    min <= max /\
    max > 0 /\
    max < 4294967296
  })
: Tot (jumper (parse_bounded_vldata min max p))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let sz = log256' max in
  [@inline_let] let _ = valid_facts (parse_bounded_vldata min max p) h input pos in
  [@inline_let] let _ = valid_facts (parse_vldata_gen sz (in_bounds min max) p) h input pos in
  jump_vldata_gen sz (in_bounds min max) p input pos

inline_for_extraction
let validate_bounded_vldata_strong
  [| validator_cls |]
  (min: nat) // must be a constant
  (max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: validator p)
  (u: unit {
    min <= max /\ max > 0 /\ max <= U32.v validator_max_length
  })
: Tot (validator (parse_bounded_vldata_strong min max s))
= fun input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ = valid_facts (parse_bounded_vldata_strong min max s) h input pos in
  [@inline_let]
  let _ = valid_facts (parse_bounded_vldata min max p) h input pos in
  validate_bounded_vldata min max v () input pos

inline_for_extraction
let jump_bounded_vldata_strong
  (min: nat) // must be a constant
  (max: nat)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (u: unit {
    min <= max /\ max > 0 /\ max < 4294967296
  })
: Tot (jumper (parse_bounded_vldata_strong min max s))
= fun (input: slice) pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts (parse_bounded_vldata_strong min max s) h input pos in
  [@inline_let] let _ = valid_facts (parse_bounded_vldata min max p) h input pos in
  jump_bounded_vldata min max p () input pos

inline_for_extraction
let write_bounded_integer
  (i: integer_size)
: Tot (leaf_writer_strong (serialize_bounded_integer i))
= [@inline_let]
  let _ = integer_size_values i in
  match i with
  | 1 -> write_bounded_integer_1 ()
  | 2 -> write_bounded_integer_2 ()
  | 3 -> write_bounded_integer_3 ()
  | 4 -> write_bounded_integer_4 ()

inline_for_extraction
let write_bounded_integer_weak
  (i: integer_size)
: Tot (leaf_writer_weak (serialize_bounded_integer i))
= [@inline_let]
  let _ = integer_size_values i in
  match i with
  | 1 -> write_bounded_integer_1_weak ()
  | 2 -> write_bounded_integer_2_weak ()
  | 3 -> write_bounded_integer_3_weak ()
  | 4 -> write_bounded_integer_4_weak ()

#push-options "--z3rlimit 32 --initial_ifuel 4 --max_ifuel 4"

let valid_vldata_gen_intro
  (h: HS.mem)
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_exact p h input pos_payload pos' /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    bounded_integer_prop sz len_payload /\
    f len_payload == true /\
    valid (parse_bounded_integer sz) h input pos /\
    contents (parse_bounded_integer sz) h input pos == len_payload
  ))))
  (ensures (
    valid_content_pos (parse_vldata_gen sz f p) h input pos (contents_exact p h input (pos `U32.add` U32.uint_to_t sz) pos') pos'
  ))
= valid_facts (parse_vldata_gen sz f p) h input pos;
  valid_facts (parse_bounded_integer sz) h input pos;
  parse_vldata_gen_eq sz f p (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos)));
  contents_exact_eq p h input (pos `U32.add` U32.uint_to_t sz) pos'

#pop-options

inline_for_extraction
let finalize_vldata_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: slice)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack unit
  (requires (fun h ->
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_exact p h input pos_payload pos' /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    bounded_integer_prop sz len_payload /\
    f len_payload == true
  ))))
  (ensures (fun h _ h' ->
    B.modifies (loc_slice_from_to input pos (pos `U32.add` U32.uint_to_t sz)) h h' /\
    valid_content_pos (parse_vldata_gen sz f p) h' input pos (contents_exact p h input (pos `U32.add` U32.uint_to_t sz) pos') pos'
  ))
= [@inline_let]
  let len_payload = pos' `U32.sub` (pos `U32.add` U32.uint_to_t sz) in
  let _ = write_bounded_integer sz len_payload input pos in
  let h = HST.get () in
  valid_vldata_gen_intro h sz f p input pos pos'

let valid_bounded_vldata_elim
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: slice)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bounded_vldata min max p) h input pos
  ))
  (ensures (
    let sz = log256' max in
    valid (parse_bounded_integer sz) h input pos /\ (
    let len_payload = contents (parse_bounded_integer sz) h input pos in
    min <= U32.v len_payload /\ U32.v len_payload <= max /\
    sz + U32.v len_payload == content_length (parse_bounded_vldata min max p) h input pos /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_pos (parse_bounded_vldata min max p) h input pos (pos_payload `U32.add` len_payload) /\
    valid_exact p h input pos_payload (pos_payload `U32.add` len_payload) /\
    contents_exact p h input pos_payload (pos_payload `U32.add` len_payload) == contents (parse_bounded_vldata min max p) h input pos
  ))))
= valid_facts (parse_bounded_vldata min max p) h input pos;
  let sz = log256' max in
  valid_facts (parse_vldata_gen sz (in_bounds min max) p) h input pos;
  valid_vldata_gen_elim h sz (in_bounds min max) p input pos

let valid_bounded_vldata_intro
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    let sz = log256' max in
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_exact p h input pos_payload pos' /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    min <= U32.v len_payload /\ U32.v len_payload <= max /\
    valid (parse_bounded_integer sz) h input pos /\
    contents (parse_bounded_integer sz) h input pos == len_payload
  ))))
  (ensures (
    let sz = log256' max in
    valid_content_pos (parse_bounded_vldata min max p) h input pos (contents_exact p h input (pos `U32.add` U32.uint_to_t sz) pos') pos'
  ))
= valid_facts (parse_bounded_vldata min max p) h input pos;
  valid_facts (parse_vldata_gen (log256' max) (in_bounds min max) p) h input pos;
  valid_vldata_gen_intro h (log256' max) (in_bounds min max) p input pos pos'

let valid_bounded_vldata_strong_elim
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (input: slice)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bounded_vldata_strong min max s) h input pos
  ))
  (ensures (
    let sz = log256' max in
    valid (parse_bounded_integer sz) h input pos /\ (
    let len_payload = contents (parse_bounded_integer sz) h input pos in
    min <= U32.v len_payload /\ U32.v len_payload <= max /\
    sz + U32.v len_payload == content_length (parse_bounded_vldata_strong min max s) h input pos /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_pos (parse_bounded_vldata_strong min max s) h input pos (pos_payload `U32.add` len_payload) /\
    valid_exact p h input pos_payload (pos_payload `U32.add` len_payload) /\
    contents_exact p h input pos_payload (pos_payload `U32.add` len_payload) == contents (parse_bounded_vldata_strong min max s) h input pos
  ))))
= valid_facts (parse_bounded_vldata_strong min max s) h input pos;
  valid_facts (parse_bounded_vldata min max p) h input pos;
  valid_bounded_vldata_elim h min max p input pos
  
let valid_bounded_vldata_strong_intro
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (input: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    let sz = log256' max in
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_exact p h input pos_payload pos' /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    min <= U32.v len_payload /\ U32.v len_payload <= max /\
    valid (parse_bounded_integer sz) h input pos /\
    contents (parse_bounded_integer sz) h input pos == len_payload
  ))))
  (ensures (
    let sz = log256' max in
    let x = contents_exact p h input (pos `U32.add` U32.uint_to_t sz) pos' in
    parse_bounded_vldata_strong_pred min max s x /\
    valid_content_pos (parse_bounded_vldata_strong min max s) h input pos x pos'
  ))
= valid_facts (parse_bounded_vldata_strong min max s) h input pos;
  valid_facts (parse_bounded_vldata min max p) h input pos;
  valid_bounded_vldata_intro h min max p input pos pos'

let finalize_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (input: slice)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack unit
  (requires (fun h ->
    let sz = log256' max in
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_exact p h input pos_payload pos' /\ (
    let len_payload = pos' `U32.sub` pos_payload in
    min <= U32.v len_payload /\ U32.v len_payload <= max
  ))))
  (ensures (fun h _ h' ->
    let sz = log256' max in
    let x = contents_exact p h input (pos `U32.add` U32.uint_to_t sz) pos' in
    B.modifies (loc_slice_from_to input pos (pos `U32.add` U32.uint_to_t sz)) h h' /\
    parse_bounded_vldata_strong_pred min max s x /\
    valid_content_pos (parse_bounded_vldata_strong min max s) h' input pos x pos'
  ))
= [@inline_let]
  let sz = log256' max in
  [@inline_let]
  let len_payload = pos' `U32.sub` (pos `U32.add` U32.uint_to_t sz) in
  let _ = write_bounded_integer sz len_payload input pos in
  let h = HST.get () in
  valid_bounded_vldata_strong_intro h min max s input pos pos'

inline_for_extraction
let weak_finalize_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (input: slice)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack bool
  (requires (fun h ->
    let sz = log256' max in
    U32.v pos + sz <= U32.v input.len /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_exact p h input pos_payload pos'
  )))
  (ensures (fun h res h' ->
    let sz = log256' max in
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    let len_payload = pos' `U32.sub` pos_payload in
    B.modifies (loc_slice_from_to input pos (pos `U32.add` U32.uint_to_t sz)) h h' /\
    (res == true <==> (min <= U32.v len_payload /\ U32.v len_payload <= max)) /\
    (if res
    then
      let x = contents_exact p h input pos_payload pos' in
      parse_bounded_vldata_strong_pred min max s x /\
      valid_content_pos (parse_bounded_vldata_strong min max s) h' input pos x pos'
    else True
  )))
= let len_payload = pos' `U32.sub`  (pos `U32.add` U32.uint_to_t (log256' max)) in
  if U32.uint_to_t max `U32.lt` len_payload || len_payload `U32.lt` U32.uint_to_t min
  then false
  else begin
    finalize_bounded_vldata_strong min max s input pos pos';
    true
  end

(*
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
  let len = read_bounded_integer sz input in
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
