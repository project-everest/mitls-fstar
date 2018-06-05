module LowParse.SLow.VLData
include LowParse.Spec.VLData
include LowParse.SLow.FLData

module Seq = FStar.Seq
module U32 = FStar.UInt32
module E = LowParse.BigEndianImpl.SLow
module B32 = LowParse.Bytes32

inline_for_extraction
let serialize32_bounded_integer_1
: (serializer32 (serialize_bounded_integer 1))
= (fun (input: bounded_integer 1) ->
    let b = E.n_to_be_1 _ _ (E.u32 ()) input in
    (b <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 1) input res } ))
  )

inline_for_extraction
let serialize32_bounded_integer_2
: (serializer32 (serialize_bounded_integer 2))
= (fun (input: bounded_integer 2) ->
    let b = E.n_to_be_2 _ _ (E.u32 ()) input in
    (b <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 2) input res } ))
  )

inline_for_extraction
let serialize32_bounded_integer_3
: (serializer32 (serialize_bounded_integer 3))
= (fun (input: bounded_integer 3) ->
    let b = E.n_to_be_3 _ _ (E.u32 ()) input in
    (b <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 3) input res } ))
  )

inline_for_extraction
let serialize32_bounded_integer_4
: (serializer32 (serialize_bounded_integer 4))
= (fun (input: bounded_integer 4) ->
    let b = E.n_to_be_4 _ _ (E.u32 ()) input in
    (b <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 4) input res } ))
  )

inline_for_extraction
let serialize32_bounded_integer
  (sz: integer_size)
: Tot (serializer32 (serialize_bounded_integer sz))
= match sz with
  | 1 -> serialize32_bounded_integer_1
  | 2 -> serialize32_bounded_integer_2
  | 3 -> serialize32_bounded_integer_3
  | 4 -> serialize32_bounded_integer_4

inline_for_extraction
let decode32_bounded_integer_1
  (b: B32.lbytes 1)
: Tot (y: bounded_integer 1 { y == decode_bounded_integer 1 (B32.reveal b) } )
= let r = E.be_to_n_1 _ _ (E.u32 ()) b in
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  (r <: (r: bounded_integer 1 { r == decode_bounded_integer 1 (B32.reveal b) } ))

inline_for_extraction
let decode32_bounded_integer_2
  (b: B32.lbytes 2)
: Tot (y: bounded_integer 2 { y == decode_bounded_integer 2 (B32.reveal b) } )
= let r = E.be_to_n_2 _ _ (E.u32 ()) b in
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  (r <: (r: bounded_integer 2 { r == decode_bounded_integer 2 (B32.reveal b) } ))

inline_for_extraction
let decode32_bounded_integer_3
  (b: B32.lbytes 3)
: Tot (y: bounded_integer 3 { y == decode_bounded_integer 3 (B32.reveal b) } )
= let r = E.be_to_n_3 _ _ (E.u32 ()) b in
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  (r <: (r: bounded_integer 3 { r == decode_bounded_integer 3 (B32.reveal b) } ))

inline_for_extraction
let decode32_bounded_integer_4
  (b: B32.lbytes 4)
: Tot (y: bounded_integer 4 { y == decode_bounded_integer 4 (B32.reveal b) } )
= let r = E.be_to_n_4 _ _ (E.u32 ()) b in
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  (r <: (r: bounded_integer 4 { r == decode_bounded_integer 4 (B32.reveal b) } ))

inline_for_extraction
let decode32_bounded_integer
  (sz: integer_size)
: Tot ((b: B32.lbytes sz) ->
    Tot (y: bounded_integer sz { y == decode_bounded_integer sz (B32.reveal b) } )
  )
= match sz with
  | 1 -> decode32_bounded_integer_1
  | 2 -> decode32_bounded_integer_2
  | 3 -> decode32_bounded_integer_3
  | 4 -> decode32_bounded_integer_4

inline_for_extraction
let parse32_bounded_integer (sz: integer_size) : Tot (parser32 (parse_bounded_integer sz)) =
  [@inline_let]
  let _ = decode_bounded_integer_injective sz in
  make_total_constant_size_parser32 sz (U32.uint_to_t sz)
    (decode_bounded_integer sz)
    ()
    (decode32_bounded_integer sz)

(* Parsers and serializers for the payload *)

inline_for_extraction
let parse32_vldata_payload
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (i: bounded_integer sz { f i == true } )
: Tot (parser32 (parse_vldata_payload sz f p i))
= fun (input: bytes32) -> parse32_fldata p32 (U32.v i) i input

inline_for_extraction
let parse32_vldata_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (f' : (x: bounded_integer sz) -> Tot (y: bool {y == f x}))
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
: Tot (parser32 (parse_vldata_gen sz f p))
= [@inline_let]
  let _ = parse_fldata_and_then_cases_injective sz f p in
  [@inline_let]
  let _ = parse_vldata_gen_kind_correct sz in
  parse32_and_then
    (parse32_filter (parse32_bounded_integer sz) f f')
    (parse_vldata_payload sz f p)
    ()
    (parse32_vldata_payload sz f p32)

inline_for_extraction
let parse32_vldata
  (sz: integer_size)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
: Tot (parser32 (parse_vldata sz p))
= parse32_vldata_gen sz (unconstrained_bounded_integer sz) (fun _ -> true) p32

#set-options "--z3rlimit 32"

inline_for_extraction
let parse32_bounded_vldata
  (min: nat)
  (min32: U32.t { U32.v min32 == min } )
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (max32: U32.t { U32.v max32 == max } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
: Tot (parser32 (parse_bounded_vldata min max p))
= [@inline_let]
  let _ = parse_bounded_vldata_correct min max p in
  [@inline_let]
  let sz : integer_size = (log256' max) in
  (fun input -> parse32_vldata_gen sz (in_bounds min max) (fun i -> not (U32.lt i min32 || U32.lt max32 i)) p32 input)

inline_for_extraction
let parse32_bounded_vldata_strong'
  (min: nat)
  (min32: U32.t { U32.v min32 == min } )
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (max32: U32.t { U32.v max32 == max } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
  (input: bytes32)
: Tot (option (parse_bounded_vldata_strong_t min max #k #t #p s * U32.t))
= let res =
    parse32_strengthen
      #(parse_bounded_vldata_kind min max)
      #t
      #(parse_bounded_vldata min max #k #t p)
      (parse32_bounded_vldata min min32 max max32 #k #t #p p32)
      (parse_bounded_vldata_strong_pred min max #k #t #p s)
      (parse_bounded_vldata_strong_correct min max #k #t #p s)
      input
  in
  match res with
  | None -> None
  | Some (x, consumed) ->
    let x1 : t = x in
    Some ((x1 <: parse_bounded_vldata_strong_t min max #k #t #p s), consumed)

let parse32_bounded_vldata_strong_correct
  (min: nat)
  (min32: U32.t { U32.v min32 == min } )
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (max32: U32.t { U32.v max32 == max } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
  (input: bytes32)
: Lemma
  ( let res : option (parse_bounded_vldata_strong_t min max s * U32.t) = 
      parse32_bounded_vldata_strong' min min32 max max32 s p32 input
    in
    parser32_correct (parse_bounded_vldata_strong min max s) input res)
= let res =
    parse32_strengthen
      #(parse_bounded_vldata_kind min max)
      #t
      #(parse_bounded_vldata min max #k #t p)
      (parse32_bounded_vldata min min32 max max32 #k #t #p p32)
      (parse_bounded_vldata_strong_pred min max #k #t #p s)
      (parse_bounded_vldata_strong_correct min max #k #t #p s)
      input
  in
  match res with
  | None -> ()
  | Some (x, consumed) ->
    let x1 : t = x in
    let res = Some ((x1 <: parse_bounded_vldata_strong_t min max #k #t #p s), consumed) in
    assert (parser32_correct (parse_bounded_vldata_strong min max s) input res)

inline_for_extraction
let parse32_bounded_vldata_strong
  (min: nat)
  (min32: U32.t { U32.v min32 == min } )
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (max32: U32.t { U32.v max32 == max } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
: Tot (parser32 #(parse_bounded_vldata_kind min max) #(parse_bounded_vldata_strong_t min max s) (parse_bounded_vldata_strong min max s))
= make_parser32
    (parse_bounded_vldata_strong min max s)
    (fun input ->
       parse32_bounded_vldata_strong_correct min min32 max max32 s p32 input;
       parse32_bounded_vldata_strong' min min32 max max32 s p32 input
    )

inline_for_extraction
let serialize32_bounded_vldata_strong'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967292 } ) // NOTE here: max must be less than 2^32 - 4
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: partial_serializer32 s)
: Tot (parse_bounded_vldata_strong_t min max s -> Tot bytes32)
= [@inline_let]
  let sz : integer_size = log256' max in
  [@inline_let]
  let ser : serializer32 (serialize_bounded_integer sz) = serialize32_bounded_integer sz in
  (fun (input: parse_bounded_vldata_strong_t min max s) ->
    let pl = s32 input in
    let len = B32.len pl in
    assert (min <= U32.v len /\ U32.v len <= max);
    let slen = ser (len <: bounded_integer sz) in
    seq_slice_append_l (B32.reveal slen) (B32.reveal pl);
    seq_slice_append_r (B32.reveal slen) (B32.reveal pl);
    let res : bytes32 = B32.b32append slen pl in
    res)

let serialize32_bounded_vldata_strong_correct
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967292 } ) // NOTE here: max must be less than 2^32 - 4
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (input: parse_bounded_vldata_strong_t min max s)
: Lemma
  (serializer32_correct (serialize_bounded_vldata_strong min max s) input (serialize32_bounded_vldata_strong' min max s32 input))
= let sz : integer_size = log256' max in
  let ser : serializer32 (serialize_bounded_integer sz) = serialize32_bounded_integer sz in
  let pl = s32 input in
  assert (B32.reveal pl == s input);
  let len = B32.len pl in
  let nlen = U32.v len in
  assert (min <= nlen /\ nlen <= max);
  let slen = ser (len <: bounded_integer sz) in
  assert (B32.reveal slen == serialize (serialize_bounded_integer sz) len);
  seq_slice_append_l (B32.reveal slen) (B32.reveal pl);
  seq_slice_append_r (B32.reveal slen) (B32.reveal pl);
  let res : bytes32 = B32.b32append slen pl in
  assert (B32.reveal res == Seq.append (B32.reveal slen) (B32.reveal pl));
  assert (B32.reveal res == serialize_bounded_vldata_strong' min max s input);
  assert (serializer32_correct (serialize_bounded_vldata_strong min max s) input res)

inline_for_extraction
let serialize32_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967292 } ) // NOTE here: max must be less than 2^32 - 4
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: partial_serializer32 s)
: Tot (serializer32 (serialize_bounded_vldata_strong min max s))
= fun (input: parse_bounded_vldata_strong_t min max s) ->
  serialize32_bounded_vldata_strong_correct min max s32 input;
  (serialize32_bounded_vldata_strong' min max s32 input <: (res: bytes32 { serializer32_correct (serialize_bounded_vldata_strong min max s) input res } ))

#reset-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false"

inline_for_extraction
let check_vldata_payload_size32
  (min: nat)
  (min32: U32.t { U32.v min32 == min } )
  (max: nat { min <= max /\ max > 0 /\ max < 4294967295 } ) // necessary to exclude the overflow case; enough to be compatible with serialize32
  (max32: U32.t { U32.v max32 == max } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: size32 s)
  (input: t)
: Tot (y: bool { y == true <==> parse_bounded_vldata_strong_pred min max s input } )
= let sz : U32.t = s32 input in
  [@inline_let]
  let y : bool =
    not (sz = u32_max || U32.lt sz min32 || U32.lt max32 sz)
  in
  [@inline_let]
  let _ : squash (y == true <==> parse_bounded_vldata_strong_pred min max s input) =
    if sz = u32_max
    then
      if Seq.length (serialize s input) > U32.v u32_max
      then ()
      else begin
        assert (U32.v u32_max == Seq.length (serialize s input));
        assert_norm (U32.v u32_max == 4294967295);
        assert (Seq.length (serialize s input) > max);
        assert (~ (parse_bounded_vldata_strong_pred min max s input))
      end
    else
      if Seq.length (serialize s input) > U32.v u32_max
      then ()
      else ()
  in
  y

inline_for_extraction
let size32_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967292 } ) // NOTE here: max must be less than 2^32 - 4, otherwise add overflows
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: size32 s)
  (sz32: U32.t { U32.v sz32 == log256' max } )
: Tot (size32 (serialize_bounded_vldata_strong min max s))
= (fun (input: parse_bounded_vldata_strong_t min max s) ->
    let len = s32 input in
    [@inline_let]
    let _ = assert_norm (U32.v u32_max == 4294967295) in
    [@inline_let]
    let _ = assert (min <= U32.v len /\ U32.v len <= max) in
    [@inline_let]
    let res : U32.t = U32.add sz32 len in
    (res <: (res: U32.t { size32_postcond (serialize_bounded_vldata_strong min max s) input res  } )))
