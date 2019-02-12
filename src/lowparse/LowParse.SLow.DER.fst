module LowParse.SLow.DER
include LowParse.Spec.DER
include LowParse.SLow.Combinators
include LowParse.SLow.Int // for parse32_u8
include LowParse.SLow.BoundedInt // for bounded_integer
open FStar.Mul

module Seq = FStar.Seq
module U8 = FStar.UInt8
module E = LowParse.BigEndian
module U32 = FStar.UInt32
module Math = LowParse.Math
module B32 = LowParse.Bytes32
module Cast = FStar.Int.Cast

#reset-options "--z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0"

#push-options "--z3rlimit 16"

let parse32_der_length_payload32
  (x: U8.t { der_length_payload_size_of_tag x <= 4 } )
: Tot (parser32 (parse_der_length_payload32 x))
= fun (input: bytes32) -> ((
    [@inline_let] let _ =
      parse_der_length_payload32_unfold x (B32.reveal input);
      assert_norm (pow2 (8 * 1) == 256);
      assert_norm (pow2 (8 * 2) == 65536);
      assert_norm (pow2 (8 * 3) == 16777216);
      assert_norm (pow2 (8 * 4) == 4294967296)
    in
    if x `U8.lt` 128uy
    then Some (Cast.uint8_to_uint32 x, 0ul)
    else if x = 128uy || x = 255uy
    then None
    else if x = 129uy
    then
      match parse32_u8 input with
      | None -> None
      | Some (z, consumed) ->
        if z `U8.lt` 128uy
        then None
        else Some ((Cast.uint8_to_uint32 z <: refine_with_tag tag_of_der_length32 x), consumed)
    else
      let len = x `U8.sub` 128uy in
      if len = 2uy
      then
        match parse32_bounded_integer 2 input with
        | None -> None
        | Some (y, consumed) ->
          if y `U32.lt `256ul
          then None
          else Some ((y <: refine_with_tag tag_of_der_length32 x), consumed)
      else if len = 3uy
      then
        match parse32_bounded_integer 3 input with
        | None -> None
        | Some (y, consumed) ->
          if y `U32.lt `65536ul
          then None
          else Some ((y <: refine_with_tag tag_of_der_length32 x), consumed)
      else
        match parse32_bounded_integer 4 input with
        | None -> None
        | Some (y, consumed) ->
          if y `U32.lt` 16777216ul
          then None
          else Some ((y <: refine_with_tag tag_of_der_length32 x), consumed)
  ) <: (res: _ { parser32_correct (parse_der_length_payload32 x) input res } ))

inline_for_extraction
let der_length_payload_size_of_tag8
  (x: U8.t)
: Tot (y: U8.t { U8.v y == der_length_payload_size_of_tag x } )
= [@inline_let]
  let _ =
    assert_norm (der_length_max == pow2 (8 * 126) - 1);
    assert_norm (pow2 7 == 128);
    assert_norm (pow2 8 == 256);
    assert_norm (256 < der_length_max);
    assert (U8.v x <= der_length_max)
  in
  if x `U8.lt` 129uy || x = 255uy
  then
    0uy
  else
    x `U8.sub` 128uy

inline_for_extraction
let log256_32
  (n: U32.t { U32.v n > 0 } )
: Tot (y: U8.t { U8.v y == log256' (U32.v n) } )
= if n `U32.lt` 256ul
  then 1uy
  else if n `U32.lt` 65536ul
  then 2uy
  else if n `U32.lt` 16777216ul
  then 3uy
  else 4uy

inline_for_extraction
let tag_of_der_length32_impl
  (x: U32.t)
: Tot (y: U8.t { U32.v x < der_length_max /\ y == tag_of_der_length (U32.v x) } )
= [@inline_let]
  let _ = assert_norm (4294967296 <= der_length_max) in
  if x `U32.lt` 128ul
  then begin
    [@inline_let] let _ = FStar.Math.Lemmas.small_modulo_lemma_1 (U32.v x) 256 in
    Cast.uint32_to_uint8 x <: U8.t
  end else
    let len_len = log256_32 x in
    [@inline_let] let _ =
      log256_eq (U32.v x);
      assert_norm (der_length_max == pow2 (8 * 126) - 1);
      Math.pow2_lt_recip (8 * (U8.v len_len - 1)) (8 * 126)
    in
    128uy `U8.add` len_len

#push-options "--max_ifuel 2"

let parse32_bounded_der_length32
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max } )
: Tot (
      [@inline_let] let _ = assert_norm (4294967296 <= der_length_max) in
      parser32 (parse_bounded_der_length32 (U32.v min) (U32.v max)))
= [@inline_let] let _ = assert_norm (4294967296 <= der_length_max) in
  fun (input: bytes32) -> ((
    [@inline_let]
    let _ =
      parse_bounded_der_length32_unfold (U32.v min) (U32.v max) (B32.reveal input)
    in
    match parse32_u8 input with
    | None -> None
    | Some (x, consumed_x) ->
      let len = der_length_payload_size_of_tag8 x in
      if len `U8.lt` der_length_payload_size_of_tag8 (tag_of_der_length32_impl min) || der_length_payload_size_of_tag8 (tag_of_der_length32_impl max) `U8.lt` len
      then None
      else begin
        let input' = B32.slice input consumed_x (B32.len input) in
        match parse32_der_length_payload32 x input' with
        | Some (y, consumed_y) ->
          if y `U32.lt` min || max `U32.lt` y
          then None
          else Some (y, consumed_x `U32.add` consumed_y)
        | None -> None
      end
  ) <: (res : _ { parser32_correct (parse_bounded_der_length32 (U32.v min) (U32.v max)) input res } ))

#pop-options

#pop-options
  
