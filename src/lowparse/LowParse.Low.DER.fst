module LowParse.Low.DER
include LowParse.Spec.DER
include LowParse.Low.Int // for parse_u8
include LowParse.Low.BoundedInt // for bounded_integer
open FStar.Mul

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

#reset-options "--z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0"

#push-options "--z3rlimit 32"

let validate_bounded_der_length_payload32
  (x: U8.t { der_length_payload_size_of_tag x <= 4 } )
: Tot (validator (parse_der_length_payload32 x))
= fun input pos ->
    let h = HST.get () in
    [@inline_let] let _ =
      valid_facts (parse_der_length_payload32 x) h input pos;
      assert (U32.v pos <= U32.v input.len);
      parse_der_length_payload32_unfold x (bytes_of_slice_from h input pos);
      assert_norm (pow2 (8 * 1) == 256);
      assert_norm (pow2 (8 * 2) == 65536);
      assert_norm (pow2 (8 * 3) == 16777216);
      assert_norm (pow2 (8 * 4) == 4294967296)
    in
    if x `U8.lt` 128uy
    then pos
    else if x = 128uy || x = 255uy
    then validator_error_generic
    else if x = 129uy
    then
      [@inline_let] let _ = valid_facts parse_u8 h input pos in
      let v = validate_u8 () input pos in
      if validator_max_length `U32.lt` v
      then v
      else
        let z = read_u8 input pos in
        if z `U8.lt` 128uy
        then validator_error_generic
        else v
    else
      let len = x `U8.sub` 128uy in
      [@inline_let] let _ = valid_facts (parse_bounded_integer (U8.v len)) h input pos in
      if len = 2uy
      then
        let v = validate_bounded_integer 2 input pos in
        if validator_max_length `U32.lt` v
        then v
        else
          let y = read_bounded_integer_2 () input pos in
          if y `U32.lt `256ul
          then validator_error_generic
          else v
      else if len = 3uy
      then
        let v = validate_bounded_integer 3 input pos in
        if validator_max_length `U32.lt` v
        then v
        else
          let y = read_bounded_integer_3 () input pos in
          if y `U32.lt `65536ul
          then validator_error_generic
          else v
      else
        let v = validate_bounded_integer 4 input pos in
        if validator_max_length `U32.lt` v
        then v
        else
          let y = read_bounded_integer_4 () input pos in
          if y `U32.lt` 16777216ul
          then validator_error_generic
          else v

let jump_bounded_der_length_payload32
  (x: U8.t { der_length_payload_size_of_tag x <= 4 } )
: Tot (jumper (parse_der_length_payload32 x))
= fun input pos ->
    let h = HST.get () in
    [@inline_let] let _ =
      valid_facts (parse_der_length_payload32 x) h input pos;
      parse_der_length_payload32_unfold x (bytes_of_slice_from h input pos);
      assert_norm (pow2 (8 * 1) == 256);
      assert_norm (pow2 (8 * 2) == 65536);
      assert_norm (pow2 (8 * 3) == 16777216);
      assert_norm (pow2 (8 * 4) == 4294967296)
    in
    if x `U8.lt` 128uy
    then pos
    else
      [@inline_let]
      let len = x `U8.sub` 128uy in
      [@inline_let] let _ =
        valid_facts parse_u8 h input pos;
        parser_kind_prop_equiv parse_u8_kind parse_u8;
        valid_facts (parse_bounded_integer (U8.v len)) h input pos;
        parser_kind_prop_equiv (parse_bounded_integer_kind (U8.v len)) (parse_bounded_integer (U8.v len))
      in
      pos `U32.add` Cast.uint8_to_uint32 len

let read_bounded_der_length_payload32
  (x: U8.t { der_length_payload_size_of_tag x <= 4 } )
: Tot (leaf_reader (parse_der_length_payload32 x))
= fun input pos ->
    let h = HST.get () in
    [@inline_let] let _ =
      valid_facts (parse_der_length_payload32 x) h input pos;
      parse_der_length_payload32_unfold x (bytes_of_slice_from h input pos);
      assert_norm (pow2 (8 * 1) == 256);
      assert_norm (pow2 (8 * 2) == 65536);
      assert_norm (pow2 (8 * 3) == 16777216);
      assert_norm (pow2 (8 * 4) == 4294967296)
    in
    if x `U8.lt` 128uy
    then
      [@inline_let]
      let res = Cast.uint8_to_uint32 x in
      [@inline_let] let _ = assert (tag_of_der_length32 res == x) in
      (res <: refine_with_tag tag_of_der_length32 x)
    else if x = 129uy
    then
      [@inline_let] let _ = valid_facts parse_u8 h input pos in
      let z = read_u8 input pos in
      [@inline_let] let res = Cast.uint8_to_uint32 z in
      [@inline_let] let _ = assert (tag_of_der_length32 res == x) in
      (res <: refine_with_tag tag_of_der_length32 x)
    else
      let len = x `U8.sub` 128uy in
      [@inline_let] let _ = valid_facts (parse_bounded_integer (U8.v len)) h input pos in
      if len = 2uy
      then
        let res = read_bounded_integer_2 () input pos in
        [@inline_let] let _ = assert (tag_of_der_length32 res == x) in
        (res <: refine_with_tag tag_of_der_length32 x)
      else if len = 3uy
      then
        let res = read_bounded_integer_3 () input pos in
        [@inline_let] let _ = assert (tag_of_der_length32 res == x) in
        (res <: refine_with_tag tag_of_der_length32 x)
      else
        let res = read_bounded_integer_4 () input pos in
        [@inline_let] let _ = assert (tag_of_der_length32 res == x) in
        (res <: refine_with_tag tag_of_der_length32 x)

#pop-options
