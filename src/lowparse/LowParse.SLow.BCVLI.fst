module LowParse.SLow.BCVLI
include LowParse.Spec.BCVLI
include LowParse.SLow.Combinators // for make_total_constant_size_parser32

module B32 = LowParse.Bytes32
module Seq = FStar.Seq
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

#push-options "--max_fuel 0"

inline_for_extraction
let bounded_integer_of_le_32_1
  (b: B32.lbytes 1)
: Tot (y: bounded_integer 1 { y == bounded_integer_of_le 1 (B32.reveal b) } )
= [@inline_let] let _ =
    bounded_integer_of_le_1_eq (B32.reveal b)
  in
  Cast.uint8_to_uint32 (B32.get b 0ul)

let parse32_bounded_integer_le_1
: parser32 (parse_bounded_integer_le 1)
= [@inline_let] let _ =
    bounded_integer_of_le_injective 1
  in
  make_total_constant_size_parser32
    1
    1ul
    (bounded_integer_of_le 1)
    ()
    bounded_integer_of_le_32_1

inline_for_extraction
let bounded_integer_of_le_32_2
  (b: B32.lbytes 2)
: Tot (y: bounded_integer 2 { y == bounded_integer_of_le 2 (B32.reveal b) } )
= [@inline_let] let _ =
    bounded_integer_of_le_2_eq (B32.reveal b)
  in
  Cast.uint8_to_uint32 (B32.get b 0ul) `U32.add` (256ul `U32.mul` Cast.uint8_to_uint32 (B32.get b 1ul))

let parse32_bounded_integer_le_2
: parser32 (parse_bounded_integer_le 2)
= [@inline_let] let _ =
    bounded_integer_of_le_injective 2
  in
  make_total_constant_size_parser32
    2
    2ul
    (bounded_integer_of_le 2)
    ()
    bounded_integer_of_le_32_2

inline_for_extraction
let bounded_integer_of_le_32_4
  (b: B32.lbytes 4)
: Tot (y: bounded_integer 4 { y == bounded_integer_of_le 4 (B32.reveal b) } )
= [@inline_let] let _ =
    bounded_integer_of_le_4_eq (B32.reveal b)
  in
  Cast.uint8_to_uint32 (B32.get b 0ul) `U32.add` (256ul `U32.mul` ( Cast.uint8_to_uint32 (B32.get b 1ul) `U32.add` (256ul `U32.mul` (Cast.uint8_to_uint32 (B32.get b 2ul) `U32.add` (256ul `U32.mul` Cast.uint8_to_uint32 (B32.get b 3ul))))))

let parse32_bounded_integer_le_4
: parser32 (parse_bounded_integer_le 4)
= [@inline_let] let _ =
    bounded_integer_of_le_injective 4
  in
  make_total_constant_size_parser32
    4
    4ul
    (bounded_integer_of_le 4)
    ()
    bounded_integer_of_le_32_4

inline_for_extraction
let parse32_u16_le : parser32 parse_u16_le =
  parse32_synth'
    _
    synth_u16_le
    parse32_bounded_integer_le_2
    ()

inline_for_extraction
let parse32_u32_le : parser32 parse_u32_le =
  parse32_synth'
    _
    synth_u32_le
    parse32_bounded_integer_le_4
    ()

let parse32_bcvli
: parser32 parse_bcvli
= fun input -> ((
    [@inline_let] let _ =
      parse_bcvli_eq (B32.reveal input)
    in
    match parse32_bounded_integer_le_1 input with
    | None -> None
    | Some (x32, consumed_x) ->
      if x32 `U32.lt` 253ul
      then Some (x32, consumed_x)
      else
        let input' = B32.slice input consumed_x (B32.len input) in
        if x32 = 253ul
        then
          match parse32_bounded_integer_le_2 input' with
          | None -> None
          | Some (y, consumed_y) ->
            if y `U32.lt` 253ul then None else Some (y, consumed_x `U32.add` consumed_y)
        else if x32 = 254ul
        then
          match parse32_bounded_integer_le_4 input' with
          | None -> None
          | Some (y, consumed_y) ->
            if y `U32.lt` 65536ul then None else Some (y, consumed_x `U32.add` consumed_y)
        else
          None
  ) <: (res: _ { parser32_correct parse_bcvli input res } ))

module U8 = FStar.UInt8

let serialize32_bounded_integer_le_1  : serializer32 (serialize_bounded_integer_le 1)
= fun (x: bounded_integer 1) -> ((
    [@inline_let] let _ =
      serialize_bounded_integer_le_1_eq x 0
    in
    B32.create 1ul (Cast.uint32_to_uint8 x)
  ) <: (res: bytes32 { serializer32_correct' (serialize_bounded_integer_le 1) x res } ))

let serialize32_bounded_integer_le_2  : serializer32 (serialize_bounded_integer_le 2)
= fun (x: bounded_integer 2) -> ((
    [@inline_let] let _ =
      serialize_bounded_integer_le_2_eq x 0;
      serialize_bounded_integer_le_2_eq x 1
    in
    B32.create 1ul (Cast.uint32_to_uint8 x) `B32.append` B32.create 1ul (Cast.uint32_to_uint8 (x `U32.div` 256ul))
  ) <: (res: bytes32 { serializer32_correct' (serialize_bounded_integer_le 2) x res } ))

let serialize32_bounded_integer_le_4  : serializer32 (serialize_bounded_integer_le 4)
= fun (x: bounded_integer 4) -> ((
    [@inline_let] let _ =
      serialize_bounded_integer_le_4_eq x 0;
      serialize_bounded_integer_le_4_eq x 1;
      serialize_bounded_integer_le_4_eq x 2;
      serialize_bounded_integer_le_4_eq x 3
    in
    let rem0 = Cast.uint32_to_uint8 x in
    let div0 = x `U32.div` 256ul in
    let rem1 = Cast.uint32_to_uint8 div0 in
    let div1 = div0 `U32.div` 256ul in
    let rem2 = Cast.uint32_to_uint8 div1 in
    let div2 = div1 `U32.div` 256ul in
    let rem3 = Cast.uint32_to_uint8 div2 in
    (B32.create 1ul rem0 `B32.append` B32.create 1ul rem1) `B32.append`
    (B32.create 1ul rem2 `B32.append` B32.create 1ul rem3)
  ) <: (res: bytes32 { serializer32_correct' (serialize_bounded_integer_le 4) x res } ))

inline_for_extraction
let serialize32_u16_le : serializer32 serialize_u16_le =
  serialize32_synth' 
    _
    synth_u16_le
    _
    serialize32_bounded_integer_le_2
    synth_u16_le_recip
    ()

inline_for_extraction
let serialize32_u32_le : serializer32 serialize_u32_le =
  serialize32_synth' 
    _
    synth_u32_le
    _
    serialize32_bounded_integer_le_4
    synth_u32_le_recip
    ()

let serialize32_bcvli
: serializer32 serialize_bcvli
= fun x -> ((
    let c1 : bounded_integer 1 =
      if x `U32.lt` 253ul
      then x
      else if x `U32.lt` 65536ul
      then 253ul
      else 254ul
    in
    let s1 = serialize32_bounded_integer_le_1 c1 in
    if c1 `U32.lt` 253ul
    then s1
    else if c1 = 253ul
    then s1 `B32.append` serialize32_bounded_integer_le_2 x
    else s1 `B32.append` serialize32_bounded_integer_le_4 x
  ) <: (res: bytes32 { serializer32_correct' serialize_bcvli x res } ))

let size32_bcvli
: size32 serialize_bcvli
= fun x -> ((
    if x `U32.lt` 253ul
    then 1ul
    else if x `U32.lt` 65536ul
    then 3ul
    else 5ul
  ) <: (res: _ { size32_postcond serialize_bcvli x res } ))

#pop-options
