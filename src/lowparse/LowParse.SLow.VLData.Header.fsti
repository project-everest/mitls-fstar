module LowParse.SLow.VLData.Header
include LowParse.Spec.VLData.Header
include LowParse.SLow.Combinators

module Seq = FStar.Seq
module U32 = FStar.UInt32
module B32 = LowParse.Bytes32

inline_for_extraction
val serialize32_bounded_integer_1
: (serializer32 (serialize_bounded_integer 1))

inline_for_extraction
val serialize32_bounded_integer_2
: (serializer32 (serialize_bounded_integer 2))

inline_for_extraction
val serialize32_bounded_integer_3
: (serializer32 (serialize_bounded_integer 3))

inline_for_extraction
val serialize32_bounded_integer_4
: (serializer32 (serialize_bounded_integer 4))

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
val decode32_bounded_integer_1
  (b: B32.lbytes 1)
: Tot (y: bounded_integer 1 { y == decode_bounded_integer 1 (B32.reveal b) } )

inline_for_extraction
val decode32_bounded_integer_2
  (b: B32.lbytes 2)
: Tot (y: bounded_integer 2 { y == decode_bounded_integer 2 (B32.reveal b) } )

inline_for_extraction
val decode32_bounded_integer_3
  (b: B32.lbytes 3)
: Tot (y: bounded_integer 3 { y == decode_bounded_integer 3 (B32.reveal b) } )

inline_for_extraction
val decode32_bounded_integer_4
  (b: B32.lbytes 4)
: Tot (y: bounded_integer 4 { y == decode_bounded_integer 4 (B32.reveal b) } )

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
