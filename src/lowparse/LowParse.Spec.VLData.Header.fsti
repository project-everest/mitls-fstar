module LowParse.Spec.VLData.Header
include LowParse.Spec.Combinators

module U32 = FStar.UInt32

let integer_size : Type0 = (sz: nat { 1 <= sz /\ sz <= 4 } )

val integer_size_values (i: integer_size) : Lemma
  (i == 1 \/ i == 2 \/ i == 3 \/ i == 4)

inline_for_extraction
let bounded_integer
  (i: integer_size)
: Tot Type0
= (u: U32.t { U32.v u < pow2 (FStar.Mul.op_Star 8 i) } )

val decode_bounded_integer
  (i: integer_size)
  (b: bytes { Seq.length b == i } )
: GTot (bounded_integer i)

val decode_bounded_integer_injective
  (i: integer_size)
: Lemma
  (make_total_constant_size_parser_precond i (bounded_integer i) (decode_bounded_integer i))

// unfold
let parse_bounded_integer_kind
  (i: integer_size)
: Tot parser_kind
= total_constant_size_parser_kind i

let parse_bounded_integer
  (i: integer_size)
: Tot (parser (parse_bounded_integer_kind i) (bounded_integer i))
= decode_bounded_integer_injective i;
  make_total_constant_size_parser i (bounded_integer i) (decode_bounded_integer i)

val serialize_bounded_integer
  (sz: integer_size)
: Tot (serializer (parse_bounded_integer sz))
