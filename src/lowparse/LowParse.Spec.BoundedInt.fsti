module LowParse.Spec.BoundedInt
include LowParse.Spec.Base
include LowParse.Spec.Int // for parse_u16_kind

module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = FStar.Kremlin.Endianness

(* bounded integers *)

let integer_size : Type0 = (sz: nat { 1 <= sz /\ sz <= 4 } )

val integer_size_values (i: integer_size) : Lemma
  (i == 1 \/ i == 2 \/ i == 3 \/ i == 4)

let bounded_integer_prop
  (i: integer_size)
  (u: U32.t)
: GTot Type0
= U32.v u < (match i with 1 -> 256 | 2 -> 65536 | 3 -> 16777216 | 4 -> 4294967296)

inline_for_extraction
let bounded_integer
  (i: integer_size)
: Tot Type0
= (u: U32.t { bounded_integer_prop i u } )

inline_for_extraction
let parse_bounded_integer_kind
  (i: integer_size)
: Tot parser_kind
= total_constant_size_parser_kind i

val parse_bounded_integer
  (i: integer_size)
: Tot (parser (parse_bounded_integer_kind i) (bounded_integer i))

val parse_bounded_integer_spec
  (i: integer_size)
  (input: bytes)
: Lemma
  (let res = parse (parse_bounded_integer i) input in
   if Seq.length input < i
   then res == None
   else
     match res with
     | None -> False
     | Some (y, consumed) ->
       U32.v y == E.be_to_n (Seq.slice input 0 i) /\ consumed == i
  )

val serialize_bounded_integer
  (sz: integer_size)
: Tot (serializer (parse_bounded_integer sz))

val parse_bounded_integer_le
  (i: integer_size)
: Tot (parser (parse_bounded_integer_kind i) (bounded_integer i))

val parse_u16_le : parser parse_u16_kind U16.t

val parse_u32_le : parser parse_u32_kind U32.t

val serialize_bounded_integer_le
  (sz: integer_size)
: Tot (serializer (parse_bounded_integer_le sz))

val serialize_u16_le : serializer parse_u16_le

val serialize_u32_le : serializer parse_u32_le
