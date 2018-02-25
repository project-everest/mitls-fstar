module LowParse.SLow.VLData.Proof

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = LowParse.BigEndian
module Cast = FStar.Int.Cast
module B32 = FStar.Bytes

let serialize32_bounded_integer_1_correct = LowParse.SLow.VLData.Proof.Serialize.BoundedInteger1.serialize32_bounded_integer_1_correct

let serialize32_bounded_integer_2_correct = LowParse.SLow.VLData.Proof.Serialize.BoundedInteger2.serialize32_bounded_integer_2_correct

let serialize32_bounded_integer_3_correct = LowParse.SLow.VLData.Proof.Serialize.BoundedInteger3.serialize32_bounded_integer_3_correct

let decode32_bounded_integer_1_correct =
LowParse.SLow.VLData.Proof.Parse.BoundedInteger1.decode32_bounded_integer_1_correct

let parse_bounded_integer_2_spec () =
  LowParse.SLow.VLData.Proof.Parse.BoundedInteger2.parse_bounded_integer_2_spec synth_bounded_integer_2 ()

let decode32_bounded_integer_3_correct =
LowParse.SLow.VLData.Proof.Parse.BoundedInteger3.decode32_bounded_integer_3_correct

let parse_bounded_integer_4_spec () =
  LowParse.SLow.VLData.Proof.Parse.BoundedInteger4.parse_bounded_integer_4_spec synth_bounded_integer_4 ()

(*
inline_for_extraction
let decode32_bounded_integer_2
 (b: B32.lbytes 2)
: Tot (y: bounded_integer 2 { y == decode_bounded_integer 2 (B32.reveal b) } )
= let b0r = B32.get b 0ul in
  assert (b0r == B32.index b 0);
  B32.index_reveal b 0;
  let b0 = Cast.uint8_to_uint32 b0r in
  let b1r = B32.get b 1ul in
  assert (b1r == B32.index b 1);
  B32.index_reveal b 1;
  let b1 = Cast.uint8_to_uint32 b1r in
  let res = U32.add b1 (U32.mul 256ul b0) in
  E.be_to_n_2_spec (B32.reveal b);
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  assert (res == (decode_bounded_integer 2 (B32.reveal b) <: U32.t));
  assert (U32.v res < pow2 (FStar.Mul.op_Star 8 2));
  let (res: bounded_integer 2) = res in
  (res <: (y: bounded_integer 2 { y == decode_bounded_integer 2 (B32.reveal b) }))

inline_for_extraction
let parse32_bounded_integer_2 : parser32 (parse_bounded_integer 2) =
  decode_bounded_integer_injective 2;
  make_total_constant_size_parser32 2 2ul
    (decode_bounded_integer 2)
    ()
    (decode32_bounded_integer_2)
*)
