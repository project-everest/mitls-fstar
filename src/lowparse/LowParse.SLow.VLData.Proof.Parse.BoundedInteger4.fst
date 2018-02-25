module LowParse.SLow.VLData.Proof.Parse.BoundedInteger4
open LowParse.SLow.VLData.Code

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = LowParse.BigEndian
module Cast = FStar.Int.Cast
module B32 = FStar.Bytes

let synth_bounded_integer_4
  (x: U32.t)
: GTot (bounded_integer 4)
= x

let parse_bounded_integer_4_spec
  (synth_bounded_integer_4' : (U32.t -> GTot (bounded_integer 4)))
  (synth_bounded_integer_4'_prf : unit { forall (x: U32.t) . synth_bounded_integer_4' x == synth_bounded_integer_4 x } )
: Lemma
  (forall (input: bytes) . parse (parse_bounded_integer 4) input == parse (parse_u32 `parse_synth` synth_bounded_integer_4') input)
= assert (forall (input: bytes { Seq.length input == 4 }) . (decode_u32 `compose` synth_bounded_integer_4') input == decode_bounded_integer 4 input);
  decode_u32_injective ();
  make_total_constant_size_parser_compose 4 U32.t (bounded_integer 4) (decode_u32) (synth_bounded_integer_4');
  assert_norm (forall (input: bytes) . parse (parse_bounded_integer 4) input == parse (make_total_constant_size_parser 4 (bounded_integer 4) (decode_u32 `compose` synth_bounded_integer_4')) input)
