module LowParse.SLow.VLData.Proof.Parse.BoundedInteger2
open LowParse.SLow.VLData.Code

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = LowParse.BigEndian
module Cast = FStar.Int.Cast
module B32 = FStar.Bytes

#reset-options "--z3rlimit 256 --max_fuel 64 --max_ifuel 64"

let synth_bounded_integer_2
  (x: U16.t)
: GTot (bounded_integer 2)
= Cast.uint16_to_uint32 x

let parse_bounded_integer_2_spec
  (synth_bounded_integer_2' : (U16.t -> GTot (bounded_integer 2)))
  (synth_bounded_integer_2'_prf : unit { forall (x: U16.t) . synth_bounded_integer_2' x == synth_bounded_integer_2 x } )
: Lemma
  (forall (input: bytes) . parse (parse_bounded_integer 2) input == parse (parse_u16 `parse_synth` synth_bounded_integer_2') input)
= let f
    (input: bytes { Seq.length input == 2 })
  : Lemma
    ((decode_u16 `compose` synth_bounded_integer_2') input == decode_bounded_integer 2 input)
  = E.be_to_n_2_spec input;
    E.lemma_be_to_n_is_bounded input;
    assert (U16.v (decode_u16 input) == U32.v (decode_bounded_integer 2 input));
    assert (U32.v ((decode_u16 `compose` synth_bounded_integer_2') input) == U32.v (decode_bounded_integer 2 input));
    U32.v_inj ((decode_u16 `compose` synth_bounded_integer_2') input) (decode_bounded_integer 2 input)
  in
  Classical.forall_intro f;
  decode_u16_injective ();
  make_total_constant_size_parser_compose 2 U16.t (bounded_integer 2) (decode_u16) (synth_bounded_integer_2');
  assert_norm (forall (input: bytes) . parse (parse_bounded_integer 2) input == parse (make_total_constant_size_parser 2 (bounded_integer 2) (decode_u16 `compose` synth_bounded_integer_2')) input)
