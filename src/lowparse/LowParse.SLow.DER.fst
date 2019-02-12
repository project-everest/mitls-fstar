module LowParse.SLow.DER
include LowParse.Spec.DER
include LowParse.SLow.Combinators
include LowParse.SLow.VLData // for bounded_integer
open FStar.Mul

module Seq = FStar.Seq
module U8 = FStar.UInt8
module E = LowParse.BigEndian
module U32 = FStar.UInt32
module Math = LowParse.Math

#reset-options "--z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0"

let be_int_of_bounded_integer
  (len: integer_size)
  (x: nat { x < pow2 (8 * len) } )
: GTot (bounded_integer len)
= integer_size_values len;
  assert_norm (pow2 (8 * 1) == 256);
  assert_norm (pow2 (8 * 2) == 65536);
  assert_norm (pow2 (8 * 3) == 16777216);
  assert_norm (pow2 (8 * 4) == 4294967296);
  U32.uint_to_t x

let be_int_of_bounded_integer_injective
  (len: integer_size)
: Lemma
  (synth_injective (be_int_of_bounded_integer len))
  [SMTPat (synth_injective (be_int_of_bounded_integer len))] // FIXME: WHY WHY WHY does this pattern NEVER trigger?
= integer_size_values len;
  assert_norm (pow2 (8 * 1) == 256);
  assert_norm (pow2 (8 * 2) == 65536);
  assert_norm (pow2 (8 * 3) == 16777216);
  assert_norm (pow2 (8 * 4) == 4294967296)

let parse_seq_flbytes_synth_be_int_eq
  (len: integer_size)
  (input: bytes)
: Lemma
  (
    let _ = synth_be_int_injective len in
    let _ = be_int_of_bounded_integer_injective len in
    parse ((parse_seq_flbytes len `parse_synth` synth_be_int len) `parse_synth` be_int_of_bounded_integer len) input == parse (parse_bounded_integer len) input)
=
    let _ = synth_be_int_injective len in
    let _ = be_int_of_bounded_integer_injective len in
    parse_synth_eq (parse_seq_flbytes len `parse_synth` synth_be_int len) (be_int_of_bounded_integer len) input;
    parse_synth_eq (parse_seq_flbytes len) (synth_be_int len) input


(*
inline_for_extraction
let parse32_be_int_2
: Tot (parser32 (parse_seq_flbytes 2 `parse_synth` synth_be_int len))
= fun (input: B32.bytes) ->
  
