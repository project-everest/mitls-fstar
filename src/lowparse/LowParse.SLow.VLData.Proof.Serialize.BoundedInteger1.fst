module LowParse.SLow.VLData.Proof.Serialize.BoundedInteger1
open LowParse.SLow.VLData.Code

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = LowParse.BigEndian
module Cast = FStar.Int.Cast
module B32 = FStar.Bytes

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 128 --max_ifuel 64 --max_fuel 64"

let serialize_bounded_integer_1_spec
  (input: bounded_integer 1)
: Lemma
  (let ser = serialize (serialize_bounded_integer 1) input in
   Seq.length ser == 1 /\
   U8.v (Seq.index ser 0) == U32.v input % 256
  )
= E.index_n_to_be 1ul (U32.v input) 0

let serialize32_bounded_integer_1_correct
  (buf: B32.lbytes 1)
  (input: bounded_integer 1)
: Lemma
  (serializer32_correct (serialize_bounded_integer 1) input (serialize32_bounded_integer_1' buf input))
= let ser32 = serialize32_bounded_integer_1' buf input in
  let rser32 = B32.reveal ser32 in
  let byte0 = Cast.uint32_to_uint8 input in
  assert (U8.v byte0 == U32.v input % 256);
  assert (Seq.index rser32 0 == byte0);
  serialize_bounded_integer_1_spec input;
  let ser = serialize (serialize_bounded_integer 1) input in
  assert (Seq.length ser == 1);
  E.lemma_u8_eq_intro rser32 ser ()
    (fun (i: nat) -> if i = 0 then () else ());
  assert (serializer32_correct (serialize_bounded_integer 1) input ser32)
