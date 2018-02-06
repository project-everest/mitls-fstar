module LowParse.SLow.VLData.Proof.Serialize.BoundedInteger2
open LowParse.SLow.VLData.Code

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = LowParse.BigEndian
module Cast = FStar.Int.Cast
module B32 = FStar.Bytes

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 256 --max_ifuel 64 --max_fuel 64"

let serialize_bounded_integer_2_spec
  (input: bounded_integer 2)
: Lemma
  (let ser = serialize (serialize_bounded_integer 2) input in
   Seq.length ser == 2 /\
   U8.v (Seq.index ser 1) == U32.v input % 256 /\
   U8.v (Seq.index ser 0) == (U32.v input / 256) % 256
  )
= E.index_n_to_be 2ul (U32.v input) 1;
  E.index_n_to_be 2ul (U32.v input) 0

let serialize32_bounded_integer_2_correct
  (buf: B32.lbytes 2)
  (input: bounded_integer 2)
: Lemma
  (serializer32_correct (serialize_bounded_integer 2) input (serialize32_bounded_integer_2' buf input))
= let ser32 = serialize32_bounded_integer_2' buf input in
  let rser32 = B32.reveal ser32 in
  let byte1 = Cast.uint32_to_uint8 input in
  assert (U8.v byte1 == U32.v input % 256);
  assert (Seq.index rser32 1 == byte1);
  let byte0v = U32.div input 256ul in
  let byte0 = Cast.uint32_to_uint8 byte0v in
  assert (U8.v byte0 == (U32.v input / 256) % 256);
  assert (Seq.index rser32 0 == byte0);
  serialize_bounded_integer_2_spec input;
  let ser = serialize (serialize_bounded_integer 2) input in
  assert (Seq.length ser == 2);
  E.lemma_u8_eq_intro rser32 ser ()
    (fun (i: nat) -> if i = 0 then () else if i = 1 then () else ());
  assert (serializer32_correct (serialize_bounded_integer 2) input ser32)
