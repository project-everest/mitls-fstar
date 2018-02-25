module LowParse.SLow.Int.Proof.SerializeU16
open LowParse.Spec.Int
open LowParse.SLow.Int.Code

module Seq = FStar.Seq
module E = LowParse.BigEndian
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B32 = FStar.Bytes
module Cast = FStar.Int.Cast

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 256 --max_ifuel 32 --max_fuel 32"

let serialize_u16_spec
  (input: U16.t)
: Lemma
  (let ser = serialize_u16 input in
   Seq.length ser == 2 /\
   U8.v (Seq.index ser 1) == U16.v input % 256 /\
   U8.v (Seq.index ser 0) == (U16.v input / 256) % 256
  )
= E.index_n_to_be 2ul (U16.v input) 1;
  E.index_n_to_be 2ul (U16.v input) 0

let serialize32_u16_correct
  (buf: B32.lbytes 2)
  (input: U16.t)
: Lemma
  (serializer32_correct #_ #_ #parse_u16 serialize_u16 input (serialize32_u16' buf input))
= let ser32 = serialize32_u16' buf input in
  let rser32 = B32.reveal ser32 in
  assert (pow2 8 == 256);
  assert (pow2 16 == 65536);
  let byte1 = Cast.uint16_to_uint8 input in
  assert (U8.v byte1 == U16.v input % 256);
  assert (Seq.index rser32 1 == byte1);
  let byte0v = U16.div input 256us in
  let byte0 = Cast.uint16_to_uint8 byte0v in
  assert (U8.v byte0 == (U16.v input / 256) % 256);
  assert (Seq.index rser32 0 == byte0);
  serialize_u16_spec input;
  let ser = serialize_u16 input in
  assert (Seq.length ser == 2);
  E.lemma_u8_eq_intro rser32 ser ()
    (fun (i: nat) -> if i = 0 then () else if i = 1 then () else ());
  assert (serializer32_correct #_ #_ #parse_u16 serialize_u16 input ser32)
