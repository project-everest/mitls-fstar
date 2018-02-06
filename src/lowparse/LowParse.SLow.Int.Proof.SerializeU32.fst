module LowParse.SLow.Int.Proof.SerializeU32
open LowParse.Spec.Int
open LowParse.SLow.Int.Code

module Seq = FStar.Seq
module E = LowParse.BigEndian
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B32 = FStar.Bytes
module Cast = FStar.Int.Cast

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 512 --max_ifuel 64 --max_fuel 64"

let serialize_u32_spec
  (input: U32.t)
: Lemma
  (let ser = serialize_u32 input in
   Seq.length ser == 4 /\
   U8.v (Seq.index ser 3) == U32.v input % 256 /\
   U8.v (Seq.index ser 2) == (U32.v input / 256) % 256 /\
   U8.v (Seq.index ser 1) == ((U32.v input / 256) / 256) % 256 /\
   U8.v (Seq.index ser 0) == (((U32.v input / 256) / 256) / 256) % 256
  )
= E.index_n_to_be 4ul (U32.v input) 3;
  E.index_n_to_be' 4 (U32.v input) 3;
  E.index_n_to_be 4ul (U32.v input) 2;
  E.index_n_to_be' 4 (U32.v input) 2;
  E.index_n_to_be 4ul (U32.v input) 1;
  E.index_n_to_be' 4 (U32.v input) 1;
  E.index_n_to_be 4ul (U32.v input) 0;
  E.index_n_to_be' 4 (U32.v input) 0

let serialize32_u32_correct
  (buf: B32.lbytes 4)
  (input: U32.t)
: Lemma
  (serializer32_correct #_ #_ #parse_u32 serialize_u32 input (serialize32_u32' buf input))
= let ser32 = serialize32_u32' buf input in
  let rser32 = B32.reveal ser32 in
  assert (pow2 8 == 256);
  assert (pow2 16 == 65536);
  assert (pow2 32 == 4294967296);
  let byte3 = Cast.uint32_to_uint8 input in
  assert (U8.v byte3 == U32.v input % 256);
  assert (Seq.index rser32 3 == byte3);
  let byte2v = U32.div input 256ul in
  let byte2 = Cast.uint32_to_uint8 byte2v in
  assert (U8.v byte2 == (U32.v input / 256) % 256);
  assert (Seq.index rser32 2 == byte2);
  let byte1v = U32.div byte2v 256ul in
  let byte1 = Cast.uint32_to_uint8 byte1v in
  assert (U8.v byte1 == ((U32.v input / 256) / 256) % 256);
  assert (Seq.index rser32 1 == byte1);
  let byte0v = U32.div byte1v 256ul in
  let byte0 = Cast.uint32_to_uint8 byte0v in
  assert (U8.v byte0 == (((U32.v input / 256) / 256) / 256) % 256);
  assert (Seq.index rser32 0 == byte0);
  serialize_u32_spec input;
  let ser = serialize_u32 input in
  assert (Seq.length ser == 4);
  E.lemma_u8_eq_intro rser32 ser ()
    (fun (i: nat) -> if i = 0 then () else if i = 1 then () else if i = 2 then () else if i = 3 then () else ());
  assert (serializer32_correct #_ #_ #parse_u32 serialize_u32 input ser32)
