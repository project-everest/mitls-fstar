module LowParse.SLow.VLData.Proof.Parse.BoundedInteger1
open LowParse.SLow.VLData.Code

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = LowParse.BigEndian
module Cast = FStar.Int.Cast
module B32 = FStar.Bytes

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 128 --max_ifuel 64 --max_fuel 64"

let decode32_bounded_integer_1_correct
 (b: B32.lbytes 1)
: Lemma
  (let y : U32.t = decode32_bounded_integer_1' b in
   U32.v y < pow2 (Prims.op_Multiply 8 1) /\
   (y <: bounded_integer 1) == decode_bounded_integer 1 (B32.reveal b))
=
  let r = B32.get b 0ul in
  assert (r == B32.index b 0);
  B32.index_reveal b 0;
  E.be_to_n_1_spec (B32.reveal b);
  let res : U32.t = Cast.uint8_to_uint32 r in
  assert (res == (decode_bounded_integer 1 (B32.reveal b) <: U32.t));
  assert (U32.v res < pow2 (FStar.Mul.op_Star 8 1));
  ()
