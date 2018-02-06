module LowParse.SLow.VLData.Proof.Parse.BoundedInteger3
open LowParse.SLow.VLData.Code

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = LowParse.BigEndian
module Cast = FStar.Int.Cast
module B32 = FStar.Bytes

#reset-options "--z3rlimit 1024 --z3refresh  --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped --max_fuel 64 --max_ifuel 64"

let decode32_bounded_integer_3_correct
  (b: B32.lbytes 3)
: Lemma
  (let y = decode32_bounded_integer_3' b in
   U32.v y < pow2 (Prims.op_Multiply 8 3) /\
   (y <: bounded_integer 3) == decode_bounded_integer 3 (B32.reveal b))
= let b0r = B32.get b 0ul in
  assert (b0r == B32.index b 0);
  B32.index_reveal b 0;
  let b0 = Cast.uint8_to_uint32 b0r in
  let b1r = B32.get b 1ul in
  assert (b1r == B32.index b 1);
  B32.index_reveal b 1;
  let b1 = Cast.uint8_to_uint32 b1r in
  let b2r = B32.get b 2ul in
  assert (b2r == B32.index b 2);
  B32.index_reveal b 2;
  let b2 = Cast.uint8_to_uint32 b2r in
  let res = U32.add b2 (U32.mul 256ul (U32.add b1 (U32.mul 256ul b0))) in
  E.be_to_n_3_spec (B32.reveal b);
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  assert (U32.v res == U32.v (decode_bounded_integer 3 (B32.reveal b) <: U32.t));
  U32.v_inj res (decode_bounded_integer 3 (B32.reveal b) <: U32.t);
  assert (U32.v res < pow2 (FStar.Mul.op_Star 8 3));
  ()
