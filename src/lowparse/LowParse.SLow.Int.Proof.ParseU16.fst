module LowParse.SLow.Int.Proof.ParseU16
open LowParse.Spec.Int
open LowParse.SLow.Int.Code

module Seq = FStar.Seq
module E = LowParse.BigEndian
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B32 = FStar.Bytes
module Cast = FStar.Int.Cast

#reset-options "--z3rlimit 128 --max_fuel 64 --max_ifuel 64"

let decode32_u16_correct
  (b: B32.lbytes 2)
: Lemma (decode32_u16' b == decode_u16 (B32.reveal b))
=     let b1 = B32.get b 1ul in
      assert_norm (b1 == B32.index b 1);
      b32_index_reveal b 1;
      let b0 = B32.get b 0ul in
      assert_norm (b0 == B32.index b 0);
      b32_index_reveal b 0;
      assert_norm (pow2 8 == 256);
      let r =
	U16.add (Cast.uint8_to_uint16 b1) (U16.mul 256us (Cast.uint8_to_uint16 b0))
      in
      assert (
	E.lemma_be_to_n_is_bounded (B32.reveal b);
	U16.v r == U8.v b1 + Prims.op_Multiply 256 (U8.v b0)
      );
      assert (
	E.lemma_be_to_n_is_bounded (B32.reveal b);
	U16.v r == U8.v b1 + Prims.op_Multiply (pow2 8) (U8.v b0)
      );
      E.be_to_n_2_spec (B32.reveal b);
      assert (
	E.lemma_be_to_n_is_bounded (B32.reveal b);
	U16.v r == E.be_to_n (B32.reveal b)
      );
      assert (
      	E.lemma_be_to_n_is_bounded (B32.reveal b);
	U16.v r == U16.v (decode_u16 (B32.reveal b))
      );
      assert (
	U16.v_inj r (decode_u16 (B32.reveal b));
	(r == decode_u16 (B32.reveal b))
      );
      ()
