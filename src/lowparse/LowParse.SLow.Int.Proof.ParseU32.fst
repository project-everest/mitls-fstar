module LowParse.SLow.Int.Proof.ParseU32
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

let decode32_u32_correct
  (b: B32.lbytes 4)
: Lemma (decode32_u32' b == decode_u32 (B32.reveal b))
=     let b3 = B32.get b 3ul in
      assert_norm (b3 == B32.index b 3);
      b32_index_reveal b 3;
      let b2 = B32.get b 2ul in
      assert_norm (b2 == B32.index b 2);
      b32_index_reveal b 2;
      let b1 = B32.get b 1ul in
      assert_norm (b1 == B32.index b 1);
      b32_index_reveal b 1;
      let b0 = B32.get b 0ul in
      assert_norm (b0 == B32.index b 0);
      b32_index_reveal b 0;
      assert_norm (pow2 8 == 256);
      let r =
        U32.add (Cast.uint8_to_uint32 b3) (U32.mul 256ul (
          U32.add (Cast.uint8_to_uint32 b2) (U32.mul 256ul (        
	  U32.add (Cast.uint8_to_uint32 b1) (U32.mul 256ul (
          Cast.uint8_to_uint32 b0
        ))))))
      in
      E.lemma_be_to_n_is_bounded (B32.reveal b);
      E.be_to_n_4_spec (B32.reveal b);
      assert (
	E.lemma_be_to_n_is_bounded (B32.reveal b);
	U32.v r == E.be_to_n (B32.reveal b)
      );
      assert (
      	E.lemma_be_to_n_is_bounded (B32.reveal b);
	U32.v r == U32.v (decode_u32 (B32.reveal b))
      );
      assert (
	U32.v_inj r (decode_u32 (B32.reveal b));
	(r == decode_u32 (B32.reveal b))
      );
      ()
