module LowParse.SLow.VLData.Code
include LowParse.Spec.VLData
include LowParse.SLow.FLData
include LowParse.SLow.Int

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = LowParse.BigEndian
module Cast = FStar.Int.Cast
module B32 = FStar.Bytes

inline_for_extraction
let serialize32_bounded_integer_1'
  (buf: B32.lbytes 1)
  (input: bounded_integer 1)
: Tot (B32.lbytes 1)
= let byte0 = Cast.uint32_to_uint8 input in
  let buf0 = lb32set buf 0ul byte0 in
  buf0

inline_for_extraction
let serialize32_bounded_integer_2'
  (buf: B32.lbytes 2)
  (input: bounded_integer 2)
: Tot (B32.lbytes 2)
= let byte1 = Cast.uint32_to_uint8 input in
  let byte0v = U32.div input 256ul in
  let byte0 = Cast.uint32_to_uint8 byte0v in
  let buf0 : B32.lbytes 2 = lb32set buf 0ul byte0 in
  let buf1 : B32.lbytes 2 = lb32set buf0 1ul byte1 in
  buf1

inline_for_extraction
let serialize32_bounded_integer_3'
  (buf: B32.lbytes 3)
  (input: bounded_integer 3)
: Tot (B32.lbytes 3)
= let byte2 = Cast.uint32_to_uint8 input in
  let byte1v = U32.div input 256ul in
  let byte1 = Cast.uint32_to_uint8 byte1v in
  let byte0v = U32.div byte1v 256ul in
  let byte0 = Cast.uint32_to_uint8 byte0v in
  let buf0 = lb32set buf 0ul byte0 in
  let buf1 = lb32set buf0 1ul byte1 in
  let buf2 = lb32set buf1 2ul byte2 in
  buf2

inline_for_extraction
let decode32_bounded_integer_1'
 (b: B32.lbytes 1)
: Tot U32.t
= let r = B32.get b 0ul in
  let res = Cast.uint8_to_uint32 r in
  res

#set-options "--z3rlimit 64"

inline_for_extraction
let decode32_bounded_integer_3'
 (b: B32.lbytes 3)
: Tot U32.t
= let b0r = B32.get b 0ul in
  let b0 = Cast.uint8_to_uint32 b0r in
  let b1r = B32.get b 1ul in
  let b1 = Cast.uint8_to_uint32 b1r in
  let b2r = B32.get b 2ul in
  let b2 = Cast.uint8_to_uint32 b2r in
  FStar.UInt.pow2_values 32;
  FStar.UInt.pow2_values 8;
  let open FStar.Mul in
  assert (
    U32.v b0 == U8.v b0r /\
    U32.v b1 == U8.v b1r /\
    U32.v b2 == U8.v b2r /\
    U32.v b2 + 256 * (U32.v b1 + 256 * U32.v b0) < 4294967296
  );
  let res = U32.add b2 (U32.mul 256ul (U32.add b1 (U32.mul 256ul b0))) in
  res
