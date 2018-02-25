module LowParse.SLow.Int.Code
// include LowParse.Spec.Int
include LowParse.SLow.Combinators

module Seq = FStar.Seq
module E = LowParse.BigEndian
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B32 = FStar.Bytes
module Cast = FStar.Int.Cast

inline_for_extraction
let serialize32_u8'
  (input: U8.t)
: Tot (B32.lbytes 1)
= let res : B32.bytes = B32.create 1ul input in
  res

inline_for_extraction
let serialize32_u16'
  (buf: B32.lbytes 2)
  (input: U16.t)
: Tot (B32.lbytes 2)
= let byte1 = Cast.uint16_to_uint8 input in
  let byte0v = U16.div input 256us in
  let byte0 = Cast.uint16_to_uint8 byte0v in
  let buf0 = lb32set buf 0ul byte0 in
  let buf1 = lb32set buf0 1ul byte1 in
  buf1

inline_for_extraction
let serialize32_u32'
  (buf: B32.lbytes 4)
  (input: U32.t)
: Tot (B32.lbytes 4)
= let byte3 = Cast.uint32_to_uint8 input in
  let byte2v = U32.div input 256ul in
  let byte2 = Cast.uint32_to_uint8 byte2v in
  let byte1v = U32.div byte2v 256ul in
  let byte1 = Cast.uint32_to_uint8 byte1v in
  let byte0v = U32.div byte1v 256ul in
  let byte0 = Cast.uint32_to_uint8 byte0v in
  let buf0 = lb32set buf 0ul byte0 in
  let buf1 = lb32set buf0 1ul byte1 in
  let buf2 = lb32set buf1 2ul byte2 in
  let buf3 = lb32set buf2 3ul byte3 in
  buf3

inline_for_extraction
let decode32_u16'
  (b: B32.lbytes 2)
: Tot U16.t
=     let b1 = B32.get b 1ul in
      let b0 = B32.get b 0ul in
      let r =
	U16.add (Cast.uint8_to_uint16 b1) (U16.mul 256us (Cast.uint8_to_uint16 b0))
      in
      r

inline_for_extraction
let decode32_u32'
  (b: B32.lbytes 4)
: Tot U32.t
=     let b3 = B32.get b 3ul in
      let b2 = B32.get b 2ul in
      let b1 = B32.get b 1ul in
      let b0 = B32.get b 0ul in
      let r =
        U32.add (Cast.uint8_to_uint32 b3) (U32.mul 256ul (
          U32.add (Cast.uint8_to_uint32 b2) (U32.mul 256ul (        
	  U32.add (Cast.uint8_to_uint32 b1) (U32.mul 256ul (
          Cast.uint8_to_uint32 b0
        ))))))
      in
      r
