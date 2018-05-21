module LowParse.Low.Int

module Aux = LowParse.Low.Int.Aux
module Unique = LowParse.Spec.Int.Unique
module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = FStar.Buffer

let parse32_u8 =
  (fun (input: pointer buffer8) (len: pointer U32.t) ->
    let h = HST.get () in
    let _ = Unique.parse_u8_unique (B.as_seq h (B.get h input 0)) in
    Aux.parse32_u8 input len
  )

let parse32_u16 =
  (fun (input: pointer buffer8) (len: pointer U32.t) ->
    let h = HST.get () in
    let _ = Unique.parse_u16_unique (B.as_seq h (B.get h input 0)) in
    Aux.parse32_u16 input len
  )

let parse32_u32 =
  (fun (input: pointer buffer8) (len: pointer U32.t) ->
    let h = HST.get () in
    let _ = Unique.parse_u32_unique (B.as_seq h (B.get h input 0)) in
    Aux.parse32_u32 input len
  )
