module LowParse.Low.Int
open LowParse.Low.Combinators

module Aux = LowParse.Low.Int.Aux
module Unique = LowParse.Spec.Int.Unique
module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer

#set-options "--z3rlimit 16"

inline_for_extraction
let parse32_u8 =
  (fun input ->
    let h = HST.get () in
    let _ = Unique.parse_u8_unique (B.as_seq h input) in
    Aux.parse32_u8 input
  )

inline_for_extraction
let parse32_u16 =
  (fun input ->
    let h = HST.get () in
    let _ = Unique.parse_u16_unique (B.as_seq h input) in
    Aux.parse32_u16 input
  )

inline_for_extraction
let parse32_u32 =
  (fun input ->
    let h = HST.get () in
    let _ = Unique.parse_u32_unique (B.as_seq h input) in
    Aux.parse32_u32 input
  )
