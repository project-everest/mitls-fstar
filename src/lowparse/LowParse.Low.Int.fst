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
module B = FStar.Buffer

#set-options "--z3rlimit 16"

inline_for_extraction
let parse32_u8 =
  (fun (input: pointer buffer8) (len: pointer U32.t) ->
    let h = HST.get () in
    let _ = Unique.parse_u8_unique (B.as_seq h (B.get h input 0)) in
    Aux.parse32_u8 input len
  )

inline_for_extraction
let parse32_u16 =
  (fun (input: pointer buffer8) (len: pointer U32.t) ->
    let h = HST.get () in
    let _ = Unique.parse_u16_unique (B.as_seq h (B.get h input 0)) in
    Aux.parse32_u16 input len
  )

inline_for_extraction
let parse32_u32 =
  (fun (input: pointer buffer8) (len: pointer U32.t) ->
    let h = HST.get () in
    let _ = Unique.parse_u32_unique (B.as_seq h (B.get h input 0)) in
    Aux.parse32_u32 input len
  )

inline_for_extraction
let validate32_u8 : validator32 parse_u8 =
  validate32_total_constant_size parse_u8 1ul ()

inline_for_extraction
let validate32_u16 : validator32 parse_u16 =
  validate32_total_constant_size parse_u16 2ul ()

inline_for_extraction
let validate32_u32 : validator32 parse_u32 =
  validate32_total_constant_size parse_u32 4ul ()

inline_for_extraction
let validate_nochk32_u8 : validator_nochk32 parse_u8 =
  validate_nochk32_constant_size parse_u8 1ul ()

inline_for_extraction
let validate_nochk32_u16 : validator_nochk32 parse_u16 =
  validate_nochk32_constant_size parse_u16 2ul ()

inline_for_extraction
let validate_nochk32_u32 : validator_nochk32 parse_u32 =
  validate_nochk32_constant_size parse_u32 4ul ()
