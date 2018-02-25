module LowParse.SLow.Int.Proof

module Seq = FStar.Seq
module E = LowParse.BigEndian
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B32 = FStar.Bytes
module Cast = FStar.Int.Cast

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 128 --max_ifuel 32 --max_fuel 32"

let serialize32_u8_correct
  input
= b32_reveal_create 1ul input

let serialize32_u16_correct = LowParse.SLow.Int.Proof.SerializeU16.serialize32_u16_correct

let serialize32_u32_correct = LowParse.SLow.Int.Proof.SerializeU32.serialize32_u32_correct

let decode32_u16_correct = LowParse.SLow.Int.Proof.ParseU16.decode32_u16_correct

let decode32_u32_correct = LowParse.SLow.Int.Proof.ParseU32.decode32_u32_correct
