module LowParse.Spec.Int

module Aux = LowParse.Spec.Int.Aux
module Seq = FStar.Seq
module E = LowParse.BigEndian
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

let parse_u8 = Aux.parse_u8

val parse_u8_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 1))
  (ensures (
    let pp = parse parse_u8 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U8.v v == E.be_to_n (Seq.slice b 0 1)
  )))

let parse_u8_spec b = Aux.parse_u8_spec b

let serialize_u8 = Aux.serialize_u8

let parse_u16 = Aux.parse_u16

val parse_u16_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 2))
  (ensures (
    let pp = parse parse_u16 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U16.v v == E.be_to_n (Seq.slice b 0 2)
  )))

let parse_u16_spec b = Aux.parse_u16_spec b

let serialize_u16 = Aux.serialize_u16

let parse_u32 = Aux.parse_u32

val parse_u32_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 4))
  (ensures (
    let pp = parse parse_u32 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U32.v v == E.be_to_n (Seq.slice b 0 4)
  )))

let parse_u32_spec = Aux.parse_u32_spec

let serialize_u32 = Aux.serialize_u32
