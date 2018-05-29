module LowParse.Low.Int.Aux
include LowParse.Spec.Int.Aux
include LowParse.Low.Combinators

module Seq = FStar.Seq
module E = LowParse.BigEndianImpl.Low
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B = LowStar.Buffer

inline_for_extraction
let parse32_u16 : parser32 parse_u16 =
  decode_u16_injective ();
    make_total_constant_size_parser32 2 2ul
      #U16.t
      decode_u16
      ()
      (fun input ->
        E.be_to_n_2 _ _ (E.u16 ()) input)

inline_for_extraction
let parse32_u32 : parser32 parse_u32 =
    decode_u32_injective ();
    make_total_constant_size_parser32 4 4ul
      #U32.t
      decode_u32
      ()
      (fun input ->
        E.be_to_n_4 _ _ (E.u32 ()) input)

inline_for_extraction
let parse32_u8 : parser32 parse_u8 =
  decode_u8_injective ();
  make_total_constant_size_parser32 1 1ul
    decode_u8
    ()
    (fun b -> B.index b 0ul)
