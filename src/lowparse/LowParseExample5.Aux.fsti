module LowParseExample5.Aux

module LPC = LowParse.Spec.Combinators
module LPI = LowParse.Low.Int
module LP = LowParse.Low.Base

module U32 = FStar.UInt32
module U16 = FStar.UInt16
module I32 = FStar.Int32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

noeq
type inner = {
  left: U16.t;
  right: U16.t;
}

noeq
type t = {
  inner: inner;
  last: U32.t;
}

val parse_inner_kind: (k: LP.parser_kind { k.LP.parser_kind_subkind == Some LP.ParserStrong /\ k.LP.parser_kind_high == Some 4 })

val parse_inner: LP.parser parse_inner_kind inner

val serialize_inner: LP.serializer parse_inner

val serialize_inner_intro
  (h: HS.mem)
  (b: LP.buffer8)
  (lo: I32.t)
  (x: U16.t * U16.t)
  (hi: I32.t)
: Lemma
  (requires (
    LP.contains_valid_serialized_data_or_fail h (LPC.serialize_nondep_then _ LPI.serialize_u16 () _ LPI.serialize_u16) b lo x hi
  ))
  (ensures (
    let (l, r) = x in
    LP.contains_valid_serialized_data_or_fail h serialize_inner b lo ({ left = l; right = r; }) hi
  ))
  [SMTPat (LP.contains_valid_serialized_data_or_fail h (LPC.serialize_nondep_then _ LPI.serialize_u16 () _ LPI.serialize_u16) b lo x hi)]

val parse_t_kind : (k: LP.parser_kind { k.LP.parser_kind_subkind == Some LP.ParserStrong /\ k.LP.parser_kind_high == Some 8 })

val parse_t : LP.parser parse_t_kind t

val serialize_t : LP.serializer parse_t

val serialize_t_intro
  (h: HS.mem)
  (b: LP.buffer8)
  (lo: I32.t)
  (x: inner * U32.t)
  (hi: I32.t)
: Lemma
  (requires (
    LP.contains_valid_serialized_data_or_fail h (LPC.serialize_nondep_then _ serialize_inner () _ LPI.serialize_u32) b lo x hi
  ))
  (ensures (
    let (l, r) = x in
    LP.contains_valid_serialized_data_or_fail h serialize_t b lo ({ inner = l; last = r; }) hi
  ))
  [SMTPat (LP.contains_valid_serialized_data_or_fail h (LPC.serialize_nondep_then _ serialize_inner () _ LPI.serialize_u32) b lo x hi)]
