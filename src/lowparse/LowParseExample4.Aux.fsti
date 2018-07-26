module LowParseExample4.Aux

module LPC = LowParse.Spec.Combinators
module LPI = LowParse.Low.Int
module LP = LowParse.Low.Base

module U32 = FStar.UInt32
module U16 = FStar.UInt16
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

val parse_inner_kind: (k: LP.parser_kind { k.LP.parser_kind_subkind == Some LP.ParserStrong})

val parse_inner: LP.parser parse_inner_kind inner

val parse_inner_intro
  (h: HS.mem)
  (b: LP.buffer8)
  (lo: U32.t)
  (x: U16.t * U16.t)
  (hi: U32.t)
: Lemma
  (requires (
    LP.exactly_contains_valid_data h (LPI.parse_u16 `LPC.nondep_then` LPI.parse_u16) b lo x hi
  ))
  (ensures (
    let (l, r) = x in
    LP.exactly_contains_valid_data h parse_inner b lo ({ left = l; right = r; }) hi
  ))
  [SMTPat (LP.exactly_contains_valid_data h (LPI.parse_u16 `LPC.nondep_then` LPI.parse_u16) b lo x hi)]

val parse_t_kind : (k: LP.parser_kind { k.LP.parser_kind_subkind == Some LP.ParserStrong})

val parse_t : LP.parser parse_t_kind t

val parse_t_intro
  (h: HS.mem)
  (b: LP.buffer8)
  (lo: U32.t)
  (x: inner * U32.t)
  (hi: U32.t)
: Lemma
  (requires (
    LP.exactly_contains_valid_data h (parse_inner `LPC.nondep_then` LPI.parse_u32) b lo x hi
  ))
  (ensures (
    let (l, r) = x in
    LP.exactly_contains_valid_data h parse_t b lo ({ inner = l; last = r; }) hi
  ))
  [SMTPat (LP.exactly_contains_valid_data h (parse_inner `LPC.nondep_then` LPI.parse_u32) b lo x hi)]
