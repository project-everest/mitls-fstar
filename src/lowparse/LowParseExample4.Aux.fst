module LowParseExample4.Aux

module LPC = LowParse.Low.Combinators
module LPI = LowParse.Low.Int
module LP = LowParse.Low.Base

module U32 = FStar.UInt32
module U16 = FStar.UInt16
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

let parse_inner_raw =
  LPI.parse_u16 `LPC.nondep_then` LPI.parse_u16

let synth_inner (x: (U16.t * U16.t)) : Tot inner =
  let (left, right) = x in
  {left = left; right = right;}

let parse_inner' : LP.parser _ inner =
  parse_inner_raw `LPC.parse_synth` synth_inner

let parse_inner_kind = LP.get_parser_kind parse_inner'

let parse_inner = parse_inner'

let parse_inner_intro =
  LPC.exactly_contains_valid_data_synth parse_inner_raw synth_inner

let parse_t_raw =
  parse_inner ` LPC.nondep_then` LPI.parse_u32

let synth_t (x: (inner * U32.t)) : Tot t =
  let (inner, last) = x in
  {inner = inner; last = last;}

let parse_t' = parse_t_raw `LPC.parse_synth` synth_t

let parse_t_kind = LP.get_parser_kind parse_t'

let parse_t = parse_t'

let parse_t_intro =
  LPC.exactly_contains_valid_data_synth parse_t_raw synth_t
