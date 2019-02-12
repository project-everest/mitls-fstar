module LowParse.SLow.DER
include LowParse.Spec.DER
include LowParse.SLow.Combinators
include LowParse.SLow.VLData // for bounded_integer
open FStar.Mul

module Seq = FStar.Seq
module U8 = FStar.UInt8
module E = LowParse.BigEndian
module U32 = FStar.UInt32
module Math = LowParse.Math

#reset-options "--z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0"


(*
inline_for_extraction
let parse32_be_int_2
: Tot (parser32 (parse_seq_flbytes 2 `parse_synth` synth_be_int len))
= fun (input: B32.bytes) ->
  
