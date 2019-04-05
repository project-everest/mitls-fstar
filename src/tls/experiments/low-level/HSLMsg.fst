module HSLMsg

module LP = LowParse.Low

open FStar.BaseTypes

type msg = {
  x: uint32;
  y: uint32
}

let msg_size :uint32 = 8ul

let synth_msg (t:(uint32 * uint32)) :msg = { x = fst t; y = snd t }

let msg_parser :LP.parser _ msg =
  (LP.parse_u32 `LP.nondep_then` LP.parse_u32) `LP.parse_synth` synth_msg

let msg_validator :LP.validator32 msg_parser =
  LP.validate32_total_constant_size msg_parser 8l ()

(* TODO: accessors *)
