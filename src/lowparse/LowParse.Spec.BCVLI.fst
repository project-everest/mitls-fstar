module LowParse.Spec.BCVLI
include LowParse.Spec.Int
include LowParse.Spec.VLData // for parse_bounded_integer

module U32 = FStar.UInt32
module Seq = FStar.Seq

inline_for_extraction
let parse_bcvli_payload_kind = {
  parser_kind_low = 0;
  parser_kind_high = Some 4;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
}

let parse_bcvli_payload (x: bounded_integer 1) : Tot (parser parse_bcvli_payload_kind U32.t) =
  if U32.v x <= 252 then weaken parse_bcvli_payload_kind (parse_ret (x <: U32.t)) else
  if U32.v x = 253 then weaken parse_bcvli_payload_kind ((parse_bounded_integer 2 `parse_filter` (fun x -> U32.v x >= 253)) `parse_synth` (fun x -> (x <: U32.t))) else
  if U32.v x = 254 then weaken parse_bcvli_payload_kind ((parse_bounded_integer 4 `parse_filter` (fun x -> U32.v x >= 65536)) `parse_synth` (fun x -> (x <: U32.t))) else
  fail_parser parse_bcvli_payload_kind U32.t

#push-options "--z3rlimit 32"

let parse_bcvli_payload_and_then_cases_injective : squash (and_then_cases_injective parse_bcvli_payload) =
  and_then_cases_injective_intro parse_bcvli_payload (fun x1 x2 b1 b2 ->
    parse_synth_eq (parse_bounded_integer 2 `parse_filter` (fun x -> U32.v x >= 253)) (fun x -> (x <: U32.t)) b1;
    parse_synth_eq (parse_bounded_integer 2 `parse_filter` (fun x -> U32.v x >= 253)) (fun x -> (x <: U32.t)) b2;
    parse_synth_eq (parse_bounded_integer 4 `parse_filter` (fun x -> U32.v x >= 65536)) (fun x -> (x <: U32.t)) b1;
    parse_synth_eq (parse_bounded_integer 4 `parse_filter` (fun x -> U32.v x >= 65536)) (fun x -> (x <: U32.t)) b2
  )

#pop-options

inline_for_extraction
let parse_bcvli_kind = and_then_kind (parse_bounded_integer_kind 1) parse_bcvli_payload_kind

let parse_bcvli : parser parse_bcvli_kind U32.t =
  parse_bounded_integer 1 `and_then` parse_bcvli_payload

let parse_bcvli_eq (b: bytes) : Lemma
  (parse parse_bcvli b == (match parse (parse_bounded_integer 1) b with
  | None -> None
  | Some (x32, consumed_x) ->
    let x = U32.v x32 in
    if x <= 252 then Some (x32, consumed_x) else
    let b' = Seq.slice b consumed_x (Seq.length b) in
    if x = 253 then
      match parse (parse_bounded_integer 2) b' with
      | None -> None
      | Some (y, consumed_y) ->
        if U32.v y < 253 then None (* redundant representations not supported, non-malleability *) else Some (y, consumed_x + consumed_y)
    else if x = 254 then
      match parse (parse_bounded_integer 4) b' with
      | None -> None
      | Some (y, consumed_y) ->
        if U32.v y < 65536 then None (* redundant representations not supported, non-malleability *) else Some (y, consumed_x + consumed_y)
    else None (* 64-bit integers not supported *)
  ))
= and_then_eq (parse_bounded_integer 1) parse_bcvli_payload b;
  match parse (parse_bounded_integer 1) b with
  | None -> ()
  | Some (x32, consumed_x) ->
    let b' = Seq.slice b consumed_x (Seq.length b) in
    parse_synth_eq (parse_bounded_integer 2 `parse_filter` (fun x -> U32.v x >= 253)) (fun x -> (x <: U32.t)) b';
    parse_filter_eq (parse_bounded_integer 2) (fun x -> U32.v x >= 253) b';
    parse_synth_eq (parse_bounded_integer 4 `parse_filter` (fun x -> U32.v x >= 65536)) (fun x -> (x <: U32.t)) b';
    parse_filter_eq (parse_bounded_integer 4) (fun x -> U32.v x >= 65536) b'
