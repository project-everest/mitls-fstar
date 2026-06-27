module Calc.Protocol

module L = FStar.List.Tot
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module SM = Common.StateMachine
module TCP = Common.TCP
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine

open FStar.List.Tot
open Calc.Wire
open Calc.Spec
open Calc.Log

type calc_wire_message = b:bytes {
  Seq.length b == 5 /\
  parse_request b <> None
}

type calc_local_event =
  | CalcLocalNoop

let calc_wire_equal
  (m0 m1:calc_wire_message)
  : GTot prop =
  Seq.equal m0 m1

let calc_serialize_wire_message
  (msg:calc_wire_message)
  : GTot TCP.bytes =
  msg

let calc_parse_wire_message
  (input:TCP.bytes)
  : GTot (WF.parse_result calc_wire_message) =
  if 5 <= Seq.length input then
    let msg = Seq.slice input 0 5 in
    if parse_request msg <> None then
      Some (msg, Seq.slice input 5 (Seq.length input))
    else
      None
  else
    None

let calc_response_wire_message
  (resp:response)
  : calc_wire_message =
  serialize_response resp

let calc_wire_request
  (msg:calc_wire_message)
  : request =
  match parse_request msg with
  | Some req -> req
  | None -> Peek

let calc_wire_residual_after_prefix
  (msg:calc_wire_message)
  (rest:TCP.bytes)
  : TCP.bytes =
  Seq.slice (Seq.append msg rest) 5 (Seq.length (Seq.append msg rest))

let lemma_slice_full_5
  (msg:bytes{Seq.length msg == 5})
  : Lemma
      (ensures Seq.equal (Seq.slice msg 0 5) msg)
=
  Seq.lemma_len_slice msg 0 5;
  assert (forall (i:nat{i < Seq.length (Seq.slice msg 0 5)}).
    Seq.index (Seq.slice msg 0 5) i == Seq.index msg i);
  Seq.lemma_eq_intro (Seq.slice msg 0 5) msg

let lemma_calc_wire_parse_prefix_shape
  (msg:calc_wire_message)
  (rest:TCP.bytes)
  : Lemma
      (ensures
        Seq.equal (Seq.slice (Seq.append msg rest) 0 5) msg /\
        Seq.equal (calc_wire_residual_after_prefix msg rest) rest)
=
  Calc.Log.lemma_slice_append_prefix msg rest;
  lemma_slice_full_5 msg;
  Seq.lemma_eq_elim (Seq.slice msg 0 5) msg;
  assert (Seq.equal (Seq.slice (Seq.append msg rest) 0 5) msg);
  SP.append_slices msg rest;
  assert (Seq.equal rest (calc_wire_residual_after_prefix msg rest))

let lemma_calc_parse_serialize_exact
  (msg:calc_wire_message)
  : Lemma
      (ensures
        exists parsed.
          calc_parse_wire_message (calc_serialize_wire_message msg) ==
            Some (parsed, Seq.empty) /\
          calc_wire_equal parsed msg)
=
  lemma_slice_full_5 msg;
  assert (Seq.equal (Seq.slice msg 0 5) msg);
  Seq.lemma_eq_elim (Seq.slice msg 0 5) msg;
  Seq.lemma_len_slice msg 5 5;
  assert (Seq.equal (Seq.slice msg 5 (Seq.length msg)) Seq.empty);
  assert (calc_parse_wire_message (calc_serialize_wire_message msg) ==
    Some (msg, Seq.empty))

let lemma_calc_parse_serialize_prefix
  (msg:calc_wire_message)
  (rest:TCP.bytes)
  : Lemma
      (ensures
        exists parsed.
          calc_parse_wire_message
            (Seq.append (calc_serialize_wire_message msg) rest) ==
              Some (parsed, rest) /\
          calc_wire_equal parsed msg)
=
  lemma_calc_wire_parse_prefix_shape msg rest;
  assert (Seq.equal (Seq.slice (Seq.append msg rest) 0 5) msg);
  assert (Seq.equal (calc_wire_residual_after_prefix msg rest) rest);
  Seq.lemma_eq_elim (Seq.slice (Seq.append msg rest) 0 5) msg;
  Seq.lemma_eq_elim (calc_wire_residual_after_prefix msg rest) rest;
  assert (calc_parse_wire_message
    (Seq.append (calc_serialize_wire_message msg) rest) == Some (msg, rest))

noextract
let calc_wire_format : WF.wire_format calc_wire_message =
  {
    WF.wf_equal = calc_wire_equal;
    WF.wf_serialize = calc_serialize_wire_message;
    WF.wf_parse = calc_parse_wire_message;
    WF.wf_parse_serialize_exact = lemma_calc_parse_serialize_exact;
    WF.wf_parse_serialize_prefix = lemma_calc_parse_serialize_prefix;
  }

let calc_step
  (log0:calc_log)
  (ev:SM.event calc_wire_message calc_local_event)
  (log1:calc_log)
  (outputs:list calc_wire_message)
  : GTot prop =
  match ev with
  | SM.WireEvent msg ->
    let req = calc_wire_request msg in
    let (next_stack, resp) = step log0.current_state req in
    let resp_msg = calc_response_wire_message resp in
    log1.current_state == next_stack /\
    log1.requests == log0.requests @ [req] /\
    log1.responses == log0.responses @ [resp] /\
    Seq.equal log1.input_bytes (Seq.append log0.input_bytes msg) /\
    Seq.equal log1.output_bytes (Seq.append log0.output_bytes resp_msg) /\
    outputs == [resp_msg]
  | SM.LocalEvent CalcLocalNoop ->
    log1 == log0 /\
    outputs == []

noextract
let calc_state_machine
  : SM.state_machine calc_log calc_wire_message calc_local_event =
  {
    SM.sm_initial_state = initial_log;
    SM.sm_step = calc_step;
  }

noextract
let calc_wire_format_state_machine
  : WFSM.wire_format_state_machine calc_log calc_wire_message calc_local_event =
  {
    WFSM.wfsm_state_machine = calc_state_machine;
    WFSM.wfsm_wire_format = calc_wire_format;
  }
