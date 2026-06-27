module Calc.Protocol

module CP = Common.Protocol
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

type calc_wire_message =
  | CalcRequest of request
  | CalcResponse of response

type calc_event =
  | CalcNetworkRequest of request
  | CalcLocalNoop

let calc_all_parse_bytes (bytes:TCP.bytes) : prop =
  if Seq.length bytes % 5 == 0
  then all_parse bytes
  else False

let rec calc_request_messages (reqs:list request)
  : Tot (list calc_wire_message)
        (decreases reqs)
  =
  match reqs with
  | [] -> []
  | req :: rest -> CalcRequest req :: calc_request_messages rest

let rec calc_response_messages (resps:list response)
  : Tot (list calc_wire_message)
        (decreases resps)
  =
  match resps with
  | [] -> []
  | resp :: rest -> CalcResponse resp :: calc_response_messages rest

let rec calc_request_events (reqs:list request)
  : Tot (list calc_event)
        (decreases reqs)
  =
  match reqs with
  | [] -> []
  | req :: rest -> CalcNetworkRequest req :: calc_request_events rest

let rec calc_received_wire_log (reqs:list request)
  : Tot (list (CP.directed_message calc_wire_message))
        (decreases reqs)
  =
  match reqs with
  | [] -> []
  | req :: rest -> CP.received (CalcRequest req) :: calc_received_wire_log rest

let rec calc_sent_wire_log (resps:list response)
  : Tot (list (CP.directed_message calc_wire_message))
        (decreases resps)
  =
  match resps with
  | [] -> []
  | resp :: rest -> CP.sent (CalcResponse resp) :: calc_sent_wire_log rest

let calc_processed_history (log:calc_log) : TCP.history =
  {
    TCP.tcp_received = log.input_bytes;
    TCP.tcp_sent = log.output_bytes;
  }

let calc_wire_log (log:calc_log) : list (CP.directed_message calc_wire_message) =
  calc_received_wire_log log.requests @ calc_sent_wire_log log.responses

let calc_event_log (log:calc_log) : list calc_event =
  calc_request_events log.requests

let calc_stream_matches
  (dir:CP.network_direction)
  (bytes:TCP.bytes)
  (messages:list calc_wire_message)
  (residual:TCP.bytes)
  : prop =
  match dir with
  | CP.NetworkReceived ->
    Seq.equal residual Seq.empty /\
    exists reqs.
      messages == calc_request_messages reqs /\
      parse_requests bytes == reqs /\
      calc_all_parse_bytes bytes
  | CP.NetworkSent ->
    Seq.equal residual Seq.empty /\
    exists resps.
      messages == calc_response_messages resps /\
      serialize_responses resps `Seq.equal` bytes

let calc_wire_history_matches
  (tcp:TCP.history)
  (wire_log:list (CP.directed_message calc_wire_message))
  : prop =
  exists reqs resps.
    wire_log == calc_received_wire_log reqs @ calc_sent_wire_log resps /\
    parse_requests tcp.TCP.tcp_received == reqs /\
    calc_all_parse_bytes tcp.TCP.tcp_received /\
    serialize_responses resps `Seq.equal` tcp.TCP.tcp_sent

noextract
let calc_wire_format : CP.wire_format calc_wire_message =
  {
    CP.wf_stream_matches = calc_stream_matches;
    CP.wf_history_matches = calc_wire_history_matches;
  }

let calc_transport_matches (tcp:TCP.history) (log:calc_log) : prop =
  TCP.history_equal tcp (calc_processed_history log)

let calc_events_refine_wire (log:calc_log) : prop =
  calc_event_log log == calc_request_events log.requests /\
  calc_wire_log log == calc_received_wire_log log.requests @
                       calc_sent_wire_log log.responses

let calc_step
  (log0:calc_log)
  (ev:calc_event)
  (log1:calc_log)
  (out:list (CP.directed_message calc_wire_message))
  : prop =
  match ev with
  | CalcNetworkRequest req ->
    let (next_stack, resp) = step log0.current_state req in
    log1.current_state == next_stack /\
    log1.requests == log0.requests @ [req] /\
    log1.responses == log0.responses @ [resp] /\
    out == [CP.sent (CalcResponse resp)]
  | CalcLocalNoop ->
    log1 == log0 /\
    out == []

let calc_state_valid (log:calc_log) : prop =
  log_consistent log /\
  calc_wire_format.CP.wf_history_matches
    (calc_processed_history log)
    (calc_wire_log log) /\
  calc_transport_matches
    (calc_processed_history log)
    log /\
  calc_events_refine_wire log

let lemma_calc_state_valid_from_log_consistent
  (log:calc_log)
  : Lemma
      (requires log_consistent log)
      (ensures calc_state_valid log)
  =
  assert (parse_requests log.input_bytes == log.requests);
  assert (calc_all_parse_bytes log.input_bytes);
  assert (serialize_responses log.responses `Seq.equal` log.output_bytes);
  assert (calc_wire_format.CP.wf_history_matches
    (calc_processed_history log)
    (calc_wire_log log));
  assert (calc_transport_matches (calc_processed_history log) log);
  assert (calc_events_refine_wire log)

let lemma_calc_state_valid_layers
  (log:calc_log)
  : Lemma
      (requires calc_state_valid log)
      (ensures
        calc_wire_format.CP.wf_history_matches
          (calc_processed_history log)
          (calc_wire_log log) /\
        calc_transport_matches
          (calc_processed_history log)
          log /\
        calc_events_refine_wire log /\
        log_consistent log)
  =
  ()

noextract
let calc_protocol : CP.state_machine_protocol calc_log calc_wire_message calc_event =
  {
    CP.sm_wire_format = calc_wire_format;
    CP.sm_processed_history = calc_processed_history;
    CP.sm_wire_log = calc_wire_log;
    CP.sm_event_log = calc_event_log;
    CP.sm_transport_matches = calc_transport_matches;
    CP.sm_events_refine_wire = calc_events_refine_wire;
    CP.sm_step = calc_step;
    CP.sm_invariant = log_consistent;
    CP.sm_valid = calc_state_valid;
    CP.sm_valid_implies_layers = lemma_calc_state_valid_layers;
  }

type calc_frame = b:bytes {
  Seq.length b == 5 /\
  parse_request b <> None
}

type calc_frame_local_event =
  | CalcFrameLocalNoop

let calc_frame_equal
  (m0 m1:calc_frame)
  : GTot prop =
  Seq.equal m0 m1

let calc_serialize_frame
  (msg:calc_frame)
  : GTot TCP.bytes =
  msg

let calc_parse_frame
  (input:TCP.bytes)
  : GTot (WF.parse_result calc_frame) =
  if 5 <= Seq.length input then
    let msg = Seq.slice input 0 5 in
    if parse_request msg <> None then
      Some (msg, Seq.slice input 5 (Seq.length input))
    else
      None
  else
    None

let calc_response_frame
  (resp:response)
  : calc_frame =
  serialize_response resp

let calc_frame_request
  (msg:calc_frame)
  : request =
  match parse_request msg with
  | Some req -> req
  | None -> Peek

let calc_frame_residual_after_prefix
  (msg:calc_frame)
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

let lemma_calc_frame_parse_prefix_shape
  (msg:calc_frame)
  (rest:TCP.bytes)
  : Lemma
      (ensures
        Seq.equal (Seq.slice (Seq.append msg rest) 0 5) msg /\
        Seq.equal (calc_frame_residual_after_prefix msg rest) rest)
=
  Calc.Log.lemma_slice_append_prefix msg rest;
  lemma_slice_full_5 msg;
  Seq.lemma_eq_elim (Seq.slice msg 0 5) msg;
  assert (Seq.equal (Seq.slice (Seq.append msg rest) 0 5) msg);
  SP.append_slices msg rest;
  assert (Seq.equal rest (calc_frame_residual_after_prefix msg rest))

let lemma_calc_parse_serialize_exact
  (msg:calc_frame)
  : Lemma
      (ensures
        exists parsed.
          calc_parse_frame (calc_serialize_frame msg) ==
            Some (parsed, Seq.empty) /\
          calc_frame_equal parsed msg)
=
  lemma_slice_full_5 msg;
  assert (Seq.equal (Seq.slice msg 0 5) msg);
  Seq.lemma_eq_elim (Seq.slice msg 0 5) msg;
  Seq.lemma_len_slice msg 5 5;
  assert (Seq.equal (Seq.slice msg 5 (Seq.length msg)) Seq.empty);
  assert (calc_parse_frame (calc_serialize_frame msg) ==
    Some (msg, Seq.empty))

let lemma_calc_parse_serialize_prefix
  (msg:calc_frame)
  (rest:TCP.bytes)
  : Lemma
      (ensures
        exists parsed.
          calc_parse_frame
            (Seq.append (calc_serialize_frame msg) rest) ==
              Some (parsed, rest) /\
          calc_frame_equal parsed msg)
=
  lemma_calc_frame_parse_prefix_shape msg rest;
  assert (Seq.equal (Seq.slice (Seq.append msg rest) 0 5) msg);
  assert (Seq.equal (calc_frame_residual_after_prefix msg rest) rest);
  Seq.lemma_eq_elim (Seq.slice (Seq.append msg rest) 0 5) msg;
  Seq.lemma_eq_elim (calc_frame_residual_after_prefix msg rest) rest;
  assert (calc_parse_frame
    (Seq.append (calc_serialize_frame msg) rest) == Some (msg, rest))

noextract
let calc_frame_wire_format : WF.wire_format calc_frame =
  {
    WF.wf_equal = calc_frame_equal;
    WF.wf_serialize = calc_serialize_frame;
    WF.wf_parse = calc_parse_frame;
    WF.wf_parse_serialize_exact = lemma_calc_parse_serialize_exact;
  }

noextract
let calc_frame_wire_format_stream_laws :
  WF.wire_format_stream_laws calc_frame calc_frame_wire_format =
  {
    WF.wfsl_parse_serialize_prefix = lemma_calc_parse_serialize_prefix;
  }

let calc_frame_step
  (log0:calc_log)
  (ev:SM.event calc_frame calc_frame_local_event)
  (log1:calc_log)
  (output:SM.step_output calc_frame unit)
  : GTot prop =
  match ev with
  | SM.WireEvent msg ->
    let req = calc_frame_request msg in
    let (next_stack, resp) = step log0.current_state req in
    let resp_msg = calc_response_frame resp in
    log1.current_state == next_stack /\
    log1.requests == log0.requests @ [req] /\
    log1.responses == log0.responses @ [resp] /\
    Seq.equal log1.input_bytes (Seq.append log0.input_bytes msg) /\
    Seq.equal log1.output_bytes (Seq.append log0.output_bytes resp_msg) /\
    output.SM.so_wire_outputs == [resp_msg] /\
    output.SM.so_local_outputs == []
  | SM.LocalEvent CalcFrameLocalNoop ->
    log1 == log0 /\
    output.SM.so_wire_outputs == [] /\
    output.SM.so_local_outputs == []

noextract
let calc_frame_state_machine
  : SM.state_machine calc_log calc_frame calc_frame_local_event unit =
  {
    SM.sm_initial_state = initial_log;
    SM.sm_step = calc_frame_step;
  }

noextract
let calc_frame_wire_format_state_machine
  : WFSM.wire_format_state_machine calc_log calc_frame calc_frame_local_event unit =
  {
    WFSM.wfsm_state_machine = calc_frame_state_machine;
    WFSM.wfsm_wire_format = calc_frame_wire_format;
  }
