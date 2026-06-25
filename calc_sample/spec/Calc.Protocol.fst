module Calc.Protocol

module CP = Common.Protocol
module TCP = Common.TCP
module L = FStar.List.Tot
module Seq = FStar.Seq

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
