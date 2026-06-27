module Calc.Server.Protocol

#lang-pulse

open Pulse.Lib.Pervasives

module CP = Common.Protocol
module CPI = Common.LegacyProtocolImplementation
module TCP = Common.TCP
module CalcP = Calc.Protocol
module Seq = FStar.Seq
module U8 = FStar.UInt8
module Vec = Pulse.Lib.Vec

open Calc.Wire
open Calc.Log
open Calc.Impl.Types

noeq
type calc_network_args = {
  calc_req_buf: Vec.vec U8.t;
  calc_resp_buf: Vec.vec U8.t;
  calc_network_log0: Ghost.erased calc_log;
  calc_network_tcp0: Ghost.erased TCP.history;
}

noeq
type calc_local_args = {
  calc_local_log0: Ghost.erased calc_log;
  calc_local_tcp0: Ghost.erased TCP.history;
}

type calc_network_result = | CalcNetworkProcessed
type calc_local_result = | CalcLocalProcessed

let calc_parse_network
  (bytes:TCP.bytes)
  : GTot (CPI.parsed_messages CalcP.calc_wire_message)
  =
  if Seq.length bytes == 5 then
    match parse_request bytes with
    | Some req -> Some ([CalcP.CalcRequest req], Seq.empty)
    | None -> None
  else
    None

let calc_serialize_network
  (msg:CalcP.calc_wire_message)
  : GTot (option TCP.bytes)
  =
  match msg with
  | CalcP.CalcResponse resp -> Some (serialize_response resp)
  | CalcP.CalcRequest _ -> None

let calc_serialized_network
  (msg:CalcP.calc_wire_message)
  (bytes:TCP.bytes)
  : GTot prop =
  match msg with
  | CalcP.CalcResponse resp -> Seq.equal bytes (serialize_response resp)
  | CalcP.CalcRequest _ -> False

let lemma_calc_parse_network_correct
  (bytes:TCP.bytes)
  : Lemma
      (ensures
        (match calc_parse_network bytes with
        | None -> True
        | Some (msgs, residual) ->
          CalcP.calc_protocol.CP.sm_wire_format.CP.wf_stream_matches
            CP.NetworkReceived
            bytes
            msgs
            residual))
  =
  if Seq.length bytes == 5 then
    match parse_request bytes with
    | Some req ->
      let empty_bytes : TCP.bytes = Seq.empty in
      Calc.Log.lemma_parse_requests_single bytes req;
      assert (parse_requests bytes == [req]);
      assert (calc_parse_network bytes == Some ([CalcP.CalcRequest req], empty_bytes));
      assert (Seq.equal empty_bytes empty_bytes);
      assert (CalcP.calc_all_parse_bytes bytes);
      assert (CalcP.calc_request_messages [req] == [CalcP.CalcRequest req])
    | None -> ()

let lemma_calc_serialize_network_correct
  (msg:CalcP.calc_wire_message)
  : Lemma
      (ensures
        (match calc_serialize_network msg with
        | None -> True
        | Some bytes -> calc_serialized_network msg bytes))
  =
  match msg with
  | CalcP.CalcResponse resp ->
    assert (Seq.equal (serialize_response resp) (serialize_response resp))
  | CalcP.CalcRequest _ -> ()

noextract
let calc_server_tcp_channel
  (_srv:server_state)
  (_tcp:TCP.history)
  : slprop =
  emp

noextract
let calc_server_ghost_log
  (srv:server_state)
  (log:calc_log)
  : slprop =
  server_exactly srv log

noextract
let calc_server_runtime_resources
  (_srv:server_state)
  (_log:calc_log)
  (_tcp:TCP.history)
  : slprop =
  emp

noextract
[@@pulse_unfold]
let calc_server_invariant
  (srv:server_state)
  (log:calc_log)
  (tcp:TCP.history)
  : slprop =
  calc_server_tcp_channel srv tcp **
  calc_server_ghost_log srv log **
  calc_server_runtime_resources srv log tcp **
  pure (
    CalcP.calc_state_valid log /\
    CalcP.calc_transport_matches tcp log
  )

let calc_server_invariant_correct
  (log:calc_log)
  (tcp:TCP.history)
  : GTot prop =
  CalcP.calc_state_valid log /\
  CalcP.calc_transport_matches tcp log

let calc_tcp_history_matches (tcp:TCP.history) (log:calc_log) : GTot prop =
  CalcP.calc_transport_matches tcp log

let calc_network_args_state (args:calc_network_args) : GTot calc_log =
  Ghost.reveal args.calc_network_log0

let calc_network_args_tcp (args:calc_network_args) : GTot TCP.history =
  Ghost.reveal args.calc_network_tcp0

let calc_local_args_state (args:calc_local_args) : GTot calc_log =
  Ghost.reveal args.calc_local_log0

let calc_local_args_tcp (args:calc_local_args) : GTot TCP.history =
  Ghost.reveal args.calc_local_tcp0

noextract
[@@pulse_unfold]
let calc_server_network_frame
  (srv:server_state)
  (args:calc_network_args)
  : slprop =
  exists* (req_bytes: Ghost.erased bytes) (resp_bytes: Ghost.erased bytes).
    Vec.pts_to args.calc_req_buf req_bytes **
    Vec.pts_to args.calc_resp_buf resp_bytes **
    pure (
      Seq.length (Ghost.reveal req_bytes) == 5 /\
      Seq.length (Ghost.reveal resp_bytes) == 5 /\
      parse_request (Ghost.reveal req_bytes) <> None
    )

noextract
[@@pulse_unfold]
let calc_server_network_extra_post
  (srv:server_state)
  (args:calc_network_args)
  (_result:calc_network_result)
  (log1:calc_log)
  (_tcp1:TCP.history)
  : slprop =
  let log0 = Ghost.reveal args.calc_network_log0 in
  let tcp0 = Ghost.reveal args.calc_network_tcp0 in
  exists* (resp_bytes1: bytes) (req_bytes: Ghost.erased bytes).
    Vec.pts_to args.calc_req_buf req_bytes **
    Vec.pts_to args.calc_resp_buf resp_bytes1 **
    pure (
      log1.input_bytes `Seq.equal` Seq.append log0.input_bytes (Ghost.reveal req_bytes) /\
      log1.output_bytes `Seq.equal` Seq.append log0.output_bytes resp_bytes1 /\
      TCP.history_equal tcp0 (CalcP.calc_processed_history log0)
    )

let calc_network_effect
  (args:calc_network_args)
  (_result:calc_network_result)
  (log0:calc_log)
  (_tcp0:TCP.history)
  (log1:calc_log)
  (tcp1:TCP.history)
  : GTot prop =
  log_single_step log0 log1 /\
  TCP.history_equal tcp1 (CalcP.calc_processed_history log1)

noextract
[@@pulse_unfold]
let calc_server_network_pre
  (srv:server_state)
  (args:calc_network_args)
  : slprop =
  let log0 = calc_network_args_state args in
  let tcp0 = calc_network_args_tcp args in
  calc_server_invariant srv log0 tcp0 **
  calc_server_network_frame srv args **
  pure (CPI.protocol_state_transport
    CalcP.calc_protocol
    calc_tcp_history_matches
    tcp0
    log0)

noextract
[@@pulse_unfold]
let calc_server_network_post
  (srv:server_state)
  (args:calc_network_args)
  (result:calc_network_result)
  : slprop =
  let log0 = calc_network_args_state args in
  let tcp0 = calc_network_args_tcp args in
  exists* (log1: Ghost.erased calc_log) (tcp1: Ghost.erased TCP.history).
    calc_server_invariant srv (Ghost.reveal log1) (Ghost.reveal tcp1) **
    calc_server_network_extra_post
      srv
      args
      result
      (Ghost.reveal log1)
      (Ghost.reveal tcp1) **
    pure (
      CPI.protocol_network_step
        CalcP.calc_protocol
        calc_tcp_history_matches
        log0
        tcp0
        (Ghost.reveal log1)
        (Ghost.reveal tcp1) /\
      calc_network_effect
        args
        result
        log0
        tcp0
        (Ghost.reveal log1)
        (Ghost.reveal tcp1)
    )

noextract
[@@pulse_unfold]
let calc_server_local_frame
  (_srv:server_state)
  (_args:calc_local_args)
  : slprop =
  emp

let calc_local_effect
  (args:calc_local_args)
  (_result:calc_local_result)
  (log0:calc_log)
  (tcp0:TCP.history)
  (log1:calc_log)
  (tcp1:TCP.history)
  : GTot prop =
  CalcP.calc_step log0 CalcP.CalcLocalNoop log1 [] /\
  TCP.history_equal tcp0 tcp1

noextract
[@@pulse_unfold]
let calc_server_local_pre
  (srv:server_state)
  (args:calc_local_args)
  : slprop =
  let log0 = calc_local_args_state args in
  let tcp0 = calc_local_args_tcp args in
  calc_server_invariant
    srv
    log0
    tcp0 **
  calc_server_local_frame srv args **
  pure (CPI.protocol_state_transport
    CalcP.calc_protocol
    calc_tcp_history_matches
    tcp0
    log0)

noextract
[@@pulse_unfold]
let calc_server_local_extra_post
  (_srv:server_state)
  (_args:calc_local_args)
  (_result:calc_local_result)
  (_log1:calc_log)
  (_tcp1:TCP.history)
  : slprop =
  emp

noextract
[@@pulse_unfold]
let calc_server_local_post
  (srv:server_state)
  (args:calc_local_args)
  (result:calc_local_result)
  : slprop =
  let log0 = calc_local_args_state args in
  let tcp0 = calc_local_args_tcp args in
  exists* (log1: Ghost.erased calc_log) (tcp1: Ghost.erased TCP.history).
    calc_server_invariant srv (Ghost.reveal log1) (Ghost.reveal tcp1) **
    calc_server_local_extra_post
      srv
      args
      result
      (Ghost.reveal log1)
      (Ghost.reveal tcp1) **
    pure (
      CPI.protocol_local_step
        CalcP.calc_protocol
        calc_tcp_history_matches
        log0
        tcp0
        (Ghost.reveal log1)
        (Ghost.reveal tcp1) /\
      calc_local_effect
        args
        result
        log0
        tcp0
        (Ghost.reveal log1)
        (Ghost.reveal tcp1)
    )

fn calc_process_network
  (srv:server_state)
  (args:calc_network_args)
requires calc_server_network_pre srv args
returns r: calc_network_result
ensures calc_server_network_post srv args r
{
  unfold (calc_server_network_pre srv args);
  unfold (calc_server_invariant srv args.calc_network_log0 args.calc_network_tcp0);
  unfold (calc_server_tcp_channel srv args.calc_network_tcp0);
  unfold (calc_server_ghost_log srv args.calc_network_log0);
  unfold (calc_server_runtime_resources srv args.calc_network_log0 args.calc_network_tcp0);
  unfold (calc_server_network_frame srv args);
  with req_bytes0 resp_bytes0. _;
  Calc.Server.process_request srv args.calc_req_buf args.calc_resp_buf;
  with resp_bytes1 log1. _;
  CalcP.lemma_calc_state_valid_from_log_consistent log1;
  let log1e = Ghost.hide log1;
  let tcp1 = Ghost.hide (CalcP.calc_processed_history log1);
  assert (pure (TCP.history_equal (Ghost.reveal tcp1) (CalcP.calc_processed_history log1)));
  assert (pure (CPI.protocol_state_transport
    CalcP.calc_protocol
    calc_tcp_history_matches
    (Ghost.reveal tcp1)
    (Ghost.reveal log1e)));
  fold (calc_server_tcp_channel srv (Ghost.reveal tcp1));
  fold (calc_server_ghost_log srv (Ghost.reveal log1e));
  fold (calc_server_runtime_resources srv (Ghost.reveal log1e) (Ghost.reveal tcp1));
  fold (calc_server_invariant srv (Ghost.reveal log1e) (Ghost.reveal tcp1));
  assert (pure (TCP.history_equal
    args.calc_network_tcp0
    (CalcP.calc_processed_history args.calc_network_log0)));
  assert (pure (calc_network_effect
    args
    CalcNetworkProcessed
    args.calc_network_log0
    args.calc_network_tcp0
    (Ghost.reveal log1e)
    (Ghost.reveal tcp1)));
  with resp_bytes1 req_bytes0. fold (calc_server_network_extra_post
    srv
    args
    CalcNetworkProcessed
    (Ghost.reveal log1e)
    (Ghost.reveal tcp1));
  assert (pure (CPI.protocol_network_step
    CalcP.calc_protocol
    calc_tcp_history_matches
    args.calc_network_log0
    args.calc_network_tcp0
    (Ghost.reveal log1e)
    (Ghost.reveal tcp1)));
  with log1e tcp1.
  fold (calc_server_network_post srv args CalcNetworkProcessed);
  CalcNetworkProcessed
}

fn calc_process_local
  (srv:server_state)
  (args:calc_local_args)
requires calc_server_local_pre srv args
returns r: calc_local_result
ensures calc_server_local_post srv args r
{
  unfold (calc_server_local_pre srv args);
  unfold (calc_server_local_frame srv args);
  fold (calc_server_local_frame srv args);
  let log1 = args.calc_local_log0;
  let tcp1 = args.calc_local_tcp0;
  assert (pure (calc_local_effect
    args
    CalcLocalProcessed
    args.calc_local_log0
    args.calc_local_tcp0
    (Ghost.reveal log1)
    (Ghost.reveal tcp1)));
  assert (pure (CPI.protocol_local_step
    CalcP.calc_protocol
    calc_tcp_history_matches
    args.calc_local_log0
    args.calc_local_tcp0
    (Ghost.reveal log1)
    (Ghost.reveal tcp1)));
  fold (calc_server_local_extra_post
    srv
    args
    CalcLocalProcessed
    (Ghost.reveal log1)
    (Ghost.reveal tcp1));
  with log1 tcp1.
  fold (calc_server_local_post srv args CalcLocalProcessed);
  CalcLocalProcessed
}

noextract
let calc_server_protocol_implementation
  : CPI.protocol_implementation
      server_state
      calc_log
      CalcP.calc_wire_message
      CalcP.calc_event
      calc_network_args
      calc_network_result
      calc_local_args
      calc_local_result
  =
  {
    CPI.pi_protocol = CalcP.calc_protocol;
    CPI.pi_parse_network = calc_parse_network;
    CPI.pi_serialize_network = calc_serialize_network;
    CPI.pi_serialized_network = calc_serialized_network;
    CPI.pi_parse_network_correct = lemma_calc_parse_network_correct;
    CPI.pi_serialize_network_correct = lemma_calc_serialize_network_correct;
    CPI.pi_tcp_channel = calc_server_tcp_channel;
    CPI.pi_ghost_log = calc_server_ghost_log;
    CPI.pi_runtime_resources = calc_server_runtime_resources;
    CPI.pi_invariant = calc_server_invariant;
    CPI.pi_tcp_history_matches = calc_tcp_history_matches;
    CPI.pi_network_args_state = calc_network_args_state;
    CPI.pi_network_args_tcp = calc_network_args_tcp;
    CPI.pi_local_args_state = calc_local_args_state;
    CPI.pi_local_args_tcp = calc_local_args_tcp;
    CPI.pi_network_frame = calc_server_network_frame;
    CPI.pi_network_extra_post = calc_server_network_extra_post;
    CPI.pi_network_effect = calc_network_effect;
    CPI.pi_local_frame = calc_server_local_frame;
    CPI.pi_local_extra_post = calc_server_local_extra_post;
    CPI.pi_local_effect = calc_local_effect;
    CPI.pi_process_network = calc_process_network;
    CPI.pi_process_local = calc_process_local;
  }
