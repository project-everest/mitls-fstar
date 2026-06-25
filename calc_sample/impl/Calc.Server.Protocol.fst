module Calc.Server.Protocol

#lang-pulse

open Pulse.Lib.Pervasives

module CP = Common.Protocol
module CPI = Common.ProtocolImplementation
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

noextract
[@@pulse_unfold]
let calc_server_network_pre
  (srv:server_state)
  (args:calc_network_args)
  : slprop =
  let log0 = Ghost.reveal args.calc_network_log0 in
  let tcp0 = Ghost.reveal args.calc_network_tcp0 in
  calc_server_invariant srv log0 tcp0 **
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
let calc_server_network_post
  (srv:server_state)
  (args:calc_network_args)
  (_result:calc_network_result)
  : slprop =
  let log0 = Ghost.reveal args.calc_network_log0 in
  let tcp0 = Ghost.reveal args.calc_network_tcp0 in
  exists* (resp_bytes1: bytes) (log1: calc_log).
    calc_server_invariant srv log1 (CalcP.calc_processed_history log1) **
    exists* (req_bytes: Ghost.erased bytes).
    Vec.pts_to args.calc_req_buf req_bytes **
    Vec.pts_to args.calc_resp_buf resp_bytes1 **
    pure (
      log_single_step log0 log1 /\
      log1.input_bytes `Seq.equal` Seq.append log0.input_bytes (Ghost.reveal req_bytes) /\
      log1.output_bytes `Seq.equal` Seq.append log0.output_bytes resp_bytes1 /\
      TCP.history_equal tcp0 (CalcP.calc_processed_history log0)
    )

noextract
[@@pulse_unfold]
let calc_server_local_pre
  (srv:server_state)
  (args:calc_local_args)
  : slprop =
  calc_server_invariant
    srv
    (Ghost.reveal args.calc_local_log0)
    (Ghost.reveal args.calc_local_tcp0)

noextract
[@@pulse_unfold]
let calc_server_local_post
  (srv:server_state)
  (args:calc_local_args)
  (_result:calc_local_result)
  : slprop =
  let log0 = Ghost.reveal args.calc_local_log0 in
  let tcp0 = Ghost.reveal args.calc_local_tcp0 in
  calc_server_invariant srv log0 tcp0 **
  pure (CalcP.calc_step log0 CalcP.CalcLocalNoop log0 [])

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
  Calc.Server.process_request srv args.calc_req_buf args.calc_resp_buf;
  with resp_bytes1 log1. _;
  CalcP.lemma_calc_state_valid_from_log_consistent log1;
  fold (calc_server_tcp_channel srv (CalcP.calc_processed_history log1));
  fold (calc_server_ghost_log srv log1);
  fold (calc_server_runtime_resources srv log1 (CalcP.calc_processed_history log1));
  fold (calc_server_invariant srv log1 (CalcP.calc_processed_history log1));
  assert (pure (TCP.history_equal
    args.calc_network_tcp0
    (CalcP.calc_processed_history args.calc_network_log0)));
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
  fold (calc_server_local_post srv args CalcLocalProcessed);
  CalcLocalProcessed
}

let calc_network_signature
  (srv:server_state)
  (args:calc_network_args)
  : GTot Type0 =
  stt calc_network_result
    (calc_server_network_pre srv args)
    (calc_server_network_post srv args)

let calc_local_signature
  (srv:server_state)
  (args:calc_local_args)
  : GTot Type0 =
  stt calc_local_result
    (calc_server_local_pre srv args)
    (calc_server_local_post srv args)

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
    CPI.pi_invariant_correct = calc_server_invariant_correct;
    CPI.pi_network_pre = calc_server_network_pre;
    CPI.pi_network_post = calc_server_network_post;
    CPI.pi_local_pre = calc_server_local_pre;
    CPI.pi_local_post = calc_server_local_post;
    CPI.pi_network_signature = calc_network_signature;
    CPI.pi_local_signature = calc_local_signature;
  }
