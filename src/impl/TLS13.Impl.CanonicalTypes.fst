module TLS13.Impl.CanonicalTypes

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CPI = Common.ProtocolImplementation
module CT = TLS13.Impl.Client.Types
module ET = TLS13.Impl.Endpoint.Types
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT

(**
  Shared role-neutral vocabulary for the canonical Common.ProtocolImplementation
  adapters.

  Error/status detail is represented by [CPI.process_status].  Application bytes
  delivered through the endpoint [app_out] buffer are surfaced as tagged local
  outputs; richer driver/control APIs remain outside this first canonical
  boundary.
 **)

type local_output =
  | AppOut: bytes:B.bytes -> local_output

let local_output_bytes (out:local_output) : B.bytes =
  match out with
  | AppOut bytes -> bytes

let rec local_outputs_bytes (outs:list local_output) : Tot (list B.bytes)
  (decreases outs)
=
  match outs with
  | [] -> []
  | out :: rest -> local_output_bytes out :: local_outputs_bytes rest

let local_outputs_app_bytes (outs:list local_output) : B.bytes =
  CL.concat_bytes (local_outputs_bytes outs)

type client_api_event = {
  client_local_kind: CT.local_event_kind;
  client_local_payload: B.bytes;
}

type client_local_event =
  | ClientAPI: event:client_api_event -> client_local_event
  | ClientGhostStep: client_local_event

type server_api_event = {
  server_local_kind: ST.local_event_kind;
  server_local_payload: B.bytes;
}

type server_local_event =
  | ServerAPI: event:server_api_event -> server_local_event
  | ServerGhostStep: server_local_event

let endpoint_status_to_process_status
  (status:ET.endpoint_status)
  : CPI.process_status =
  match status with
  | ET.StepOk -> CPI.StepOk
  | ET.NeedMoreInput -> CPI.NeedMoreInput
  | ET.DecodeError -> CPI.DecodeError
  | ET.IllegalTransition -> CPI.IllegalTransition
  | ET.OutputBufferTooSmall -> CPI.OutputBufferTooSmall
  | ET.ConnectionFailed -> CPI.ConnectionFailed

let process_result_of_endpoint
  (consumed_len:SZ.t)
  (response:ET.endpoint_response)
  : CPI.process_result =
  {
    CPI.process_status =
      endpoint_status_to_process_status response.ET.status;
    CPI.process_consumed_len = consumed_len;
    CPI.process_produced_len = response.ET.network_out_len;
    CPI.process_app_len = response.ET.app_out_len;
  }

let client_process_result
  (response:CT.client_buffer_response)
  : CPI.process_result =
  process_result_of_endpoint response.CT.consumed_len response.CT.response

let client_local_process_result
  (response:CT.client_response)
  : CPI.process_result =
  process_result_of_endpoint 0sz response

let server_process_result
  (response:ST.server_buffer_response)
  : CPI.process_result =
  process_result_of_endpoint response.ST.consumed_len response.ST.response

let server_local_process_result
  (response:ST.server_response)
  : CPI.process_result =
  process_result_of_endpoint 0sz response

let app_out_written
  (response:ET.endpoint_response)
  (app_out:B.bytes)
  (app_bytes:B.bytes)
  : prop =
  SZ.v response.ET.app_out_len == B.length app_bytes /\
  SZ.v response.ET.app_out_len <= B.length app_out /\
  Seq.equal
    (Seq.slice app_out 0 (SZ.v response.ET.app_out_len))
    app_bytes
