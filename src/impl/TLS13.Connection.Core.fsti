module TLS13.Connection.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module Seq = FStar.Seq
module S = TLS13.StateMachine
module SZ = FStar.SizeT
module U8 = FStar.UInt8

(**
  Buffer-oriented proof boundary for the application-data phase.

  This module is intentionally scoped to application write/read/close requests.
  Handshake start/connect is not part of this first core API, because the current
  connection implementation still treats the handshake transcript as an external
  TCB milestone.

  The implementation establishes the calc-style theorem shape over concrete
  buffers and CL.step witnesses. Application writes use the record/framing code
  to emit one TLS record into network_out. KReadApplicationData currently models
  an empty input poll that returns NeedNetworkInput, and multi-record
  fragmentation remains a later milestone.
**)

val client_core : Type0

val is_client_core : client_core -> CL.connection_view -> slprop

fn client_core_new ()
  returns c: client_core
  ensures is_client_core c CL.empty_connection_view

fn client_core_free (c: client_core)
  requires is_client_core c 'view
  ensures emp

fn client_core_install_application_keys_runtime
  (c: client_core)
  (key: array U8.t)
  (iv: array U8.t)
  requires is_client_core c 'view **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pure (B.length 'key_bytes == 32 /\ B.length 'iv_bytes == 12)
  ensures is_client_core c 'view **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes

type request_kind =
  | KSendApplicationData
  | KReadApplicationData
  | KClose

type core_result = {
  network_out_len: SZ.t;
  app_out_len: SZ.t;
  status: CL.client_status;
}

let buffer_prefix_matches (buffer:B.bytes) (len:nat) (bytes:B.bytes) : prop =
  len <= B.length buffer /\
  B.length bytes == len /\
  Seq.equal bytes (Seq.slice buffer 0 len)

let request_buffers_match
  (kind:request_kind)
  (network_in:B.bytes)
  (app_in:B.bytes)
  (requested_app_len:nat)
  (req:CL.client_request)
  : prop =
  match kind with
  | KSendApplicationData ->
    Seq.equal network_in B.empty /\
    req == CL.request_no_network_in (CL.OpSendApplicationData app_in)
  | KReadApplicationData ->
    Seq.equal network_in B.empty /\
    Seq.equal app_in B.empty /\
    req == CL.request_with_network_in (CL.OpReadApplicationData requested_app_len) network_in
  | KClose ->
    Seq.equal network_in B.empty /\
    Seq.equal app_in B.empty /\
    requested_app_len == 0 /\
    req == CL.request_no_network_in CL.OpClose

let response_buffers_match
  (result:core_result)
  (network_out_buffer:B.bytes)
  (app_out_buffer:B.bytes)
  (resp:CL.client_response)
  : prop =
  SZ.v result.network_out_len <= B.length network_out_buffer /\
  SZ.v result.app_out_len <= B.length app_out_buffer /\
  result.status == resp.CL.status /\
  CL.response_shape resp /\
  buffer_prefix_matches network_out_buffer (SZ.v result.network_out_len) resp.CL.network_out /\
  buffer_prefix_matches app_out_buffer (SZ.v result.app_out_len) resp.CL.app_out

fn process_request
  (c: client_core)
  (kind: request_kind)
  (network_in: array U8.t)
  (network_in_len: SZ.t)
  (app_in: array U8.t)
  (app_in_len: SZ.t)
  (requested_app_len: SZ.t)
  (network_out: array U8.t)
  (network_out_cap: SZ.t)
  (app_out: array U8.t)
  (app_out_cap: SZ.t)
  (#view0: erased CL.connection_view)
  (#mreq: erased CL.client_request)
requires
  is_client_core c view0 **
  pts_to network_in 'network_in_bytes **
  pts_to app_in 'app_in_bytes **
  pts_to network_out 'network_out0 **
  pts_to app_out 'app_out0 **
  pure (
    B.length 'network_in_bytes == SZ.v network_in_len /\
    B.length 'app_in_bytes == SZ.v app_in_len /\
    B.length 'network_out0 == SZ.v network_out_cap /\
    B.length 'app_out0 == SZ.v app_out_cap /\
    view0.CL.state.S.phase == S.ApplicationData /\
    request_buffers_match
      kind
      (Ghost.reveal 'network_in_bytes)
      (Ghost.reveal 'app_in_bytes)
      (SZ.v requested_app_len)
      mreq)
returns result: core_result
ensures exists* view1 network_out1 app_out1.
  is_client_core c view1 **
  pts_to network_in 'network_in_bytes **
  pts_to app_in 'app_in_bytes **
  pts_to network_out network_out1 **
  pts_to app_out app_out1 **
  pure (
    B.length network_out1 == SZ.v network_out_cap /\
    B.length app_out1 == SZ.v app_out_cap /\
    (exists mresp.
      response_buffers_match result (Ghost.reveal network_out1) (Ghost.reveal app_out1) mresp /\
      CL.step view0 mreq view1 mresp))
