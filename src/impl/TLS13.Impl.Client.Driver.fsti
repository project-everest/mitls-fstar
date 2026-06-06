module TLS13.Impl.Client.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module A = Pulse.Lib.Array
module C = TLS13.Impl.Client
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.ConnectionState
module CT = TLS13.Impl.Client.Types
module IO = TLS13.IO
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

noeq type driver = {
  driver_client: C.client;
  driver_channel: IO.channel;
}

noextract
let driver_exactly
  (d:driver)
  (st:TLS13.Spec.ConnectionState.connection_state)
  : slprop =
  C.connection_exactly d.driver_client st **
  IO.is_channel d.driver_channel

type local_write_result = {
  local_write_resp: CT.client_response;
  local_write_written: SZ.t;
}

type network_write_result = {
  network_write_buffer_resp: CT.client_buffer_response;
  network_write_written: SZ.t;
}

noeq type network_read_result = {
  network_read_len: SZ.t;
  network_read_buffer_resp: CT.client_buffer_response;
  network_read_written: SZ.t;
  network_read_prefix: Ghost.erased B.bytes;
}

noeq type buffered_network_result = {
  buffered_network_read: network_read_result;
  buffered_network_new_len: SZ.t;
}

noeq type buffered_network_io_result = {
  buffered_network_io_read_len: SZ.t;
  buffered_network_io_buffered: buffered_network_result;
}

noeq type buffered_network_loop_result = {
  buffered_network_loop_last: buffered_network_result;
  buffered_network_loop_exhausted: bool;
}

type ready_local_action_result = {
  ready_local_action: CT.next_local_action;
  ready_local_processed: bool;
  ready_local_resp: CT.client_response;
  ready_local_written: SZ.t;
}

type driver_drain_result = {
  driver_drain_last: ready_local_action_result;
  driver_drain_exhausted: bool;
}

fn driver_connect
  (connect_host:array U8.t)
  (connect_host_len:SZ.t)
  (port:U16.t)
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to connect_host 'connect_host_bytes **
           pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'connect_host_bytes == SZ.v connect_host_len /\
                 B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_hostname_len /\
                 SZ.v trust_anchors_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_trust_anchors_len)
  returns result: option driver
  ensures pts_to connect_host 'connect_host_bytes **
          pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          (match result with
           | Some d ->
             driver_exactly
               d
               (CR.configured_initial_state
                 (Ghost.reveal 'server_name_bytes)
                 (Ghost.reveal 'trust_anchors_bytes)
                 validation_time_seconds) **
             pure (CT.client_state_correct
               (CR.configured_initial_state
                 (Ghost.reveal 'server_name_bytes)
                 (Ghost.reveal 'trust_anchors_bytes)
                 validation_time_seconds) /\
                   CT.client_end_to_end_invariant
                     (CR.configured_initial_state
                       (Ghost.reveal 'server_name_bytes)
                       (Ghost.reveal 'trust_anchors_bytes)
                       validation_time_seconds))
           | None ->
             emp)

fn driver_control_snapshot
  (d:driver)
  requires driver_exactly d 'st0
  returns snapshot:CR.control_snapshot
  ensures driver_exactly d 'st0 **
          pure (CR.control_snapshot_matches snapshot 'st0)

fn driver_copy_certificate_leaf_der
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 Bounds.max_handshake_flight_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          driver_exactly d 'st0 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der with
                 | Some leaf ->
                   SZ.v copied_len == B.length leaf /\
                   Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) leaf
                 | None -> False))

fn driver_copy_certificate_verify_input
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 Bounds.max_certificate_verify_input_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          driver_exactly d 'st0 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input with
                 | Some input ->
                   SZ.v copied_len == B.length input /\
                   Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) input
                 | None -> False))

fn driver_copy_certificate_verify_signature
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 L.max_signature_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)
  returns snapshot:CR.certificate_verify_signature_snapshot
  ensures exists* out_bytes.
          driver_exactly d 'st0 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v snapshot.CR.cv_signature_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                 | Some cv ->
                   L.signature_scheme_matches snapshot.CR.cv_signature_scheme cv.M.scheme /\
                   SZ.v snapshot.CR.cv_signature_len == B.length cv.M.signature /\
                   Seq.equal
                     (Seq.slice out_bytes 0 (SZ.v snapshot.CR.cv_signature_len))
                     cv.M.signature
                 | None -> False))

fn process_local_event_and_write_once
  (c:C.client)
  (ch:IO.channel)
  (kind:CT.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           IO.is_channel ch **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           C.connection_exactly c st1 **
           IO.is_channel ch **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                   'st0
                   st1
                   result.local_write_resp
                   kind
                   (Ghost.reveal 'payload_bytes)
                   network_out_bytes
                   app_out_bytes /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                  SZ.v result.local_write_written <=
                  SZ.v result.local_write_resp.CT.network_out_len) /\
                 (result.local_write_resp.CT.status == CT.StepOk \/
                  result.local_write_written == 0sz))

fn driver_process_local_event
  (d:driver)
  (kind:CT.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                  'st0
                  kind
                  (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                  'st0
                  st1
                  result.local_write_resp
                  kind
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                 SZ.v result.local_write_written <=
                 SZ.v result.local_write_resp.CT.network_out_len) /\
                 (result.local_write_resp.CT.status == CT.StepOk \/
                 result.local_write_written == 0sz))

fn receive_network_bytes_once
  (d:driver)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: network_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw 'raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.network_bytes_end_to_end_correct
                  'st0
                  st1
                  result.network_write_buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  (Ghost.reveal 'old_network_out)
                  network_out_bytes
                  (Ghost.reveal 'old_app_out)
                  app_out_bytes /\
                 (result.network_write_buffer_resp.CT.response.CT.status ==
                 CT.StepOk ==>
                 SZ.v result.network_write_written <=
                 SZ.v result.network_write_buffer_resp.CT.response.CT.network_out_len) /\
                 (result.network_write_buffer_resp.CT.response.CT.status ==
                 CT.StepOk \/
                 result.network_write_written == 0sz))

fn driver_receive_application_data_once
  (d:driver)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: network_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw 'raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.network_bytes_end_to_end_correct
                 'st0
                 st1
                 result.network_write_buffer_resp
                 (Ghost.reveal 'raw_bytes)
                 (Ghost.reveal 'old_network_out)
                 network_out_bytes
                 (Ghost.reveal 'old_app_out)
                 app_out_bytes /\
                 (result.network_write_buffer_resp.CT.response.CT.status ==
                 CT.StepOk ==>
                 SZ.v result.network_write_written <=
                 SZ.v result.network_write_buffer_resp.CT.response.CT.network_out_len) /\
                 (result.network_write_buffer_resp.CT.response.CT.status ==
                 CT.StepOk \/
                 result.network_write_written == 0sz))

fn driver_process_buffered_network_bytes_once
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: network_read_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes ==
                 SZ.v raw_capacity /\
                 B.length (Ghost.reveal result.network_read_prefix) ==
                 SZ.v result.network_read_len /\
                 result.network_read_len == buffered_len /\
                 SZ.v result.network_read_len <= SZ.v raw_capacity /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.network_bytes_end_to_end_correct
                 'st0
                 st1
                 result.network_read_buffer_resp
                 (Ghost.reveal result.network_read_prefix)
                 (Ghost.reveal 'old_network_out)
                 network_out_bytes
                 (Ghost.reveal 'old_app_out)
                 app_out_bytes /\
                 (result.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk ==>
                 SZ.v result.network_read_written <=
                 SZ.v result.network_read_buffer_resp.CT.response.CT.network_out_len) /\
                 (result.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk \/
                 result.network_read_written == 0sz))

fn driver_process_buffered_network_bytes_compact_once
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes ==
                  SZ.v raw_capacity /\
                 B.length (Ghost.reveal result.buffered_network_read.network_read_prefix) ==
                  SZ.v result.buffered_network_read.network_read_len /\
                 result.buffered_network_read.network_read_len == buffered_len /\
                 SZ.v result.buffered_network_new_len <= SZ.v buffered_len /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.network_bytes_end_to_end_correct
                 'st0
                 st1
                 result.buffered_network_read.network_read_buffer_resp
                 (Ghost.reveal result.buffered_network_read.network_read_prefix)
                 (Ghost.reveal 'old_network_out)
                 network_out_bytes
                 (Ghost.reveal 'old_app_out)
                 app_out_bytes /\
                 (result.buffered_network_read.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk ==>
                 SZ.v result.buffered_network_read.network_read_written <=
                 SZ.v result.buffered_network_read.network_read_buffer_resp.CT.response.CT.network_out_len) /\
                 (result.buffered_network_read.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk \/
                 result.buffered_network_read.network_read_written == 0sz))

fn driver_read_buffered_network_bytes_compact_once
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_io_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.buffered_network_io_read_len <=
                 SZ.v raw_capacity - SZ.v buffered_len /\
                 B.length
                 (Ghost.reveal
                   result.buffered_network_io_buffered.buffered_network_read.network_read_prefix) ==
                 SZ.v
                   result.buffered_network_io_buffered.buffered_network_read.network_read_len /\
                 SZ.v
                 result.buffered_network_io_buffered.buffered_network_read.network_read_len <=
                 SZ.v raw_capacity /\
                 SZ.v result.buffered_network_io_buffered.buffered_network_new_len <=
                 SZ.v result.buffered_network_io_buffered.buffered_network_read.network_read_len /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.network_bytes_end_to_end_correct
                 'st0
                 st1
                 result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
                 (Ghost.reveal
                   result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
                 (Ghost.reveal 'old_network_out)
                 network_out_bytes
                 (Ghost.reveal 'old_app_out)
                 app_out_bytes)

fn rec driver_process_buffered_network_records
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_loop_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.buffered_network_loop_last.buffered_network_new_len <=
                  SZ.v buffered_len /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len)

fn driver_read_network_bytes_once
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: network_read_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes ==
                  SZ.v raw_capacity /\
                 B.length (Ghost.reveal result.network_read_prefix) ==
                  SZ.v result.network_read_len /\
                 SZ.v result.network_read_len <= SZ.v raw_capacity /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.network_bytes_end_to_end_correct
                 'st0
                 st1
                 result.network_read_buffer_resp
                 (Ghost.reveal result.network_read_prefix)
                 (Ghost.reveal 'old_network_out)
                 network_out_bytes
                 (Ghost.reveal 'old_app_out)
                 app_out_bytes /\
                 (result.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk ==>
                 SZ.v result.network_read_written <=
                 SZ.v result.network_read_buffer_resp.CT.response.CT.network_out_len) /\
                 (result.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk \/
                 result.network_read_written == 0sz))

fn driver_read_application_data_once
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: network_read_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes ==
                  SZ.v raw_capacity /\
                 B.length (Ghost.reveal result.network_read_prefix) ==
                  SZ.v result.network_read_len /\
                 SZ.v result.network_read_len <= SZ.v raw_capacity /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.network_bytes_end_to_end_correct
                 'st0
                 st1
                 result.network_read_buffer_resp
                 (Ghost.reveal result.network_read_prefix)
                 (Ghost.reveal 'old_network_out)
                 network_out_bytes
                 (Ghost.reveal 'old_app_out)
                 app_out_bytes /\
                 (result.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk ==>
                 SZ.v result.network_read_written <=
                 SZ.v result.network_read_buffer_resp.CT.response.CT.network_out_len) /\
                 (result.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk \/
                 result.network_read_written == 0sz))

fn process_ready_internal_local_action_once
  (c:C.client)
  (ch:IO.channel)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           IO.is_channel ch **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: ready_local_action_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           C.connection_exactly c st1 **
           IO.is_channel ch **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 C.next_local_action_sound
                   'st0
                   network_out_len
                   certificate_public_key_len
                   server_finished_payload_len
                   result.ready_local_action /\
                 (result.ready_local_processed ==>
                  result.ready_local_action.CT.next_local_ready == true /\
                  CT.local_event_end_to_end_correct
                    'st0
                    st1
                    result.ready_local_resp
                    result.ready_local_action.CT.next_local_kind
                    (Ghost.reveal 'empty_payload_bytes)
                    network_out_bytes
                    app_out_bytes /\
                  (result.ready_local_resp.CT.status == CT.StepOk ==>
                   SZ.v result.ready_local_written <=
                   SZ.v result.ready_local_resp.CT.network_out_len) /\
                  (result.ready_local_resp.CT.status == CT.StepOk \/
                   result.ready_local_written == 0sz)) /\
                 (result.ready_local_processed \/
                  result.ready_local_written == 0sz))

fn driver_handshake_step
  (d:driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: ready_local_action_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 C.next_local_action_sound
                  'st0
                  network_out_len
                  certificate_public_key_len
                  server_finished_payload_len
                  result.ready_local_action /\
                 (result.ready_local_processed ==>
                 result.ready_local_action.CT.next_local_ready == true /\
                 CT.local_event_end_to_end_correct
                   'st0
                   st1
                   result.ready_local_resp
                   result.ready_local_action.CT.next_local_kind
                   (Ghost.reveal 'empty_payload_bytes)
                   network_out_bytes
                   app_out_bytes /\
                 (result.ready_local_resp.CT.status == CT.StepOk ==>
                  SZ.v result.ready_local_written <=
                  SZ.v result.ready_local_resp.CT.network_out_len) /\
                 (result.ready_local_resp.CT.status == CT.StepOk \/
                  result.ready_local_written == 0sz)) /\
                 (result.ready_local_processed \/
                 result.ready_local_written == 0sz))

fn rec driver_drain_local_actions
  (d:driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: driver_drain_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 (result.driver_drain_last.ready_local_processed \/
                 result.driver_drain_last.ready_local_written == 0sz) /\
                 (result.driver_drain_exhausted ==>
                 result.driver_drain_last.ready_local_processed == false /\
                 result.driver_drain_last.ready_local_written == 0sz))

fn send_application_data_once
  (c:C.client)
  (ch:IO.channel)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           IO.is_channel ch **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           C.connection_exactly c st1 **
           IO.is_channel ch **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                   'st0
                   st1
                   result.local_write_resp
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes)
                   network_out_bytes
                   app_out_bytes /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                  SZ.v result.local_write_written <=
                  SZ.v result.local_write_resp.CT.network_out_len) /\
                 (result.local_write_resp.CT.status == CT.StepOk \/
                  result.local_write_written == 0sz))

fn driver_send_application_data
  (d:driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                  'st0
                  CT.LocalSendApplicationData
                  (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                  'st0
                  st1
                  result.local_write_resp
                  CT.LocalSendApplicationData
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                 SZ.v result.local_write_written <=
                 SZ.v result.local_write_resp.CT.network_out_len) /\
                 (result.local_write_resp.CT.status == CT.StepOk \/
                 result.local_write_written == 0sz))

fn driver_send_close_notify
  (d:driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                  'st0
                  st1
                  result.local_write_resp
                  CT.LocalSendCloseNotify
                  (Ghost.reveal 'empty_payload_bytes)
                  network_out_bytes
                  app_out_bytes /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                 SZ.v result.local_write_written <=
                 SZ.v result.local_write_resp.CT.network_out_len) /\
                 (result.local_write_resp.CT.status == CT.StepOk \/
                 result.local_write_written == 0sz))

fn driver_close (d:driver)
  requires driver_exactly d 'st0
  ensures C.connection_exactly d.driver_client 'st0
