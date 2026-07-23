module TLS13.Impl.Server.Driver.BufferedNetwork

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BS = Common.BufferedStream
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module Seq = FStar.Seq
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module U8 = FStar.UInt8

noeq type network_read_result = {
  network_read_len: SZ.t;
  network_read_buffer_resp: ST.server_buffer_response;
  network_read_written: SZ.t;
  network_read_prefix: Ghost.erased B.bytes;
}

noeq type buffered_network_result = {
  buffered_network_read: network_read_result;
  buffered_network_new_len: SZ.t;
}

noeq type completed_drive = {
  completed_drive_outcome:
    BS.drive_outcome unit ST.server_status buffered_network_result;
  completed_drive_pending_len: SZ.t;
}

noextract
let completed_drive_correct
  (st0 st1:CS.connection_state)
  (old_network_out network_out old_app_out app_out:B.bytes)
  (result:completed_drive)
  : prop =
  match result.completed_drive_outcome with
  | BS.DriveExhausted ->
    st1 == st0 /\
    Seq.equal network_out old_network_out /\
    Seq.equal app_out old_app_out
  | BS.DriveYield network consumed _ _ ->
    let buffer_resp =
      network.buffered_network_read.network_read_buffer_resp in
    ST.server_network_bytes_end_to_end_correct
      st0
      st1
      buffer_resp
      (Ghost.reveal network.buffered_network_read.network_read_prefix)
      network_out
      app_out /\
    ST.server_network_consumed_input_projection
      st0
      st1
      buffer_resp
      (Ghost.reveal network.buffered_network_read.network_read_prefix)
      network_out
      app_out /\
    buffer_resp.ST.response.ST.status == ST.StepOk /\
    consumed == SZ.v buffer_resp.ST.consumed_len
  | BS.DriveReject network error _ ->
    let buffer_resp =
      network.buffered_network_read.network_read_buffer_resp in
    ST.server_network_bytes_end_to_end_correct
      st0
      st1
      buffer_resp
      (Ghost.reveal network.buffered_network_read.network_read_prefix)
      network_out
      app_out /\
    ST.server_network_consumed_input_projection
      st0
      st1
      buffer_resp
      (Ghost.reveal network.buffered_network_read.network_read_prefix)
      network_out
      app_out /\
    buffer_resp.ST.response.ST.status == error /\
    error <> ST.NeedMoreInput /\
    error <> ST.StepOk
  | BS.DriveProgress _ _ _
  | BS.DriveBufferFull _ _ ->
    False

inline_for_extraction
fn drive
  (d:DS.buffered_driver)
  (network_out:array U8.t)
  (network_out_capacity:SZ.t)
  (app_out:array U8.t)
  (app_out_capacity:SZ.t)
  (buffered_len:SZ.t)
  (fuel:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      buffered_len **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'old_network_out == SZ.v network_out_capacity /\
      B.length 'old_app_out == SZ.v app_out_capacity /\
      TLS13.Impl.Messages.max_record_fragment_len <= SZ.v app_out_capacity)
  returns result:completed_drive
  ensures
    exists* st1 buffered_after network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        buffered_after
        result.completed_drive_pending_len **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length buffered_after == SZ.v result.completed_drive_pending_len /\
        B.length network_out_bytes == SZ.v network_out_capacity /\
        B.length app_out_bytes == SZ.v app_out_capacity /\
        st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config /\
        ST.server_end_to_end_invariant st1 /\
        completed_drive_correct
          'st0
          st1
          'old_network_out
          network_out_bytes
          'old_app_out
          app_out_bytes
          result)
