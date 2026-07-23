module TLS13.Impl.Client.Driver.BufferedNetwork

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BS = Common.BufferedStream
module CT = TLS13.Impl.Client.Types
module DS = TLS13.Impl.Client.Driver.State
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn process_local_event
  (d:DS.top_buffered_driver)
  (kind:CT.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires
    DS.top_buffered_driver_exactly d 'st0 'buffered 'buffered_len **
    pts_to payload 'payload_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'payload_bytes == SZ.v payload_len /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len /\
      CT.local_input_wf 'st0 kind (Ghost.reveal 'payload_bytes))
  returns result:DS.local_write_result
  ensures
    exists* st1 network_out_bytes app_out_bytes.
      DS.top_buffered_driver_exactly d st1 'buffered 'buffered_len **
      pts_to payload 'payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len /\
        CT.local_event_end_to_end_correct
          'st0
          st1
          result.DS.local_write_resp
          kind
          (Ghost.reveal 'payload_bytes)
          network_out_bytes
          app_out_bytes /\
        result.DS.local_write_written ==
          result.DS.local_write_resp.CT.network_out_len /\
        (result.DS.local_write_resp.CT.status == CT.StepOk ==>
          SZ.v result.DS.local_write_written <=
            SZ.v result.DS.local_write_resp.CT.network_out_len))

noextract
val public_drive_post:
  DS.top_buffered_driver ->
  network_out:array U8.t ->
  network_out_capacity:SZ.t ->
  app_out:array U8.t ->
  app_out_capacity:SZ.t ->
  initial_state:TLS13.Spec.StateMachine.connection_state ->
  initial_network_out:B.bytes ->
  initial_app_out:B.bytes ->
  BS.drive_outcome unit CT.client_status DS.buffered_network_result ->
  slprop

inline_for_extraction
fn drive_until_conclusive
  (d:DS.top_buffered_driver)
  (network_out:array U8.t)
  (network_out_capacity:SZ.t)
  (app_out:array U8.t)
  (app_out_capacity:SZ.t)
  (buffered_len:SZ.t)
  (fuel:SZ.t)
  requires
    DS.top_buffered_driver_exactly d 'st0 'buffered buffered_len **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'old_network_out == SZ.v network_out_capacity /\
      B.length 'old_app_out == SZ.v app_out_capacity /\
      TLS13.Impl.Messages.max_record_fragment_len <= SZ.v app_out_capacity)
  returns outcome:BS.drive_outcome unit CT.client_status DS.buffered_network_result
  ensures
    public_drive_post
      d
      network_out
      network_out_capacity
      app_out
      app_out_capacity
      'st0
      'old_network_out
      'old_app_out
      outcome **
    pure (SZ.v (BS.drive_fuel_left outcome) <= SZ.v fuel)

noeq type completed_drive = {
  completed_drive_outcome:
    BS.drive_outcome unit CT.client_status DS.buffered_network_result;
  completed_drive_pending_len: SZ.t;
}

inline_for_extraction
fn drive
  (d:DS.top_buffered_driver)
  (network_out:array U8.t)
  (network_out_capacity:SZ.t)
  (app_out:array U8.t)
  (app_out_capacity:SZ.t)
  (buffered_len:SZ.t)
  (fuel:SZ.t)
  requires
    DS.top_buffered_driver_exactly d 'st0 'buffered buffered_len **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'old_network_out == SZ.v network_out_capacity /\
      B.length 'old_app_out == SZ.v app_out_capacity /\
      TLS13.Impl.Messages.max_record_fragment_len <= SZ.v app_out_capacity)
  returns result:completed_drive
  ensures
    exists* st1 buffered_after network_out_bytes app_out_bytes.
      DS.top_buffered_driver_exactly
        d
        st1
        buffered_after
        result.completed_drive_pending_len **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length buffered_after == SZ.v result.completed_drive_pending_len /\
        B.length network_out_bytes == SZ.v network_out_capacity /\
        B.length app_out_bytes == SZ.v app_out_capacity /\
        st1.TLS13.Spec.StateMachine.cs_model.TLS13.Spec.StateMachine.model_config ==
          'st0.TLS13.Spec.StateMachine.cs_model.TLS13.Spec.StateMachine.model_config /\
        (TLS13.Impl.Client.Types.client_end_to_end_invariant 'st0 ==>
         TLS13.Impl.Client.Types.client_end_to_end_invariant st1))
