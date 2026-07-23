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
