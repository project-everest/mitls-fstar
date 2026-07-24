module TLS13.Impl.Server.Driver.BufferedLocal

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module DS = TLS13.Impl.Server.Driver.State
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module U8 = FStar.UInt8

type local_status =
  | LocalProcessed
  | LocalStepFailed
  | LocalNotReady
  | LocalUnsupported

noeq type drain_result = {
  drain_last: local_status;
  drain_exhausted: bool;
}

fn process_ready_empty_local_action_once
  (d:DS.buffered_driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len **
    pts_to empty_payload 'empty_payload_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'empty_payload_bytes == 0 /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len /\
      16645 <= SZ.v network_out_len)
  returns status:local_status
  ensures
    exists* st1 network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        'buffered
        'buffered_len **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len)

fn drain_ready_empty_local_actions
  (d:DS.buffered_driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len **
    pts_to empty_payload 'empty_payload_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'empty_payload_bytes == 0 /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len /\
      16645 <= SZ.v network_out_len)
  returns result:drain_result
  ensures
    exists* st1 network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        'buffered
        'buffered_len **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len)
