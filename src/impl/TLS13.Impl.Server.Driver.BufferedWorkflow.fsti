module TLS13.Impl.Server.Driver.BufferedWorkflow

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CM = TLS13.Impl.ConnectionState.Model
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module SZ = FStar.SizeT
module U8 = FStar.UInt8

type handshake_status =
  | HandshakeOk
  | HandshakeExhausted
  | HandshakeStepFailed
  | HandshakeRandomFailed
  | HandshakeSelectionNotReady
  | HandshakeSentinelCollision

noeq type handshake_result = {
  handshake_status: handshake_status;
  handshake_pending_len: SZ.t;
}

fn run
  (d:DS.buffered_driver)
  (empty_payload:array U8.t)
  (material_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (buffered_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      buffered_len **
    pts_to empty_payload 'empty_payload_bytes **
    pts_to material_payload 'material_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'buffered == SZ.v buffered_len /\
      B.length 'empty_payload_bytes == 0 /\
      B.length 'material_bytes == SZ.v DS.driver_material_capacity /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len /\
      network_out_len == DS.driver_network_out_capacity /\
      app_out_len == DS.driver_app_out_capacity /\
      CM.can_start_server 'st0)
  returns result:handshake_result
  ensures
    exists* st1 buffered_after material_after network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        buffered_after
        result.handshake_pending_len **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to material_payload material_after **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length buffered_after == SZ.v result.handshake_pending_len /\
        B.length material_after == SZ.v DS.driver_material_capacity /\
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len /\
        (result.handshake_status == HandshakeOk ==>
         st1.CS.cs_model.CS.model_control == CS.ControlApplicationData))
