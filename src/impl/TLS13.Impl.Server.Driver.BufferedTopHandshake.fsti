module TLS13.Impl.Server.Driver.BufferedTopHandshake

#lang-pulse

open Pulse.Lib.Pervasives

module BW = TLS13.Impl.Server.Driver.BufferedWorkflow
module CM = TLS13.Impl.ConnectionState.Model
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module SZ = FStar.SizeT

fn run_connected
  (d:DS.top_server_driver)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires
    DS.top_server_driver_connected
      d
      'st0
      'certificate_chain
      'credential_identity
      'received0
      'sent0 **
    pure (CM.can_start_server 'st0)
  returns status:BW.handshake_status
  ensures
    exists* st1 received1 sent1.
      DS.top_server_driver_connected
        d
        st1
        'certificate_chain
        'credential_identity
        received1
        sent1 **
      pure (
        status == BW.HandshakeOk ==>
        st1.CS.cs_model.CS.model_control == CS.ControlApplicationData)
