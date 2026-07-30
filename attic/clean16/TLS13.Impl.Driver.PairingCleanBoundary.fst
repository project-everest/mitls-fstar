module TLS13.Impl.Driver.PairingCleanBoundary

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module Pairing = TLS13.Impl.Driver.Pairing
module PR = TLS13.Impl.Driver.PairingProtectedReplay
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module R = TLS13.Record.Spec
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

let lemma_client_server_application_record_material_agrees_from_clean_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_supported_handshake_complete_boundary client server)
      (ensures
        TLS13.Spec.StateMachine.KeyMaterial.supported_profile_client_server_key_material_agrees client server /\
        TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
          (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
          (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  eliminate exists
    (w:handshake_complete_boundary_witnesses).
    paired_supported_handshake_complete_boundary_inputs client server w
  returns
    TLS13.Spec.StateMachine.KeyMaterial.supported_profile_client_server_key_material_agrees client server /\
    TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
      (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ClientTraffic)
      client
      server /\
    TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
      (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ServerTraffic)
      client
      server
  with _.
  ( PR.lemma_client_server_application_record_material_agrees_from_cleartext_prefix_full_replays
      client
      server
      w.hcb_client_ch
      w.hcb_server_ch
      w.hcb_client_sh
      w.hcb_server_sh
      w.hcb_client_ch_raw
      w.hcb_server_ch_raw
      w.hcb_client_sh_raw
      w.hcb_server_sh_raw
      (CS.initial_model server.CS.cs_model.CS.model_config)
      (CS.initial_model client.CS.cs_model.CS.model_config)
      w.hcb_start
      w.hcb_selection
      w.hcb_server_shared
      w.hcb_client_shared
      w.hcb_server_model1
      w.hcb_server_model2
      w.hcb_server_model3
      w.hcb_server_model4
      w.hcb_server_model5
      w.hcb_client_model1
      w.hcb_client_model2
      w.hcb_client_model3
      w.hcb_client_model4
      w.hcb_server_after_install
      w.hcb_client_after_install
      w.hcb_server_after0
      w.hcb_client_after0
      w.hcb_server_after1
      w.hcb_client_after1
      w.hcb_server_after_auth_skip
      w.hcb_client_after_auth_skip
      w.hcb_server_after2
      w.hcb_client_after2
      w.hcb_client_after_verify_skip
      w.hcb_server_after3
      w.hcb_client_after3
      w.hcb_server_auth_skip
      w.hcb_client_auth_skip
      w.hcb_client_verify_skip
      w.hcb_server_material
      w.hcb_client_material
      w.hcb_sent_msg0
      w.hcb_received_msg0
      w.hcb_sent_msg1
      w.hcb_received_msg1
      w.hcb_sent_msg2
      w.hcb_received_msg2
      w.hcb_sent_msg3
      w.hcb_received_msg3
      w.hcb_verified_server_finished
      w.hcb_client_app_write_material
      w.hcb_client_app_read_material
      w.hcb_server_app_write_material
      w.hcb_sent_msg4
      w.hcb_received_msg4
      w.hcb_client_finished_rest
      w.hcb_server_finished_rest
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      client.CS.cs_wire_log.CL.raw_sent
      client.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model
      client.CS.cs_model
      w.hcb_cf_client_after_verify
      w.hcb_cf_client_after_app_write
      w.hcb_cf_client_after_app_read
      w.hcb_cf_server_after_app_write
      w.hcb_cf_client_after_finished
      w.hcb_cf_server_after_finished )
