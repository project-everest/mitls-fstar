module TLS13.Impl.Driver.PairingValidByteTrace

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module ClientCP = TLS13.Impl.Client.CanonicalProtocol
module CS = TLS13.Spec.StateMachine
module EC = TLS13.Spec.Endpoint.Client
module ES = TLS13.Spec.Endpoint.Server
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module Seq = FStar.Seq
module ServerCP = TLS13.Impl.Server.CanonicalProtocol
module WFSM = Common.WireFormatStateMachine

let lemma_client_server_application_record_material_agrees_from_valid_paired_byte_traces_at_handshake_complete_boundary
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        paired_valid_byte_traces_at_handshake_complete_boundary
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
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
  PCB.lemma_client_server_application_record_material_agrees_from_clean_boundary
    client
    server
