module TLS13.Impl.Driver.PairingNormalizedShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module ClientCP = TLS13.Impl.Client.CanonicalProtocol
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module Pairing = TLS13.Impl.Driver.Pairing
module PNT = TLS13.Impl.Driver.PairingNoTail
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module ServerCP = TLS13.Impl.Server.CanonicalProtocol
module WFSM = Common.WireFormatStateMachine
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

noextract
let paired_successful_handshake_normalized_replay_shape
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  exists
    (client_ch:GCH.clientHello)
    (server_ch:GCH.clientHello)
    (client_sh:GSH.serverHello)
    (server_sh:GSH.serverHello)
    (client_ch_raw:B.bytes)
    (server_ch_raw:B.bytes)
    (client_sh_raw:B.bytes)
    (server_sh_raw:B.bytes).
    CD.client_driver_application_ready client /\
    SD.server_driver_application_ready server /\
    client.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      Some client_ch /\
    server.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      Some server_ch /\
    client.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      Some client_sh /\
    server.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      Some server_sh /\
    WFL.supported_client_hello_wire_profile client_ch /\
    Seq.equal client_ch_raw server_ch_raw /\
    Seq.equal server_sh_raw client_sh_raw /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello client_ch))
      client_ch_raw /\
    CS.received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello server_ch))
      server_ch_raw /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello server_sh))
      server_sh_raw /\
    CS.received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello client_sh))
      client_sh_raw /\
    Pairing.paired_protected_handshake_event_projection_pair_witnesses
      client
      server /\
    Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
      client
      server

val lemma_client_server_application_record_material_agrees_from_normalized_replay_shape
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        paired_successful_handshake_normalized_replay_shape client server)
      (ensures
        WFL.paired_cleartext_hello_wire_equivalent client server /\
        WFL.paired_cleartext_hello_key_shares client server /\
        WFL.paired_protected_handshake_wire_equivalent client server /\
        Pairing.paired_handshake_events client server /\
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)

noextract
let paired_supported_no_tail_valid_byte_traces_with_normalized_replay_shape
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  WFSM.valid_byte_trace
    (ClientCP.client_system client_initial)
    client_received
    client
    client_sent
    Seq.empty /\
  WFSM.valid_byte_trace
    (ServerCP.server_system server_initial)
    server_received
    server
    server_sent
    Seq.empty /\
  Seq.equal client_sent server_received /\
  Seq.equal server_sent client_received /\
  PNT.paired_no_tail_application_ready_boundary client server /\
  paired_successful_handshake_normalized_replay_shape client server

val lemma_client_server_application_record_material_agrees_from_no_tail_valid_byte_traces_with_normalized_replay_shape
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        paired_supported_no_tail_valid_byte_traces_with_normalized_replay_shape
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
