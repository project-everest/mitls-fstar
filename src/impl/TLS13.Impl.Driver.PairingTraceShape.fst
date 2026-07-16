module TLS13.Impl.Driver.PairingTraceShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module ClientCP = TLS13.Impl.Client.CanonicalProtocol
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module GEE   = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV   = TLS13.Wire.Generated.CertificateVerify
module GFin  = TLS13.Wire.Generated.Finished
module Pairing = TLS13.Impl.Driver.Pairing
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module ServerCP = TLS13.Impl.Server.CanonicalProtocol
module WFSM = Common.WireFormatStateMachine

let lemma_paired_successful_handshake_complete_event_log_shape_paired_handshake_event_trace
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_successful_handshake_complete_event_log_shape client server)
      (ensures Pairing.paired_handshake_event_trace client server)
=
  eliminate exists
    (ch:GCH.clientHello)
    (sh:GSH.serverHello)
    (ee:GEE.encryptedExtensions)
    (cert:GCert.certificate)
    (cv:GCV.certificateVerify)
    (sf:GFin.finished)
    (cf:GFin.finished)
    (start:CS.handshake_start)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (client_shared:C.x25519_shared_secret)
    (server_material:CS.traffic_key_material)
    (client_material:CS.traffic_key_material)
    (client_hs_write_material:CS.traffic_key_material)
    (server_auth_skip:CS.local_event)
    (client_auth_skip:CS.local_event)
    (client_verify_skip:CS.local_event)
    (client_app_write_material:CS.traffic_key_material)
    (client_app_read_material:CS.traffic_key_material)
    (server_app_write_material:CS.traffic_key_material)
    (server_app_read_material:CS.traffic_key_material).
    paired_successful_handshake_complete_event_log_shape_inputs
      client
      server
      ch
      sh
      ee
      cert
      cv
      sf
      cf
      start
      selection
      server_shared
      client_shared
      server_material
      client_material
      client_hs_write_material
      server_auth_skip
      client_auth_skip
      client_verify_skip
      client_app_write_material
      client_app_read_material
      server_app_write_material
      server_app_read_material
  returns
    Pairing.paired_handshake_event_trace client server
  with _.
  ( let server_suffix =
      PWL.server_protected_handshake_contiguous_replay_events
        server_material
        (M.EncryptedExtensions ee)
        (M.Certificate cert)
        server_auth_skip
        (M.CertificateVerify cv)
        (M.Finished sf)
        server_app_write_material
        (M.Finished cf)
        [
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = server_app_read_material;
              };
            });
          CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
        ] in
    let client_suffix =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = client_hs_write_material;
        }) ::
      PWL.client_protected_handshake_contiguous_replay_events
        client_material
        (M.EncryptedExtensions ee)
        (M.Certificate cert)
        client_auth_skip
        (M.CertificateVerify cv)
        client_verify_skip
        (M.Finished sf)
        sf
        client_app_write_material
        client_app_read_material
        (M.Finished cf)
        [] in
    let server_prefix =
      PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh in
    let client_prefix =
      PWSeg.client_cleartext_handshake_prefix_events
        start
        ch
        sh
        client_shared in
    let server_events = FStar.List.Tot.append server_prefix server_suffix in
    let client_events = FStar.List.Tot.append client_prefix client_suffix in
    assert (client.CS.cs_event_log == client_events);
    assert (server.CS.cs_event_log == server_events);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_certificate == Some cert);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_certificate == Some cert);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some sf);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some sf);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_client_finished == Some cf);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_client_finished == Some cf);
    assert
      (Pairing.event_trace_has_tls_message
        CL.Sent
        (M.TlsHandshake (M.ClientHello ch))
        client.CS.cs_event_log);
    assert
      (Pairing.event_trace_has_tls_message
        CL.Received
        (M.TlsHandshake (M.ClientHello ch))
        server.CS.cs_event_log);
    assert
      (Pairing.event_trace_has_tls_message
        CL.Received
        (M.TlsHandshake (M.ServerHello sh))
        client.CS.cs_event_log);
    assert
      (Pairing.event_trace_has_tls_message
        CL.Sent
        (M.TlsHandshake (M.ServerHello sh))
        server.CS.cs_event_log);
    assert
      (Pairing.event_trace_has_tls_message
        CL.Received
        (M.TlsHandshake (M.EncryptedExtensions ee))
        client.CS.cs_event_log);
    assert
      (Pairing.event_trace_has_tls_message
        CL.Sent
        (M.TlsHandshake (M.EncryptedExtensions ee))
        server.CS.cs_event_log);
    assert
      (Pairing.event_trace_has_tls_message
        CL.Received
        (M.TlsHandshake (M.Certificate cert))
        client.CS.cs_event_log);
    assert
      (Pairing.event_trace_has_tls_message
        CL.Sent
        (M.TlsHandshake (M.Certificate cert))
        server.CS.cs_event_log);
    assert
      (Pairing.event_trace_has_tls_message
        CL.Received
        (M.TlsHandshake (M.CertificateVerify cv))
        client.CS.cs_event_log);
    assert
      (Pairing.event_trace_has_tls_message
        CL.Sent
        (M.TlsHandshake (M.CertificateVerify cv))
        server.CS.cs_event_log);
    assert
      (Pairing.event_trace_has_tls_message
        CL.Received
        (M.TlsHandshake (M.Finished sf))
        client.CS.cs_event_log);
    assert
      (Pairing.event_trace_has_tls_message
        CL.Sent
        (M.TlsHandshake (M.Finished sf))
        server.CS.cs_event_log);
    assert
      (Pairing.event_trace_has_tls_message
        CL.Sent
        (M.TlsHandshake (M.Finished cf))
        client.CS.cs_event_log);
    assert
      (Pairing.event_trace_has_tls_message
        CL.Received
        (M.TlsHandshake (M.Finished cf))
        server.CS.cs_event_log);
    assert (Pairing.paired_handshake_event_trace client server) )

let lemma_client_server_application_record_material_agrees_from_successful_handshake_complete_semantic_state_trace
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_successful_handshake_complete_semantic_state_trace client server)
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
=
  lemma_paired_successful_handshake_complete_event_log_shape_paired_handshake_event_trace
    client
    server;
  Pairing.lemma_client_server_application_record_material_agrees_from_paired_handshake_event_trace
    client
    server

let lemma_client_server_application_record_material_agrees_from_successful_handshake_complete_state_trace
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_successful_handshake_complete_state_trace client server)
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
=
  lemma_client_server_application_record_material_agrees_from_successful_handshake_complete_semantic_state_trace
    client
    server

let lemma_client_server_application_record_material_agrees_from_paired_application_ready_semantic_traces
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_trace:list CS.conn_event)
  (server_trace:list CS.conn_event)
  : Lemma
      (requires
        paired_application_ready_semantic_traces_with_message_states
          client
          server
          client_trace
          server_trace)
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
=
  Pairing.lemma_client_server_application_record_material_agrees_from_paired_handshake_message_states
    client
    server

let lemma_client_server_application_record_material_agrees_from_valid_paired_byte_traces_with_successful_handshake_complete_state_trace
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
        paired_valid_byte_traces_with_successful_handshake_complete_state_trace
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
=
  lemma_client_server_application_record_material_agrees_from_successful_handshake_complete_state_trace
    client
    server
