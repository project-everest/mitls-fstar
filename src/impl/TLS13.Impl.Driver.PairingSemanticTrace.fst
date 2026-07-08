module TLS13.Impl.Driver.PairingSemanticTrace

#lang-pulse

open Pulse.Lib.Pervasives

module C = TLS13.Crypto.Spec
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module Pairing = TLS13.Impl.Driver.Pairing
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PNTPH = TLS13.Impl.Driver.PairingNoTailServerPostHelloShape
module PNTSS = TLS13.Impl.Driver.PairingNoTailServerShape
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module SD = TLS13.Impl.Server.Driver
module X = TLS13.X509.Spec

let lemma_paired_successful_no_tail_semantic_traces_paired_handshake_message_states
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_trace:list CS.conn_event)
  (server_trace:list CS.conn_event)
  : Lemma
      (requires
        paired_successful_no_tail_semantic_traces
          client
          server
          client_trace
          server_trace)
      (ensures Pairing.paired_handshake_message_states client server)
=
  eliminate exists
    (c_start:CS.handshake_start)
    (c_ch:M.client_hello)
    (c_sh:M.server_hello)
    (c_shared:C.x25519_shared_secret)
    (c_e4:CS.conn_event)
    (c_e5:CS.conn_event)
    (c_ee:M.encrypted_extensions)
    (c_cert:M.certificate_msg)
    (c_peer:X.peer_identity)
    (c_cv:M.certificate_verify)
    (c_sf:M.finished)
    (c_e13:CS.conn_event)
    (c_e14:CS.conn_event)
    (c_cf:M.finished).
    client_successful_no_tail_semantic_trace_state_inputs
      client
      client_trace
      c_start
      c_ch
      c_sh
      c_shared
      c_e4
      c_e5
      c_ee
      c_cert
      c_peer
      c_cv
      c_sf
      c_e13
      c_e14
      c_cf
  returns
    Pairing.paired_handshake_message_states client server
  with _.
  eliminate exists
    (s_ch:M.client_hello)
    (s_selection:CS.server_handshake_selection)
    (s_shared:C.x25519_shared_secret)
    (s_sh:M.server_hello)
    (s_e5:CS.conn_event)
    (s_e6:CS.conn_event)
    (s_ee:M.encrypted_extensions)
    (s_cert:M.certificate_msg)
    (s_cv:M.certificate_verify)
    (s_sf:M.finished)
    (s_app_write:CS.traffic_key_material)
    (s_cf:M.finished)
    (s_app_read:CS.traffic_key_material).
    server_successful_no_tail_semantic_trace_state_inputs
      server
      server_trace
      s_ch
      s_selection
      s_shared
      s_sh
      s_e5
      s_e6
      s_ee
      s_cert
      s_cv
      s_sf
      s_app_write
      s_cf
      s_app_read
  returns
    Pairing.paired_handshake_message_states client server
  with _.
  ( assert
      (CS.sent_tls_messages client_trace ==
        [
          M.TlsHandshake (M.ClientHello c_ch);
          M.TlsHandshake (M.Finished c_cf)
        ]);
    assert
      (CS.received_tls_messages server_trace ==
        [
          M.TlsHandshake (M.ClientHello s_ch);
          M.TlsHandshake (M.Finished s_cf)
        ]);
    assert
      (CS.sent_tls_messages client_trace ==
        CS.received_tls_messages server_trace);
    assert
      ([
        M.TlsHandshake (M.ClientHello c_ch);
        M.TlsHandshake (M.Finished c_cf)
       ] ==
       [
        M.TlsHandshake (M.ClientHello s_ch);
        M.TlsHandshake (M.Finished s_cf)
       ]);
    assert (c_ch == s_ch);
    assert (c_cf == s_cf);
    assert
      (CS.sent_tls_messages server_trace ==
        [
          M.TlsHandshake (M.ServerHello s_sh);
          M.TlsHandshake (M.EncryptedExtensions s_ee);
          M.TlsHandshake (M.Certificate s_cert);
          M.TlsHandshake (M.CertificateVerify s_cv);
          M.TlsHandshake (M.Finished s_sf)
        ]);
    assert
      (CS.received_tls_messages client_trace ==
        [
          M.TlsHandshake (M.ServerHello c_sh);
          M.TlsHandshake (M.EncryptedExtensions c_ee);
          M.TlsHandshake (M.Certificate c_cert);
          M.TlsHandshake (M.CertificateVerify c_cv);
          M.TlsHandshake (M.Finished c_sf)
        ]);
    assert
      (CS.sent_tls_messages server_trace ==
        CS.received_tls_messages client_trace);
    assert
      ([
        M.TlsHandshake (M.ServerHello s_sh);
        M.TlsHandshake (M.EncryptedExtensions s_ee);
        M.TlsHandshake (M.Certificate s_cert);
        M.TlsHandshake (M.CertificateVerify s_cv);
        M.TlsHandshake (M.Finished s_sf)
       ] ==
       [
        M.TlsHandshake (M.ServerHello c_sh);
        M.TlsHandshake (M.EncryptedExtensions c_ee);
        M.TlsHandshake (M.Certificate c_cert);
        M.TlsHandshake (M.CertificateVerify c_cv);
        M.TlsHandshake (M.Finished c_sf)
       ]);
    assert (s_sh == c_sh);
    assert (s_ee == c_ee);
    assert (s_cert == c_cert);
    assert (s_cv == c_cv);
    assert (s_sf == c_sf);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
        Some c_ch);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
        Some s_ch);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
        Some c_sh);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
        Some s_sh);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
        Some c_ee);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
        Some s_ee);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_certificate ==
        Some c_cert);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_certificate ==
        Some s_cert);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
        Some c_cv);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
        Some s_cv);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
        Some c_sf);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
        Some s_sf);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
        Some c_cf);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
        Some s_cf);
    assert (Pairing.paired_handshake_message_states client server) )

let lemma_client_server_application_record_material_agrees_from_paired_successful_no_tail_semantic_traces
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_trace:list CS.conn_event)
  (server_trace:list CS.conn_event)
  : Lemma
      (requires
        paired_successful_no_tail_semantic_traces
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
  lemma_paired_successful_no_tail_semantic_traces_paired_handshake_message_states
    client
    server
    client_trace
    server_trace;
  Pairing.lemma_client_server_application_record_material_agrees_from_paired_handshake_message_states
    client
    server
