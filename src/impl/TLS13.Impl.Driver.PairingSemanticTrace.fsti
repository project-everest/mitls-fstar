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

(**
  Semantic trace pairing, independent of record bytes.

  These traces are [CS.conn_event] logs.  The two equalities say that the TLS
  messages semantically sent by each endpoint are exactly the TLS messages
  semantically received by its peer, in order.  ChangeCipherSpec no-ops and
  local API events contribute no handshake messages unless they are represented
  as TLS network events in these projections.
**)
noextract
let paired_semantic_tls_io_traces
  (client_trace:list CS.conn_event)
  (server_trace:list CS.conn_event)
  : prop =
  CS.sent_tls_messages client_trace ==
    CS.received_tls_messages server_trace /\
  CS.sent_tls_messages server_trace ==
    CS.received_tls_messages client_trace

(**
  Client-side no-tail semantic inversion package.

  This predicate records the successful first-handshake client event shape and
  the corresponding final handshake slots.  It deliberately says nothing about
  raw records or parser/serializer injectivity.
**)
noextract
let client_successful_no_tail_semantic_trace_state_inputs
  (client:CS.connection_state)
  (client_trace:list CS.conn_event)
  (start:CS.handshake_start)
  (ch:M.client_hello)
  (sh:M.server_hello)
  (client_shared:C.x25519_shared_secret)
  (e4:CS.conn_event)
  (e5:CS.conn_event)
  (ee:M.encrypted_extensions)
  (cert:M.certificate_msg)
  (peer:X.peer_identity)
  (cv:M.certificate_verify)
  (sf:M.finished)
  (e13:CS.conn_event)
  (e14:CS.conn_event)
  (cf:M.finished)
  : prop =
  client.CS.cs_event_log == client_trace /\
  client_trace ==
    [
      CS.ConnLocalEvent (CS.LocalStartHandshake start);
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      };
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      };
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared);
      e4;
      e5;
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      };
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Certificate cert);
      };
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      };
      CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Finished sf);
      };
      CS.ConnLocalEvent (CS.LocalVerifyFinished sf);
      e13;
      e14;
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      }
    ] /\
  PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
  PNTCAS.client_no_tail_application_install_cover e13 e14 /\
  CS.sent_tls_messages client_trace ==
    [
      M.TlsHandshake (M.ClientHello ch);
      M.TlsHandshake (M.Finished cf)
    ] /\
  CS.received_tls_messages client_trace ==
    [
      M.TlsHandshake (M.ServerHello sh);
      M.TlsHandshake (M.EncryptedExtensions ee);
      M.TlsHandshake (M.Certificate cert);
      M.TlsHandshake (M.CertificateVerify cv);
      M.TlsHandshake (M.Finished sf)
    ] /\
  client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch /\
  client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh /\
  client.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == Some ee /\
  client.CS.cs_model.CS.model_handshake.CS.hs_certificate == Some cert /\
  client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
  client.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some sf /\
  client.CS.cs_model.CS.model_handshake.CS.hs_client_finished == Some cf

noextract
let client_successful_no_tail_semantic_trace_state
  (client:CS.connection_state)
  (client_trace:list CS.conn_event)
  : prop =
  exists
    (start:CS.handshake_start)
    (ch:M.client_hello)
    (sh:M.server_hello)
    (client_shared:C.x25519_shared_secret)
    (e4:CS.conn_event)
    (e5:CS.conn_event)
    (ee:M.encrypted_extensions)
    (cert:M.certificate_msg)
    (peer:X.peer_identity)
    (cv:M.certificate_verify)
    (sf:M.finished)
    (e13:CS.conn_event)
    (e14:CS.conn_event)
    (cf:M.finished).
    client_successful_no_tail_semantic_trace_state_inputs
      client
      client_trace
      start
      ch
      sh
      client_shared
      e4
      e5
      ee
      cert
      peer
      cv
      sf
      e13
      e14
      cf


val lemma_client_successful_no_tail_semantic_trace_state_from_boundary
  (client:CS.connection_state)
  (client_trace:list CS.conn_event)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16 /\
        client_trace == client.CS.cs_event_log)
      (ensures
        PNTCAS.client_no_tail_finished_sent_shape client /\
        client_successful_no_tail_semantic_trace_state client client_trace)

(**
  Server-side no-tail semantic inversion package.  The two handshake-traffic
  installs after ServerHello are intentionally order-insensitive; they are local
  state-machine steps and do not affect the semantic TLS I/O projection.
**)
noextract
let server_successful_no_tail_semantic_trace_state_inputs
  (server:CS.connection_state)
  (server_trace:list CS.conn_event)
  (ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (sh:M.server_hello)
  (e5:CS.conn_event)
  (e6:CS.conn_event)
  (ee:M.encrypted_extensions)
  (cert:M.certificate_msg)
  (cv:M.certificate_verify)
  (sf:M.finished)
  (server_app_write_material:CS.traffic_key_material)
  (cf:M.finished)
  (server_app_read_material:CS.traffic_key_material)
  : prop =
  server.CS.cs_event_log == server_trace /\
  server_trace ==
    FStar.List.Tot.append
      (PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh)
      [
        e5;
        e6;
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
        };
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Certificate cert);
        };
        CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        };
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Finished sf);
        };
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = server_app_write_material;
            };
          });
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Finished cf);
        };
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
      ] /\
  PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
  CS.sent_tls_messages server_trace ==
    [
      M.TlsHandshake (M.ServerHello sh);
      M.TlsHandshake (M.EncryptedExtensions ee);
      M.TlsHandshake (M.Certificate cert);
      M.TlsHandshake (M.CertificateVerify cv);
      M.TlsHandshake (M.Finished sf)
    ] /\
  CS.received_tls_messages server_trace ==
    [
      M.TlsHandshake (M.ClientHello ch);
      M.TlsHandshake (M.Finished cf)
    ] /\
  server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch /\
  server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh /\
  server.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == Some ee /\
  server.CS.cs_model.CS.model_handshake.CS.hs_certificate == Some cert /\
  server.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
  server.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some sf /\
  server.CS.cs_model.CS.model_handshake.CS.hs_client_finished == Some cf

noextract
let server_successful_no_tail_semantic_trace_state
  (server:CS.connection_state)
  (server_trace:list CS.conn_event)
  : prop =
  exists
    (ch:M.client_hello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:M.server_hello)
    (e5:CS.conn_event)
    (e6:CS.conn_event)
    (ee:M.encrypted_extensions)
    (cert:M.certificate_msg)
    (cv:M.certificate_verify)
    (sf:M.finished)
    (server_app_write_material:CS.traffic_key_material)
    (cf:M.finished)
    (server_app_read_material:CS.traffic_key_material).
    server_successful_no_tail_semantic_trace_state_inputs
      server
      server_trace
      ch
      selection
      server_shared
      sh
      e5
      e6
      ee
      cert
      cv
      sf
      server_app_write_material
      cf
      server_app_read_material

val lemma_server_successful_no_tail_semantic_trace_state_from_no_ccs_boundary
  (server:CS.connection_state)
  (server_trace:list CS.conn_event)
  : Lemma
      (requires
        PNTPH.server_no_tail_no_ccs_application_ready_boundary server /\
        server_trace == server.CS.cs_event_log)
      (ensures
        PNTPH.server_no_tail_post_two_handshake_installs_tail_order server /\
        server_successful_no_tail_semantic_trace_state server server_trace)

noextract
let paired_successful_no_tail_semantic_traces
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_trace:list CS.conn_event)
  (server_trace:list CS.conn_event)
  : prop =
  paired_semantic_tls_io_traces client_trace server_trace /\
  CD.client_driver_application_ready client /\
  SD.server_driver_application_ready server /\
  Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
    client
    server /\
  PNTCAS.client_no_tail_finished_sent_shape client /\
  PNTPH.server_no_tail_post_two_handshake_installs_tail_order server /\
  client_successful_no_tail_semantic_trace_state client client_trace /\
  server_successful_no_tail_semantic_trace_state server server_trace

noextract
let paired_successful_no_tail_semantic_traces_no_ccs_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_trace:list CS.conn_event)
  (server_trace:list CS.conn_event)
  : prop =
  paired_semantic_tls_io_traces client_trace server_trace /\
  CD.client_driver_application_ready client /\
  FStar.List.Tot.length client.CS.cs_event_log == 16 /\
  client_trace == client.CS.cs_event_log /\
  PNTPH.server_no_tail_no_ccs_application_ready_boundary server /\
  server_trace == server.CS.cs_event_log /\
  Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
    client
    server

noextract
let paired_successful_no_tail_semantic_logs_no_ccs_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  paired_semantic_tls_io_traces
    client.CS.cs_event_log
    server.CS.cs_event_log /\
  CD.client_driver_application_ready client /\
  FStar.List.Tot.length client.CS.cs_event_log == 16 /\
  PNTPH.server_no_tail_no_ccs_application_ready_boundary server /\
  Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
    client
    server

val lemma_paired_successful_no_tail_semantic_traces_from_no_ccs_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_trace:list CS.conn_event)
  (server_trace:list CS.conn_event)
  : Lemma
      (requires
        paired_successful_no_tail_semantic_traces_no_ccs_boundary
          client
          server
          client_trace
          server_trace)
      (ensures
        paired_successful_no_tail_semantic_traces
          client
          server
          client_trace
          server_trace)

val lemma_paired_successful_no_tail_semantic_traces_paired_handshake_message_states
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

val lemma_client_server_application_record_material_agrees_from_paired_successful_no_tail_semantic_traces
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

val lemma_client_server_application_record_material_agrees_from_paired_successful_no_tail_semantic_logs_no_ccs_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        paired_successful_no_tail_semantic_logs_no_ccs_boundary
          client
          server)
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
