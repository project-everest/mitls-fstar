module TLS13.Impl.Driver.PairingNoTailClientFinishedReceiverReplay

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module GEE   = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV   = TLS13.Wire.Generated.CertificateVerify
module GFin  = TLS13.Wire.Generated.Finished
module PNTSFR = TLS13.Impl.Driver.PairingNoTailServerFlightReplay
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PNTSS = TLS13.Impl.Driver.PairingNoTailServerShape
module PWR = TLS13.ConnectionState.ProtectedWireReplay
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module Seq = FStar.Seq

#push-options "--split_queries always --z3rlimit 10"

let lemma_server_client_finished_received_decode_suffix_replay_slice_from_ordered_post_server_hello
  (server:CS.connection_state)
  : Lemma
      (requires PNTSFR.server_post_server_hello_ordered_received_decode_replay_slice server)
      (ensures server_client_finished_received_decode_suffix_replay_slice server)
=
  eliminate exists
    (ch:GCH.clientHello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:GSH.serverHello)
    (e5:CS.conn_event)
    (e6:CS.conn_event)
    (ee:GEE.encryptedExtensions)
    (cert:GCert.certificate)
    (cv:GCV.certificateVerify)
    (sf:GFin.finished)
    (cf:GFin.finished)
    (server_app_write_material:CS.traffic_key_material)
    (server_app_read_material:CS.traffic_key_material)
    (model5:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
    let ordered_rest =
      [
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
      ] in
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (e5 :: e6 :: ordered_rest) /\
    PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_received_decode_replay
      (CS.initial_model server.CS.cs_model.CS.model_config)
      (PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh)
      prefix_sent
      prefix_received
      model5 /\
    CS.conn_events_received_decode_replay
      model5
      (e5 :: e6 :: ordered_rest)
      suffix_sent
      suffix_received
      server.CS.cs_model
  returns server_client_finished_received_decode_suffix_replay_slice server
  with _.
  (
    let ordered_rest =
      [
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
      ] in
    let server_flight_prefix =
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
        }
      ] in
    let client_finished_suffix =
      [
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
      ] in
    assert (e5 :: e6 :: ordered_rest ==
      FStar.List.Tot.append server_flight_prefix client_finished_suffix);
    assert (server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (FStar.List.Tot.append server_flight_prefix client_finished_suffix));
    assert (CS.conn_events_received_decode_replay
      model5
      (FStar.List.Tot.append server_flight_prefix client_finished_suffix)
      suffix_sent
      suffix_received
      server.CS.cs_model);
    PWR.lemma_conn_events_received_decode_replay_append_split
      model5
      server_flight_prefix
      client_finished_suffix
      suffix_sent
      suffix_received
      server.CS.cs_model;
    assert (exists
      (after_server_flight:CS.connection_model)
      (server_flight_sent:B.bytes)
      (server_flight_received:B.bytes)
      (client_finished_sent:B.bytes)
      (client_finished_received:B.bytes).
      Seq.equal
        suffix_sent
        (B.append server_flight_sent client_finished_sent) /\
      Seq.equal
        suffix_received
        (B.append server_flight_received client_finished_received) /\
      CS.conn_events_received_decode_replay
        model5
        server_flight_prefix
        server_flight_sent
        server_flight_received
        after_server_flight /\
      CS.conn_events_received_decode_replay
        after_server_flight
        client_finished_suffix
        client_finished_sent
        client_finished_received
        server.CS.cs_model);
    assert (server_client_finished_received_decode_suffix_replay_slice server    )
  )

let lemma_clean16_no_tail_valid_byte_traces_server_client_finished_received_decode_suffix_replay_slice
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
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures server_client_finished_received_decode_suffix_replay_slice server)
=
  PNTSFR.lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_ordered_received_decode_replay_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_server_client_finished_received_decode_suffix_replay_slice_from_ordered_post_server_hello
    server
