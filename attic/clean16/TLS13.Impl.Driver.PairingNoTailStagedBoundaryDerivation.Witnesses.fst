module TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Witnesses

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module SMCan = TLS13.Spec.StateMachine.Canonical
module SMCorr = TLS13.Spec.StateMachine.Correspondence
module SMIds = TLS13.Spec.StateMachine.KeyIdentifiers
module SMReplay = TLS13.Spec.StateMachine.Replay
module EC = TLS13.Spec.Endpoint.Client
module ES = TLS13.Spec.Endpoint.Server
module CD = TLS13.Impl.Client.Driver
module M = TLS13.Messages
module Sem   = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished
module Pairing = TLS13.Impl.Driver.Pairing
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PNB = TLS13.Impl.Driver.PairingNormalizedBoundary
module PNTCFRE = TLS13.Impl.Driver.PairingNoTailClientFinishedRawEquality
module PNTCFRR = TLS13.Impl.Driver.PairingNoTailClientFinishedReceiverReplay
module PNTCFR = TLS13.Impl.Driver.PairingNoTailClientFinishedReplay
module PNTCFS = TLS13.Impl.Driver.PairingNoTailClientFinishedStaged
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PNTPPD = TLS13.Impl.Driver.PairingNoTailProtectedProjectionDerivation
module PNTRB = TLS13.Impl.Driver.PairingNoTailRawBridge
module PNTSFR = TLS13.Impl.Driver.PairingNoTailServerFlightReplay
module PNTSFS = TLS13.Impl.Driver.PairingNoTailServerFlightStaged
module PNTPH = TLS13.Impl.Driver.PairingNoTailServerPostHelloShape
module PSNB = TLS13.Impl.Driver.PairingStagedNormalizedBoundary
module SD = TLS13.Impl.Server.Driver
module Tac = FStar.Tactics
module WFL = TLS13.Spec.WireFormatLemmas
module RA = TLS13.ConnectionState.ProtectedWireRecordAlignment
module PWL = TLS13.ConnectionState.ProtectedWireBase
module R = TLS13.Record.Spec
module T = TLS13.Types
module PWReplay = TLS13.ConnectionState.ProtectedWireReplay
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNTSS = TLS13.Impl.Driver.PairingNoTailServerShape
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module X = TLS13.X509.Spec
module K = TLS13.Keys
module W = TLS13.Wire.Spec
module L = FStar.List.Tot
module CSL = TLS13.ConnectionState.Lemmas
module WRD = TLS13.Wire.Spec.RevealDecode

module Foundation = TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Foundation
open TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Foundation
module Replay = TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Replay
open TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Replay
module ServerFlight = TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.ServerFlight
open TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.ServerFlight
module ClientFinished = TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.ClientFinished
open TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.ClientFinished


module WitnessPack = TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.WitnessPack

#push-options "--z3rlimit 10"

#push-options "--z3rlimit 10"
noextract
let lemma_installed_protected_projection_replay_witnesses_from_milestones_and_hello_key_shares
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        clean16_staged_boundary_derivation_milestones client server /\
        WFL.paired_cleartext_hello_key_shares client server)
      (ensures
        PNTPPD.installed_protected_projection_replay_witnesses client server)
=
    // ---- Bring the canonical + ClientFinished milestone slices into scope ----
    assert (PNTSFR.server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice server);
    assert (PNTSFR.client_post_derive_ordered_received_decode_replay_slice client);
    assert (PNTCFRR.server_client_finished_received_decode_suffix_replay_slice server);
    PNTCFR.lemma_client_finished_exact_suffix_sent_seal_replay_slice_from_staged_milestone
      client server;
    PNTCFR.lemma_client_finished_exact_suffix_sent_seal_head_step_slice_from_replay_slice
      client;
    PNTCFR.lemma_client_finished_canonical_sent_seal_replay_slice_from_head_step_slice
      client;
    assert (PNTCFR.client_finished_canonical_sent_seal_replay_slice client);
    eliminate exists
      (ch_s:GCH.clientHello)
      (selection_s:CS.server_handshake_selection)
      (server_shared_s:C.x25519_shared_secret)
      (sh_s:GSH.serverHello)
      (ee_s:GEE.encryptedExtensions)
      (cert_s:GCert.certificate)
      (cv_s:GCV.certificateVerify)
      (sf_s:GFin.finished)
      (cf_s:GFin.finished)
      (server_material_s:CS.traffic_key_material)
      (server_read_material_s:CS.traffic_key_material)
      (server_app_write_material_s:CS.traffic_key_material)
      (server_app_read_material_s:CS.traffic_key_material)
      (model5_s:CS.connection_model)
      (server_after_write_s:CS.connection_model)
      (server_after_read_s:CS.connection_model)
      (prefix_sent_s:B.bytes)
      (prefix_received_s:B.bytes)
      (suffix_sent_s:B.bytes)
      (suffix_received_s:B.bytes).
      (let server_write_install =
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = server_material_s;
            };
          }) in
      let server_read_install =
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = server_read_material_s;
            };
          }) in
      let ordered_rest =
        [
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_s);
          };
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Certificate cert_s);
          };
          CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_s);
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv_s);
          };
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished sf_s);
          };
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_app_write_material_s;
              };
            });
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Finished cf_s);
          };
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = server_app_read_material_s;
              };
            });
          CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_s)
        ] in
      PNTSFR.server_post_server_hello_ordered_sent_seal_replay_slice server /\
      Seq.equal
        server.CS.cs_wire_log.CL.raw_sent
        (B.append prefix_sent_s suffix_sent_s) /\
      Seq.equal
        server.CS.cs_wire_log.CL.raw_received
        (B.append prefix_received_s suffix_received_s) /\
      SMReplay.conn_events_sent_seal_replay
        (CS.initial_model server.CS.cs_model.CS.model_config)
        (PWSeg.server_cleartext_handshake_prefix_events
          ch_s
          selection_s
          server_shared_s
          sh_s)
        prefix_sent_s
        prefix_received_s
        model5_s /\
      CS.step_model model5_s server_write_install == Some server_after_write_s /\
      CS.step_model server_after_write_s server_read_install == Some server_after_read_s /\
      SMReplay.conn_events_sent_seal_replay
        model5_s
        (server_write_install :: server_read_install :: ordered_rest)
        suffix_sent_s
        suffix_received_s
        server.CS.cs_model)
    with
    (
      assert (PNTSFR.client_post_derive_ordered_received_decode_replay_slice client);
      eliminate exists
        (start_c:CS.handshake_start)
        (ch_c:GCH.clientHello)
        (sh_c:GSH.serverHello)
        (client_shared_c:C.x25519_shared_secret)
        (e4_c:CS.conn_event)
        (e5_c:CS.conn_event)
        (ee_c:GEE.encryptedExtensions)
        (cert_c:GCert.certificate)
        (peer_c:X.peer_identity)
        (cv_c:GCV.certificateVerify)
        (sf_c:GFin.finished)
        (e13_c:CS.conn_event)
        (e14_c:CS.conn_event)
        (cf_c:GFin.finished)
        (model4_c:CS.connection_model)
        (prefix_sent_c:B.bytes)
        (prefix_received_c:B.bytes)
        (suffix_sent_c:B.bytes)
        (suffix_received_c:B.bytes).
        (let ordered_rest =
          [
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Certificate cert_c);
            };
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c);
            };
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf_c);
            };
            CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
            e13_c;
            e14_c;
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished cf_c);
            }
          ] in
        client.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.client_cleartext_handshake_prefix_events
              start_c
              ch_c
              sh_c
              client_shared_c)
            (e4_c :: e5_c :: ordered_rest) /\
        PCPS.client_no_tail_two_handshake_install_cover e4_c e5_c /\
        PNTCAS.client_no_tail_application_install_cover e13_c e14_c /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_sent
          (B.append prefix_sent_c suffix_sent_c) /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_received
          (B.append prefix_received_c suffix_received_c) /\
        SMReplay.conn_events_received_decode_replay
          (CS.initial_model client.CS.cs_model.CS.model_config)
          (PWSeg.client_cleartext_handshake_prefix_events
            start_c
            ch_c
            sh_c
            client_shared_c)
          prefix_sent_c
          prefix_received_c
          model4_c /\
        SMReplay.conn_events_received_decode_replay
          model4_c
          (e4_c :: e5_c :: ordered_rest)
          suffix_sent_c
          suffix_received_c
          client.CS.cs_model)
      with
      (
        assert (PNTCFRR.server_client_finished_received_decode_suffix_replay_slice server);
        eliminate exists
          (ch_r:GCH.clientHello)
          (selection_r:CS.server_handshake_selection)
          (server_shared_r:C.x25519_shared_secret)
          (sh_r:GSH.serverHello)
          (e5_r:CS.conn_event)
          (e6_r:CS.conn_event)
          (ee_r:GEE.encryptedExtensions)
          (cert_r:GCert.certificate)
          (cv_r:GCV.certificateVerify)
          (sf_r:GFin.finished)
          (cf_r:GFin.finished)
          (server_app_write_material_r:CS.traffic_key_material)
          (server_app_read_material_r:CS.traffic_key_material)
          (model5_r:CS.connection_model)
          (after_server_flight_r:CS.connection_model)
          (prefix_sent_r:B.bytes)
          (prefix_received_r:B.bytes)
          (suffix_sent_r:B.bytes)
          (suffix_received_r:B.bytes)
          (server_flight_sent_r:B.bytes)
          (server_flight_received_r:B.bytes)
          (client_finished_sent_r:B.bytes)
          (client_finished_received_r:B.bytes).
          (let server_flight_prefix =
            [
              e5_r;
              e6_r;
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_r);
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Certificate cert_r);
              };
              CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_r);
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv_r);
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished sf_r);
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
                    CS.install_material = server_app_write_material_r;
                  };
                });
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished cf_r);
              };
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficRead;
                    CS.install_material = server_app_read_material_r;
                  };
                });
              CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_r)
            ] in
          server.CS.cs_event_log ==
            FStar.List.Tot.append
              (PWSeg.server_cleartext_handshake_prefix_events
                ch_r
                selection_r
                server_shared_r
                sh_r)
              (FStar.List.Tot.append server_flight_prefix client_finished_suffix) /\
          PNTSS.server_no_tail_two_handshake_install_cover e5_r e6_r /\
          Seq.equal
            server.CS.cs_wire_log.CL.raw_sent
            (B.append prefix_sent_r suffix_sent_r) /\
          Seq.equal
            server.CS.cs_wire_log.CL.raw_received
            (B.append prefix_received_r suffix_received_r) /\
          Seq.equal
            suffix_sent_r
            (B.append server_flight_sent_r client_finished_sent_r) /\
          Seq.equal
            suffix_received_r
            (B.append server_flight_received_r client_finished_received_r) /\
          SMReplay.conn_events_received_decode_replay
            (CS.initial_model server.CS.cs_model.CS.model_config)
            (PWSeg.server_cleartext_handshake_prefix_events
              ch_r
              selection_r
              server_shared_r
              sh_r)
            prefix_sent_r
            prefix_received_r
            model5_r /\
          SMReplay.conn_events_received_decode_replay
            model5_r
            server_flight_prefix
            server_flight_sent_r
            server_flight_received_r
            after_server_flight_r /\
          SMReplay.conn_events_received_decode_replay
            after_server_flight_r
            client_finished_suffix
            client_finished_sent_r
            client_finished_received_r
            server.CS.cs_model)
        with
        (
          assert (PNTCFR.client_finished_canonical_sent_seal_replay_slice client);
          eliminate exists
            (sf_f:GFin.finished)
            (cf_f:GFin.finished)
            (model12_f:CS.connection_model)
            (after_verify_f:CS.connection_model)
            (after_app_write_f:CS.connection_model)
            (after_app_read_f:CS.connection_model)
            (client_app_write_material_f:CS.traffic_key_material)
            (client_app_read_material_f:CS.traffic_key_material)
            (suffix_sent_f:B.bytes)
            (suffix_received_f:B.bytes).
            (SMReplay.conn_events_sent_seal_replay
              model12_f
              (CS.ConnLocalEvent (CS.LocalVerifyFinished sf_f) ::
               CS.ConnLocalEvent
                 (CS.LocalInstallTrafficKeys {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = client_app_write_material_f;
                 }) ::
               CS.ConnLocalEvent
                 (CS.LocalInstallTrafficKeys {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = client_app_read_material_f;
                 }) ::
               CS.ConnNetworkEvent ({
                 CL.message_direction = CL.Sent;
                 CL.message_value = M.TlsHandshake (M.Finished cf_f);
               }) ::
               [])
              suffix_sent_f
              suffix_received_f
              client.CS.cs_model /\
            CS.step_model
              model12_f
              (CS.ConnLocalEvent (CS.LocalVerifyFinished sf_f)) == Some after_verify_f /\
            CS.step_model
              after_verify_f
              (CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = client_app_write_material_f;
                })) == Some after_app_write_f /\
            CS.step_model
              after_app_write_f
              (CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = client_app_read_material_f;
                })) == Some after_app_read_f /\
            CS.step_model
              after_app_read_f
              (CS.ConnNetworkEvent ({
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished cf_f);
              })) == Some client.CS.cs_model /\
            CS.raw_records_exactly suffix_sent_f T.Application_data 1)
          with
          (
            WitnessPack.lemma_installed_witness_pack_from_extracted_slices
              client server
              ch_s selection_s server_shared_s sh_s ee_s cert_s cv_s sf_s cf_s
              server_material_s server_read_material_s
              server_app_write_material_s server_app_read_material_s
              model5_s server_after_write_s server_after_read_s
              prefix_sent_s prefix_received_s suffix_sent_s suffix_received_s
              start_c ch_c sh_c client_shared_c e4_c e5_c
              ee_c cert_c peer_c cv_c sf_c e13_c e14_c cf_c model4_c
              prefix_sent_c prefix_received_c suffix_sent_c suffix_received_c
              ch_r selection_r server_shared_r sh_r e5_r e6_r
              ee_r cert_r cv_r sf_r cf_r
              server_app_write_material_r server_app_read_material_r
              model5_r after_server_flight_r
              prefix_sent_r prefix_received_r suffix_sent_r suffix_received_r
              server_flight_sent_r server_flight_received_r
              client_finished_sent_r client_finished_received_r
              sf_f cf_f model12_f after_verify_f after_app_write_f after_app_read_f
              client_app_write_material_f client_app_read_material_f
              suffix_sent_f suffix_received_f
          )
        )
      )
    )

#pop-options
#pop-options
