module TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.WitnessPack

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


#push-options "--split_queries always --z3rlimit 10"

noextract
let lemma_installed_witness_pack_from_extracted_slices
(client server:CS.connection_state)
  (ch_s:GCH.clientHello)
  (selection_s:CS.server_handshake_selection)
  (server_shared_s:C.x25519_shared_secret)
  (sh_s:GSH.serverHello)
  (ee_s:GEE.encryptedExtensions)
  (cert_s:GCert.certificate)
  (cv_s:GCV.certificateVerify)
  (sf_s cf_s:GFin.finished)
  (server_material_s server_read_material_s:CS.traffic_key_material)
  (server_app_write_material_s server_app_read_material_s:CS.traffic_key_material)
  (model5_s server_after_write_s server_after_read_s:CS.connection_model)
  (prefix_sent_s prefix_received_s suffix_sent_s suffix_received_s:B.bytes)
  (start_c:CS.handshake_start)
  (ch_c:GCH.clientHello)
  (sh_c:GSH.serverHello)
  (client_shared_c:C.x25519_shared_secret)
  (e4_c e5_c:CS.conn_event)
  (ee_c:GEE.encryptedExtensions)
  (cert_c:GCert.certificate)
  (peer_c:X.peer_identity)
  (cv_c:GCV.certificateVerify)
  (sf_c:GFin.finished)
  (e13_c e14_c:CS.conn_event)
  (cf_c:GFin.finished)
  (model4_c:CS.connection_model)
  (prefix_sent_c prefix_received_c suffix_sent_c suffix_received_c:B.bytes)
  (ch_r:GCH.clientHello)
  (selection_r:CS.server_handshake_selection)
  (server_shared_r:C.x25519_shared_secret)
  (sh_r:GSH.serverHello)
  (e5_r e6_r:CS.conn_event)
  (ee_r:GEE.encryptedExtensions)
  (cert_r:GCert.certificate)
  (cv_r:GCV.certificateVerify)
  (sf_r cf_r:GFin.finished)
  (server_app_write_material_r server_app_read_material_r:CS.traffic_key_material)
  (model5_r after_server_flight_r:CS.connection_model)
  (prefix_sent_r prefix_received_r suffix_sent_r suffix_received_r:B.bytes)
  (server_flight_sent_r server_flight_received_r:B.bytes)
  (client_finished_sent_r client_finished_received_r:B.bytes)
  (sf_f cf_f:GFin.finished)
  (model12_f after_verify_f after_app_write_f after_app_read_f:CS.connection_model)
  (client_app_write_material_f client_app_read_material_f:CS.traffic_key_material)
  (suffix_sent_f suffix_received_f:B.bytes)
  : Lemma
      (requires
        clean16_staged_boundary_derivation_milestones client server /\
        WFL.paired_cleartext_hello_key_shares client server /\
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
                server.CS.cs_model) /\
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
                  client.CS.cs_model) /\
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
                    server.CS.cs_model) /\
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
                    CS.raw_records_exactly suffix_sent_f T.Application_data 1))
      (ensures
        PNTPPD.installed_protected_projection_replay_witnesses client server)
=
            lemma_h4_client_exact_recon client server;
            let goal_w : prop = PNTPPD.installed_protected_projection_replay_witnesses client server in
            eliminate exists (model12_ex:CS.connection_model) (sf_ex cf_ex:GFin.finished)
               (cawm_ex carm_ex:CS.traffic_key_material) (av_ex aw_ex ar_ex:CS.connection_model)
               (suffix_sent_ex suffix_received_ex prefix_sent_ex frag_ex:B.bytes)
               (start_ex:CS.handshake_start) (ch_ex:GCH.clientHello) (sh_ex:GSH.serverHello) (client_shared_ex:C.x25519_shared_secret)
               (e4_ex e5_ex:CS.conn_event) (ee_ex:GEE.encryptedExtensions) (cert_ex:GCert.certificate) (peer_ex:X.peer_identity)
               (cv_ex:GCV.certificateVerify) (e13_ex e14_ex:CS.conn_event) (prefix_received_ex:B.bytes).
               (Seq.equal client.CS.cs_wire_log.CL.raw_sent (B.append prefix_sent_ex suffix_sent_ex) /\
                W.parse_record_wire prefix_sent_ex == Some (T.Handshake, frag_ex, B.length prefix_sent_ex) /\
                CS.step_model model12_ex (ev_vf_of sf_ex) == Some av_ex /\
                CS.step_model av_ex (iaw cawm_ex) == Some aw_ex /\
                CS.step_model aw_ex (iar carm_ex) == Some ar_ex /\
                CS.step_model ar_ex (ev_sent_of cf_ex) == Some client.CS.cs_model /\
                SMReplay.conn_events_sent_seal_replay model12_ex
                  (ev_vf_of sf_ex :: iaw cawm_ex :: iar carm_ex :: ev_sent_of cf_ex :: [])
                  suffix_sent_ex suffix_received_ex client.CS.cs_model /\
                SMReplay.conn_events_sent_seal_replay
                  (CS.initial_model client.CS.cs_model.CS.model_config)
                  (CS.ConnLocalEvent (CS.LocalStartHandshake start_ex) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch_ex); }) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh_ex); }) ::
                   CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared_ex) ::
                   e4_ex :: e5_ex ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_ex); }) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_ex); }) ::
                   CS.ConnLocalEvent (CS.LocalValidateCertificate peer_ex) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_ex); }) ::
                   CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_ex) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_ex); }) ::
                   [])
                  prefix_sent_ex prefix_received_ex model12_ex /\
                client.CS.cs_event_log ==
                  (CS.ConnLocalEvent (CS.LocalStartHandshake start_ex) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch_ex); }) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh_ex); }) ::
                   CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared_ex) ::
                   e4_ex :: e5_ex ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_ex); }) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_ex); }) ::
                   CS.ConnLocalEvent (CS.LocalValidateCertificate peer_ex) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_ex); }) ::
                   CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_ex) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_ex); }) ::
                   CS.ConnLocalEvent (CS.LocalVerifyFinished sf_ex) ::
                   e13_ex :: e14_ex ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_ex); }) ::
                   []))
            with
            (
            let ordered_rest_s =
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
            let server_write_install =
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
            peel_sent_bp model5_s server_write_install (server_read_install :: ordered_rest_s) suffix_sent_s suffix_received_s server.CS.cs_model;
            assert (step_next model5_s server_write_install == server_after_write_s);
            peel_sent_bp server_after_write_s server_read_install ordered_rest_s suffix_sent_s suffix_received_s server.CS.cs_model;
            assert (step_next server_after_write_s server_read_install == server_after_read_s);
            let srv_raw_sent = suffix_sent_s in
            let srv_raw_received = suffix_received_s in
            (
            let ordered_rest_c =
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
            lemma_two_install_events_are_local e4_c e5_c;
            peel_received_bp model4_c e4_c (e5_c :: ordered_rest_c) suffix_sent_c suffix_received_c client.CS.cs_model;
            let client_after_e4_c = step_next model4_c e4_c in
            peel_received_bp client_after_e4_c e5_c ordered_rest_c suffix_sent_c suffix_received_c client.CS.cs_model;
            let client_after_installs_c = step_next client_after_e4_c e5_c in
            let cli_raw_sent = suffix_sent_c in
            let cli_raw_received = suffix_received_c in
            (
            let ev_sent_ee =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_s);
              } in
            let ev_sent_cert =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Certificate cert_s);
              } in
            let ev_sign_cv = CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_s) in
            let ev_sent_cv =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv_s);
              } in
            let ev_sent_sf =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished sf_s);
              } in
            let s_after0 = step_next server_after_read_s ev_sent_ee in
            let s_after1 = step_next s_after0 ev_sent_cert in
            let s_after_auth = step_next s_after1 ev_sign_cv in
            let s_after2 = step_next s_after_auth ev_sent_cv in
            let s_after3 = step_next s_after2 ev_sent_sf in
            let ev_recv_ee =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c);
              } in
            let ev_recv_cert =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Certificate cert_c);
              } in
            let ev_validate = CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c) in
            let ev_recv_cv =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c);
              } in
            let ev_verify_cert = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c) in
            let ev_recv_sf =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished sf_c);
              } in
            let c_after0 = step_next client_after_installs_c ev_recv_ee in
            let c_after1 = step_next c_after0 ev_recv_cert in
            let c_after_auth = step_next c_after1 ev_validate in
            let c_after2 = step_next c_after_auth ev_recv_cv in
            let c_after_verify = step_next c_after2 ev_verify_cert in
            let c_after3 = step_next c_after_verify ev_recv_sf in
            let ev_install_app_write_forrole =
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficWrite;
                    CS.install_material = server_app_write_material_r;
                  };
                }) in
            let ev_recv_cf_r =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished cf_r);
              } in
            let cf_srv_after_app_write = step_next after_server_flight_r ev_install_app_write_forrole in
            let cf_srv_after_finished = step_next cf_srv_after_app_write ev_recv_cf_r in
            // ---- Peel step facts along the server flight ----
            peel_sent server_after_read_s ev_sent_ee
              [ev_sent_cert; ev_sign_cv; ev_sent_cv; ev_sent_sf;
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
               CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_s)]
              server.CS.cs_model;
            let w : PNTPPD.installed_protected_projection_replay_witness_pack = {
              PNTPPD.ippr_server_flight_sender = server_after_read_s;
              PNTPPD.ippr_server_flight_receiver = client_after_installs_c;
              PNTPPD.ippr_server_after0 = s_after0;
              PNTPPD.ippr_client_after0 = c_after0;
              PNTPPD.ippr_server_after1 = s_after1;
              PNTPPD.ippr_client_after1 = c_after1;
              PNTPPD.ippr_server_after_auth_skip = s_after_auth;
              PNTPPD.ippr_client_after_auth_skip = c_after_auth;
              PNTPPD.ippr_server_after2 = s_after2;
              PNTPPD.ippr_client_after2 = c_after2;
              PNTPPD.ippr_client_after_verify_skip = c_after_verify;
              PNTPPD.ippr_server_after3 = s_after3;
              PNTPPD.ippr_client_after3 = c_after3;
              PNTPPD.ippr_server_auth_skip = CS.LocalSignCertificateVerify cv_s;
              PNTPPD.ippr_client_auth_skip = CS.LocalValidateCertificate peer_c;
              PNTPPD.ippr_client_verify_skip = CS.LocalVerifyCertificateSignature cv_c;
              PNTPPD.ippr_sent_msg0 = M.EncryptedExtensions ee_s;
              PNTPPD.ippr_received_msg0 = M.EncryptedExtensions ee_c;
              PNTPPD.ippr_sent_msg1 = M.Certificate cert_s;
              PNTPPD.ippr_received_msg1 = M.Certificate cert_c;
              PNTPPD.ippr_sent_msg2 = M.CertificateVerify cv_s;
              PNTPPD.ippr_received_msg2 = M.CertificateVerify cv_c;
              PNTPPD.ippr_sent_msg3 = M.Finished sf_s;
              PNTPPD.ippr_received_msg3 = M.Finished sf_c;
              PNTPPD.ippr_server_rest =
                [
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
                ];
              PNTPPD.ippr_client_rest =
                [
                  CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
                  e13_c;
                  e14_c;
                  CS.ConnNetworkEvent {
                    CL.message_direction = CL.Sent;
                    CL.message_value = M.TlsHandshake (M.Finished cf_c);
                  }
                ];
              PNTPPD.ippr_server_raw_sent = srv_raw_sent;
              PNTPPD.ippr_server_raw_received = srv_raw_received;
              PNTPPD.ippr_client_raw_sent = cli_raw_sent;
              PNTPPD.ippr_client_raw_received = cli_raw_received;
              PNTPPD.ippr_server_final = server.CS.cs_model;
              PNTPPD.ippr_client_final = client.CS.cs_model;
              PNTPPD.ippr_client_finished_sender = model12_ex;
              PNTPPD.ippr_client_finished_receiver = after_server_flight_r;
              PNTPPD.ippr_cf_client_after_verify = av_ex;
              PNTPPD.ippr_cf_client_after_app_write = aw_ex;
              PNTPPD.ippr_cf_client_after_app_read = ar_ex;
              PNTPPD.ippr_cf_server_after_app_write = cf_srv_after_app_write;
              PNTPPD.ippr_cf_client_after_finished = client.CS.cs_model;
              PNTPPD.ippr_cf_server_after_finished = cf_srv_after_finished;
              PNTPPD.ippr_verified_server_finished = sf_ex;
              PNTPPD.ippr_client_app_write_material = cawm_ex;
              PNTPPD.ippr_client_app_read_material = carm_ex;
              PNTPPD.ippr_server_app_write_material = server_app_write_material_r;
              PNTPPD.ippr_sent_msg4 = M.Finished cf_ex;
              PNTPPD.ippr_received_msg4 = M.Finished cf_r;
              PNTPPD.ippr_client_finished_rest = [];
              PNTPPD.ippr_server_finished_rest =
                [
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
                ];
              PNTPPD.ippr_client_finished_raw_sent = suffix_sent_ex;
              PNTPPD.ippr_client_finished_raw_received = suffix_received_ex;
              PNTPPD.ippr_server_finished_raw_sent = client_finished_sent_r;
              PNTPPD.ippr_server_finished_raw_received = client_finished_received_r;
              PNTPPD.ippr_client_finished_final = client.CS.cs_model;
              PNTPPD.ippr_server_finished_final = server.CS.cs_model;
            } in
            introduce exists (w0:PNTPPD.installed_protected_projection_replay_witness_pack).
              PNTPPD.installed_protected_projection_replay_pack_inputs client server w0
            with w
            and (
              // --- Message-match: field-track the two canonical flights ---
              lemma_server_flight_walk server_after_read_s ee_s cert_s cv_s sf_s cf_s
                server_app_write_material_s server_app_read_material_s server.CS.cs_model;
              lemma_client_flight_walk client_after_installs_c ee_c cert_c peer_c cv_c sf_c cf_c
                e13_c e14_c client.CS.cs_model;
              lemma_client_flight_step_and_record_facts
                client_after_installs_c ee_c cert_c peer_c cv_c sf_c cf_c
                e13_c e14_c client.CS.cs_model;
              // server.hs_client_finished == Some cf_r (cross-flight, from CFRR suffix)
              lemma_cfrr_suffix_walk after_server_flight_r
                server_app_write_material_r server_app_read_material_r cf_r server.CS.cs_model;
              // client.hs_client_finished == Some cf_f (cross-flight, from CF slice sent finished)
              lemma_sent_finished_at_appdata_sets_client_finished ar_ex client.CS.cs_model cf_ex;
              // --- Hard conjuncts (alignments + byte pairings) ---
              // ---- Hole 1: server-write / client-read handshake install alignment ----
              lemma_pack_server_flight_align_real client server ch_s selection_s server_shared_s sh_s
                ee_s cert_s cv_s sf_s cf_s
                server_material_s server_read_material_s server_app_write_material_s server_app_read_material_s
                model5_s server_after_write_s server_after_read_s
                start_c ch_c sh_c client_shared_c
                ee_c cert_c peer_c cv_c sf_c cf_c
                e4_c e5_c e13_c e14_c
                model4_c client_after_e4_c client_after_installs_c;
              // ---- Hole 2: server-sent / client-received suffix byte equality ----
              assert (PNTSFS.clean16_server_encrypted_flight_staged_milestone client server);
              assert (SMCorr.paired_wire_logs client server);
              lemma_pack_server_bytes_real client server ch_s selection_s server_shared_s sh_s
                ee_s cert_s cv_s sf_s cf_s
                server_material_s server_read_material_s server_app_write_material_s server_app_read_material_s
                model5_s prefix_sent_s prefix_received_s suffix_sent_s suffix_received_s
                start_c ch_c sh_c client_shared_c
                e4_c e5_c ee_c cert_c peer_c cv_c sf_c e13_c e14_c cf_c
                model4_c prefix_sent_c prefix_received_c suffix_received_c;
              // ---- Hole 3: client-write / server-read handshake install alignment ----
              lemma_cf_client_identity client
                (CS.initial_model client.CS.cs_model.CS.model_config)
                model4_c client_after_e4_c client_after_installs_c c_after3 model12_ex
                start_ex ch_ex sh_ex client_shared_ex e4_ex e5_ex ee_ex cert_ex peer_ex cv_ex sf_ex e13_ex e14_ex cf_ex
                start_c ch_c sh_c client_shared_c e4_c e5_c ee_c cert_c peer_c cv_c sf_c e13_c e14_c cf_c
                prefix_sent_ex prefix_received_ex prefix_sent_c prefix_received_c suffix_sent_c suffix_received_c;
              lemma_pack_cf_align_core client server ch_r selection_r server_shared_r sh_r
                e5_r e6_r ee_r cert_r cv_r sf_r cf_r server_app_write_material_r server_app_read_material_r
                model5_r after_server_flight_r server_flight_sent_r server_flight_received_r
                start_c ch_c sh_c client_shared_c e4_c e5_c e13_c e14_c ee_c cert_c peer_c cv_c sf_c cf_c
                model4_c client_after_e4_c client_after_installs_c c_after3
                suffix_sent_c suffix_received_c;
              assert (PWL.write_read_record_material_aligned model12_ex after_server_flight_r);
              // ---- HOLE 4 (closed): client-finished suffix byte equality ----
              // suffix_sent_ex (stream-tied client-finished record) == client_finished_received_r
              lemma_server_prefix_received_ch
                (CS.initial_model server.CS.cs_model.CS.model_config)
                ch_r selection_r server_shared_r sh_r
                prefix_sent_r prefix_received_r model5_r;
              lemma_received_client_hello_is_wire_h4 ch_r prefix_received_r;
              eliminate exists frag2.
                W.parse_record_wire prefix_received_r == Some (T.Handshake, frag2, B.length prefix_received_r)
              with
              (
                // server flight received bytes are empty
                lemma_server_flight_received_empty model5_r e5_r e6_r ee_r cert_r cv_r sf_r
                  server_flight_sent_r server_flight_received_r after_server_flight_r;
                Seq.lemma_eq_elim server_flight_received_r B.empty;
                append_empty_left client_finished_received_r;
                Seq.lemma_eq_elim
                  (B.append server_flight_received_r client_finished_received_r)
                  client_finished_received_r;
                Seq.lemma_eq_elim suffix_received_r client_finished_received_r;
                // S == server.raw_received == prefix_received_r ++ suffix_received_r
                //   == prefix_received_r ++ client_finished_received_r
                assert (SMCorr.paired_wire_logs client server);
                Seq.lemma_eq_elim
                  client.CS.cs_wire_log.CL.raw_sent
                  server.CS.cs_wire_log.CL.raw_received;
                Seq.lemma_eq_elim
                  server.CS.cs_wire_log.CL.raw_received
                  (B.append prefix_received_r suffix_received_r);
                Seq.lemma_eq_elim
                  (B.append prefix_received_r suffix_received_r)
                  (B.append prefix_received_r client_finished_received_r);
                // client side split (from packaging bundle):
                //   S == prefix_sent_ex ++ suffix_sent_ex
                // first-wire-record uniqueness pins suffix_sent_ex == client_finished_received_r
                lemma_first_wire_record_unique_split_h4
                  client.CS.cs_wire_log.CL.raw_sent
                  prefix_sent_ex suffix_sent_ex
                  prefix_received_r client_finished_received_r
                  T.Handshake T.Handshake frag_ex frag2
              );
              // Bring the 10 final message-field facts into context (from the walks/inversions)
              assert (server.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == Some ee_s);
              assert (server.CS.cs_model.CS.model_handshake.CS.hs_certificate == Some cert_s);
              assert (server.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv_s);
              assert (server.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some sf_s);
              assert (server.CS.cs_model.CS.model_handshake.CS.hs_client_finished == Some cf_r);
              assert (client.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == Some ee_c);
              assert (client.CS.cs_model.CS.model_handshake.CS.hs_certificate == Some cert_c);
              assert (client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv_c);
              assert (client.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some sf_c);
              assert (client.CS.cs_model.CS.model_handshake.CS.hs_client_finished == Some cf_ex);
              // Isolate the message-match conjunct (clean-context helper)
              lemma_message_match client server ee_s cert_s cv_s sf_s cf_r ee_c cert_c cv_c sf_c cf_ex;
              assert (PNTPPD.installed_protected_projection_replay_pack_inputs client server w)
            )
            )
            )
            )

#pop-options
