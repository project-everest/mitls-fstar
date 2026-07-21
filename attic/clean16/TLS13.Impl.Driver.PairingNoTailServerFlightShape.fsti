module TLS13.Impl.Driver.PairingNoTailServerFlightShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module GEE   = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV   = TLS13.Wire.Generated.CertificateVerify
module GFin  = TLS13.Wire.Generated.Finished
module PNTWHR = TLS13.Impl.Driver.PairingNoTailServerHelloWindowRank

(**
  Server post-[ServerHello] shape after the two commuting
  [ServerEndpoint]/[TrafficHandshake] installs have both happened.

  The preceding milestone deliberately leaves those two installs
  order-insensitive.  This predicate starts immediately after them and fixes the
  remaining nine server events.
**)
noextract
let server_post_two_handshake_installs_tail_order
  (rest:list CS.conn_event)
  : prop =
  exists
    (ee:GEE.encryptedExtensions)
    (cert:GCert.certificate)
    (cv:GCV.certificateVerify)
    (sf:GFin.finished)
    (cf:GFin.finished)
    (server_app_write_material:CS.traffic_key_material)
    (server_app_read_material:CS.traffic_key_material).
    rest ==
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
      ]

val lemma_server_post_two_handshake_installs_tail_order_from_replay
  (model:CS.connection_model)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        FStar.List.Tot.length rest == 9 /\
        CS.conn_events_raw_replay
          model
          rest
          raw_sent
          raw_received
          final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNTWHR.server_hello_window_rank final_model == 0)
      (ensures server_post_two_handshake_installs_tail_order rest)