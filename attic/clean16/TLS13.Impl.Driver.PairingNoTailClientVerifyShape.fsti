module TLS13.Impl.Driver.PairingNoTailClientVerifyShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CD = TLS13.Impl.Client.Driver
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PCPrS = TLS13.Impl.Driver.PairingNoTailClientProtectedShape
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module X = TLS13.X509.Spec

noextract
val client_after_certificate_validated_model
  : model:CS.connection_model -> Tot prop

noextract
val client_after_certificate_verify_model
  : model:CS.connection_model -> Tot prop

val lemma_client_after_certificate_verify_model_facts
  (model:CS.connection_model)
  : Lemma
      (requires client_after_certificate_verify_model model)
      (ensures
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
        Some? model.CS.model_handshake.CS.hs_certificate /\
        Some? model.CS.model_handshake.CS.hs_validated_peer /\
        Some? model.CS.model_handshake.CS.hs_certificate_verify /\
        Some? model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)

noextract
let client_no_tail_certificate_verify_received_shape
  (client:CS.connection_state)
  : prop =
  exists start ch sh client_shared e4 e5 ee cert peer cv rest.
    client.CS.cs_event_log ==
      CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }) ::
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
      e4 ::
      e5 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Certificate cert);
      }) ::
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      }) ::
      rest /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5

noextract
let client_no_tail_certificate_signature_verified_shape
  (client:CS.connection_state)
  : prop =
  exists start ch sh client_shared e4 e5 ee cert peer cv rest.
    client.CS.cs_event_log ==
      CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }) ::
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
      e4 ::
      e5 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Certificate cert);
      }) ::
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      }) ::
      CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
      rest /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5

val lemma_client_no_tail_model9_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 ee cert peer rest5 model9 tail_sent tail_received.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            }) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
            e4 ::
            e5 ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Certificate cert);
            }) ::
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
            rest5 /\
          FStar.List.Tot.length rest5 == 7 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          client_after_certificate_validated_model model9 /\
          CS.conn_events_raw_replay
            model9
            rest5
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0)

val lemma_client_no_tail_tenth_event_certificate_verify_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_certificate_verify_received_shape client)

val lemma_client_no_tail_model10_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 ee cert peer cv rest6 model10 tail_sent tail_received.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            }) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
            e4 ::
            e5 ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Certificate cert);
            }) ::
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            }) ::
            rest6 /\
          FStar.List.Tot.length rest6 == 6 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          model10.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
          client_after_certificate_verify_model model10 /\
          CS.conn_events_raw_replay
            model10
            rest6
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0)

val lemma_client_no_tail_eleventh_event_verify_certificate_signature_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_certificate_signature_verified_shape client)
