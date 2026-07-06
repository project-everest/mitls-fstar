module TLS13.Impl.Driver.PairingNoTailClientFinishedShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CD = TLS13.Impl.Client.Driver
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module X = TLS13.X509.Spec

noextract
val client_after_signature_verified_model
  : model:CS.connection_model -> Tot prop

noextract
val client_after_server_finished_model
  : model:CS.connection_model -> Tot prop

noextract
val client_after_server_finished_verified_model
  : model:CS.connection_model -> Tot prop

val lemma_client_after_server_finished_verified_model_facts
  (model:CS.connection_model)
  : Lemma
      (requires client_after_server_finished_verified_model model)
      (ensures
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        Some? model.CS.model_handshake.CS.hs_certificate /\
        Some? model.CS.model_handshake.CS.hs_validated_peer /\
        Some? model.CS.model_handshake.CS.hs_certificate_verify /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == true /\
        Some? model.CS.model_handshake.CS.hs_server_finished /\
        model.CS.model_handshake.CS.hs_server_finished_verified == true /\
        Some? model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)

noextract
let client_no_tail_server_finished_received_shape
  (client:CS.connection_state)
  : prop =
  exists start ch sh client_shared e4 e5 ee cert peer cv sf rest.
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
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Finished sf);
      }) ::
      rest /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5

noextract
let client_no_tail_server_finished_verified_shape
  (client:CS.connection_state)
  : prop =
  exists start ch sh client_shared e4 e5 ee cert peer cv sf rest.
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
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Finished sf);
      }) ::
      CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
      rest /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5

val lemma_client_no_tail_model11_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 ee cert peer cv rest7 model11 tail_sent tail_received.
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
            rest7 /\
          FStar.List.Tot.length rest7 == 5 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          client_after_signature_verified_model model11 /\
          CS.conn_events_raw_replay
            model11
            rest7
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0)

val lemma_client_no_tail_twelfth_event_server_finished_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_server_finished_received_shape client)

val lemma_client_no_tail_model12_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 ee cert peer cv sf rest8 model12 tail_sent tail_received.
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
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf);
            }) ::
            rest8 /\
          FStar.List.Tot.length rest8 == 4 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          model12.CS.model_handshake.CS.hs_server_finished == Some sf /\
          client_after_server_finished_model model12 /\
          CS.conn_events_raw_replay
            model12
            rest8
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0)

val lemma_client_no_tail_model13_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 ee cert peer cv sf rest9 model13 tail_sent tail_received.
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
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf);
            }) ::
            CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
            rest9 /\
          FStar.List.Tot.length rest9 == 3 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          client_after_server_finished_verified_model model13 /\
          CS.conn_events_raw_replay
            model13
            rest9
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0)

val lemma_client_no_tail_thirteenth_event_verify_finished_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_server_finished_verified_shape client)
