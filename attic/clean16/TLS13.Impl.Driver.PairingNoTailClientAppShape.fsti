module TLS13.Impl.Driver.PairingNoTailClientAppShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CD = TLS13.Impl.Client.Driver
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module X = TLS13.X509.Spec

val client_no_tail_application_write_install_event
  : ev:CS.conn_event -> Tot prop

val client_no_tail_application_read_install_event
  : ev:CS.conn_event -> Tot prop

val client_no_tail_application_install_cover
  : e13:CS.conn_event -> e14:CS.conn_event -> Tot prop

val lemma_client_no_tail_application_write_install_event_cases
  (ev:CS.conn_event)
  : Lemma
      (requires client_no_tail_application_write_install_event ev)
      (ensures (
        match ev with
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
          install.CS.install_epoch == CS.TrafficApplication /\
          install.CS.install_direction == CS.TrafficWrite
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
          role_install.CS.install_role == CS.ClientEndpoint /\
          role_install.CS.install_payload.CS.install_epoch == CS.TrafficApplication /\
          role_install.CS.install_payload.CS.install_direction == CS.TrafficWrite
        | _ ->
          False))

val lemma_client_no_tail_application_read_install_event_cases
  (ev:CS.conn_event)
  : Lemma
      (requires client_no_tail_application_read_install_event ev)
      (ensures (
        match ev with
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
          install.CS.install_epoch == CS.TrafficApplication /\
          install.CS.install_direction == CS.TrafficRead
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
          role_install.CS.install_role == CS.ClientEndpoint /\
          role_install.CS.install_payload.CS.install_epoch == CS.TrafficApplication /\
          role_install.CS.install_payload.CS.install_direction == CS.TrafficRead
        | _ ->
          False))

val lemma_client_no_tail_application_install_cover_cases
  (e13:CS.conn_event)
  (e14:CS.conn_event)
  : Lemma
      (requires client_no_tail_application_install_cover e13 e14)
      (ensures
        (client_no_tail_application_write_install_event e13 /\
         client_no_tail_application_read_install_event e14) \/
        (client_no_tail_application_read_install_event e13 /\
         client_no_tail_application_write_install_event e14))

val lemma_client_no_tail_application_write_read_events_disjoint
  (ev:CS.conn_event)
  : Lemma
      (requires
        client_no_tail_application_write_install_event ev /\
        client_no_tail_application_read_install_event ev)
      (ensures False)

val lemma_client_no_tail_application_install_cover_write_first
  (e13:CS.conn_event)
  (e14:CS.conn_event)
  : Lemma
      (requires
        client_no_tail_application_install_cover e13 e14 /\
        client_no_tail_application_write_install_event e13)
      (ensures client_no_tail_application_read_install_event e14)

val lemma_client_no_tail_application_install_cover_read_first
  (e13:CS.conn_event)
  (e14:CS.conn_event)
  : Lemma
      (requires
        client_no_tail_application_install_cover e13 e14 /\
        client_no_tail_application_read_install_event e13)
      (ensures client_no_tail_application_write_install_event e14)

val lemma_client_no_tail_application_write_install_event_step_model_as_plain
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        client_no_tail_application_write_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        exists material.
          CS.step_model
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = material;
              })) == Some model1)

val lemma_client_no_tail_application_read_install_event_step_model_as_plain
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        client_no_tail_application_read_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        exists material.
          CS.step_model
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = material;
              })) == Some model1)

noextract
val client_after_application_installs_model
  : model:CS.connection_model -> Tot prop

val lemma_client_after_application_installs_model_facts
  (model:CS.connection_model)
  : Lemma
      (requires client_after_application_installs_model model)
      (ensures
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)

noextract
let client_no_tail_application_installs_shape
  (client:CS.connection_state)
  : prop =
  exists start ch sh client_shared e4 e5 ee cert peer cv sf e13 e14 rest.
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
      e13 ::
      e14 ::
      rest /\
    FStar.List.Tot.length rest == 1 /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    client_no_tail_application_install_cover e13 e14

noextract
let client_no_tail_finished_sent_shape
  (client:CS.connection_state)
  : prop =
  exists start ch sh client_shared e4 e5 ee cert peer cv sf e13 e14 cf.
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
      e13 ::
      e14 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      }) ::
      [] /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    client_no_tail_application_install_cover e13 e14

val lemma_client_no_tail_model15_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 ee cert peer cv sf e13 e14 rest11 model15 tail_sent tail_received.
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
            e13 ::
            e14 ::
            rest11 /\
          FStar.List.Tot.length rest11 == 1 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          client_no_tail_application_install_cover e13 e14 /\
          client_after_application_installs_model model15 /\
          CS.conn_events_raw_replay
            model15
            rest11
            tail_sent
            tail_received
            client.CS.cs_model)

val lemma_client_no_tail_fourteenth_and_fifteenth_events_application_install_cover_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_application_installs_shape client)

val lemma_client_no_tail_sixteenth_event_client_finished_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_finished_sent_shape client)
