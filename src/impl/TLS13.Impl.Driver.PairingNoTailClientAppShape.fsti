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
