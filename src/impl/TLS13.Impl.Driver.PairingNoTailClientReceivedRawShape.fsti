module TLS13.Impl.Driver.PairingNoTailClientReceivedRawShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module GEE   = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV   = TLS13.Wire.Generated.CertificateVerify
module GFin  = TLS13.Wire.Generated.Finished
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module Seq = FStar.Seq
module T = TLS13.Types
module X = TLS13.X509.Spec

noextract
let client_received_cleartext_and_server_flight_raw_slices
  (client:CS.connection_state)
  : prop =
  exists
    (sh:GSH.serverHello)
    (ee:GEE.encryptedExtensions)
    (cert:GCert.certificate)
    (cv:GCV.certificateVerify)
    (sf:GFin.finished)
    server_sh_raw
    ee_raw
    cert_raw
    cv_raw
    sf_raw.
    Seq.equal
      client.CS.cs_wire_log.CL.raw_received
      (B.append
        server_sh_raw
        (B.append ee_raw (B.append cert_raw (B.append cv_raw sf_raw)))) /\
    CS.received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello sh))
      server_sh_raw /\
    CS.raw_records_exactly ee_raw T.Application_data 1 /\
    CS.raw_records_exactly cert_raw T.Application_data 1 /\
    CS.raw_records_exactly cv_raw T.Application_data 1 /\
    CS.raw_records_exactly sf_raw T.Application_data 1

val lemma_client_no_tail_server_flight_received_raw_slices_for_shape
  (client:CS.connection_state)
  (start:CS.handshake_start)
  (ch:GCH.clientHello)
  (sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (e4 e5:CS.conn_event)
  (ee:GEE.encryptedExtensions)
  (cert:GCert.certificate)
  (peer:X.peer_identity)
  (cv:GCV.certificateVerify)
  (sf:GFin.finished)
  (e13 e14:CS.conn_event)
  (cf:GFin.finished)
  : Lemma
      (requires
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
        PNTCAS.client_no_tail_application_install_cover e13 e14 /\
        TLS13.Spec.StateMachine.Replay.connection_state_raw_event_replay_consistent client)
      (ensures
        exists server_sh_raw ee_raw cert_raw cv_raw sf_raw.
          Seq.equal
            client.CS.cs_wire_log.CL.raw_received
            (B.append
              server_sh_raw
              (B.append ee_raw (B.append cert_raw (B.append cv_raw sf_raw)))) /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ServerHello sh))
            server_sh_raw /\
          CS.raw_records_exactly ee_raw T.Application_data 1 /\
          CS.raw_records_exactly cert_raw T.Application_data 1 /\
          CS.raw_records_exactly cv_raw T.Application_data 1 /\
          CS.raw_records_exactly sf_raw T.Application_data 1)

val lemma_client_no_tail_server_flight_received_raw_slices
  (client:CS.connection_state)
  : Lemma
      (requires
        PNTCAS.client_no_tail_finished_sent_shape client /\
        TLS13.Spec.StateMachine.Replay.connection_state_raw_event_replay_consistent client)
      (ensures client_received_cleartext_and_server_flight_raw_slices client)
