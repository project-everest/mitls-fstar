module TLS13.Impl.Driver.PairingNoTailClientSentRawShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module Seq = FStar.Seq
module T = TLS13.Types
module X = TLS13.X509.Spec

noextract
let client_sent_cleartext_and_finished_raw_slices
  (client:CS.connection_state)
  : prop =
  exists (ch:M.client_hello) (cf:M.finished) client_ch_raw client_finished_raw.
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append client_ch_raw client_finished_raw) /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello ch))
      client_ch_raw /\
    CS.raw_records_exactly client_finished_raw T.ApplicationData 1

(**
  Reusable raw-suffix fact for the exact ClientFinished tail:
  [LocalVerifyFinished; app-write/app-read installs; Sent Finished] contributes
  exactly one protected ApplicationData record on the sent stream.  The
  application installs may appear in either role-local order accepted by
  [client_no_tail_application_install_cover].
**)
val lemma_client_finished_exact_suffix_raw_slice
  (model:CS.connection_model)
  (sf:M.finished)
  (e13 e14:CS.conn_event)
  (cf:M.finished)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_install_cover e13 e14 /\
        CS.conn_events_raw_replay
          model
          (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
           e13 ::
           e14 ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.Finished cf);
           }) ::
           [])
          raw_sent
          raw_received
          final_model)
      (ensures
        exists finished_raw.
          Seq.equal raw_sent finished_raw /\
          CS.raw_records_exactly finished_raw T.ApplicationData 1)

val lemma_client_no_tail_finished_sent_raw_slices_for_shape
  (client:CS.connection_state)
  (start:CS.handshake_start)
  (ch:M.client_hello)
  (sh:M.server_hello)
  (client_shared:C.x25519_shared_secret)
  (e4 e5:CS.conn_event)
  (ee:M.encrypted_extensions)
  (cert:M.certificate_msg)
  (peer:X.peer_identity)
  (cv:M.certificate_verify)
  (sf:M.finished)
  (e13 e14:CS.conn_event)
  (cf:M.finished)
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
        CS.connection_state_raw_event_replay_consistent client)
      (ensures
        exists client_ch_raw client_finished_raw.
          Seq.equal
            client.CS.cs_wire_log.CL.raw_sent
            (B.append client_ch_raw client_finished_raw) /\
          CS.cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello ch))
            client_ch_raw /\
          CS.raw_records_exactly client_finished_raw T.ApplicationData 1)

val lemma_client_no_tail_finished_sent_raw_slices
  (client:CS.connection_state)
  : Lemma
      (requires
        PNTCAS.client_no_tail_finished_sent_shape client /\
        CS.connection_state_raw_event_replay_consistent client)
      (ensures client_sent_cleartext_and_finished_raw_slices client)
