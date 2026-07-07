module TLS13.Impl.Driver.PairingNoTailClientFinishedStaged

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PNTCFS = TLS13.Impl.Driver.PairingNoTailClientFinishedShape
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNTCSR = TLS13.Impl.Driver.PairingNoTailClientSentRawShape
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized

let lemma_clean16_no_tail_valid_byte_traces_client_finished_staged_milestone
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
      (ensures
        paired_no_tail_client_finished_staged_milestone
          client
          server)
=
  PNTN.lemma_clean16_no_tail_valid_byte_traces_role_local_client_finished_sent_server_start_spine16
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTN.lemma_clean16_no_tail_valid_byte_traces_client_sent_cleartext_and_finished_raw_slices
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTN.lemma_clean16_no_tail_valid_byte_traces_server_received_cleartext_and_client_finished_raw_slices
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTN.lemma_clean16_no_tail_valid_byte_traces_paired_wire_logs
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTCFS.lemma_client_no_tail_model12_witness client;
  eliminate exists
    start
    ch
    sh
    client_shared
    e4
    e5
    ee
    cert
    peer
    cv
    sf
    rest8
    model12
    tail_sent
    tail_received.
    client.CS.cs_event_log ==
      CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
      CS.ConnNetworkEvent ({
        TLS13.ConnectionLog.message_direction = TLS13.ConnectionLog.Sent;
        TLS13.ConnectionLog.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.ClientHello ch);
      }) ::
      CS.ConnNetworkEvent ({
        TLS13.ConnectionLog.message_direction = TLS13.ConnectionLog.Received;
        TLS13.ConnectionLog.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.ServerHello sh);
      }) ::
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
      e4 ::
      e5 ::
      CS.ConnNetworkEvent ({
        TLS13.ConnectionLog.message_direction = TLS13.ConnectionLog.Received;
        TLS13.ConnectionLog.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.EncryptedExtensions ee);
      }) ::
      CS.ConnNetworkEvent ({
        TLS13.ConnectionLog.message_direction = TLS13.ConnectionLog.Received;
        TLS13.ConnectionLog.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.Certificate cert);
      }) ::
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
      CS.ConnNetworkEvent ({
        TLS13.ConnectionLog.message_direction = TLS13.ConnectionLog.Received;
        TLS13.ConnectionLog.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.CertificateVerify cv);
      }) ::
      CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
      CS.ConnNetworkEvent ({
        TLS13.ConnectionLog.message_direction = TLS13.ConnectionLog.Received;
        TLS13.ConnectionLog.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.Finished sf);
      }) ::
      rest8 /\
    FStar.List.Tot.length rest8 == 4 /\
    TLS13.Impl.Driver.PairingNoTailClientPostSharedShape.client_no_tail_two_handshake_install_cover e4 e5 /\
    model12.CS.model_handshake.CS.hs_server_finished == Some sf /\
    PNTCFS.client_after_server_finished_model model12 /\
    CS.conn_events_raw_replay
      model12
      rest8
      tail_sent
      tail_received
      client.CS.cs_model /\
    TLS13.Impl.Driver.PairingNoTailInversion.client_application_progress_rank
      client.CS.cs_model == 0
  returns
    paired_no_tail_client_finished_staged_milestone
      client
      server
  with _.
  (
    PNTCFS.lemma_client_after_server_finished_model_facts model12;
    assert (client_finished_model12_replay_slice client);
    assert (PNTCAS.client_no_tail_finished_sent_shape client);
    eliminate exists
      start2
      ch2
      sh2
      client_shared2
      e42
      e52
      ee2
      cert2
      peer2
      cv2
      sf2
      e132
      e142
      cf2.
      client.CS.cs_event_log ==
        CS.ConnLocalEvent (CS.LocalStartHandshake start2) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.ClientHello ch2);
        }) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.ServerHello sh2);
        }) ::
        CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared2) ::
        e42 ::
        e52 ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.EncryptedExtensions ee2);
        }) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.Certificate cert2);
        }) ::
        CS.ConnLocalEvent (CS.LocalValidateCertificate peer2) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.CertificateVerify cv2);
        }) ::
        CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv2) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.Finished sf2);
        }) ::
        CS.ConnLocalEvent (CS.LocalVerifyFinished sf2) ::
        e132 ::
        e142 ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.Finished cf2);
        }) ::
        [] /\
      PCPS.client_no_tail_two_handshake_install_cover e42 e52 /\
      PNTCAS.client_no_tail_application_install_cover e132 e142
    returns client_finished_model12_exact_suffix_replay_slice client
    with _.
    (
      assert (sf2 == sf);
      assert (
        rest8 ==
          CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
          e132 ::
          e142 ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.Finished cf2);
          }) ::
          []);
      assert (
        CS.conn_events_raw_replay
          model12
          (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
           e132 ::
           e142 ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = TLS13.Messages.TlsHandshake (TLS13.Messages.Finished cf2);
           }) ::
           [])
          tail_sent
          tail_received
          client.CS.cs_model);
      assert (client_finished_model12_exact_suffix_replay_slice client)
    );
    assert (PNTCSR.client_sent_cleartext_and_finished_raw_slices client);
    assert (PNTN.server_received_cleartext_and_client_finished_raw_slices server);
    assert (CS.paired_wire_logs client server)
  )
