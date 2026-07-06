module TLS13.Impl.Driver.PairingNoTailClientSentRawShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PWR = TLS13.ConnectionState.ProtectedWireReplay
module Seq = FStar.Seq
module T = TLS13.Types
module X = TLS13.X509.Spec

let event_has_empty_sent_delta
  (ev:CS.conn_event)
  : Tot prop =
  match ev with
  | CS.ConnLocalEvent _ ->
    True
  | CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Received

let sent_finished_event (cf:M.finished) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.Finished cf);
  })

let rec empty_sent_until_finished
  (events:list CS.conn_event)
  (cf:M.finished)
  : Tot prop
        (decreases events)
  =
  match events with
  | [] ->
    False
  | ev :: [] ->
    ev == sent_finished_event cf
  | ev :: rest ->
    event_has_empty_sent_delta ev /\
    empty_sent_until_finished rest cf

let lemma_event_raw_delta_legal_empty_sent
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        event_has_empty_sent_delta ev /\
        CS.event_raw_delta_legal model ev delta_sent delta_received)
      (ensures Seq.equal delta_sent B.empty)
=
  match ev with
  | CS.ConnLocalEvent _ -> ()
  | CS.ConnNetworkEvent msg ->
    assert (msg.CL.message_direction == CL.Received)

let lemma_event_raw_delta_legal_local
  (model:CS.connection_model)
  (ev:CS.local_event)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.event_raw_delta_legal
          model
          (CS.ConnLocalEvent ev)
          delta_sent
          delta_received)
      (ensures
        Seq.equal delta_sent B.empty /\
        Seq.equal delta_received B.empty)
=
  ()

let lemma_event_raw_delta_legal_sent_client_hello
  (model:CS.connection_model)
  (ch:M.client_hello)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.event_raw_delta_legal
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }))
          delta_sent
          delta_received)
      (ensures
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello ch))
          delta_sent /\
        Seq.equal delta_received B.empty)
=
  ()

let lemma_finished_event_raw_slice
  (model:CS.connection_model)
  (cf:M.finished)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model
          [sent_finished_event cf]
          raw_sent
          raw_received
          final_model)
      (ensures CS.raw_records_exactly raw_sent T.ApplicationData 1)
=
  PWR.lemma_conn_events_raw_replay_head
    model
    (sent_finished_event cf)
    []
    raw_sent
    raw_received
    final_model;
  eliminate exists model1 delta_sent delta_received tail_sent tail_received.
    CS.legal_event model (sent_finished_event cf) /\
    CS.step_model model (sent_finished_event cf) == Some model1 /\
    CS.event_raw_delta_legal model (sent_finished_event cf) delta_sent delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    CS.conn_events_raw_replay model1 [] tail_sent tail_received final_model
  returns CS.raw_records_exactly raw_sent T.ApplicationData 1
  with _.
  (
    assert_norm (CS.network_message_is_cleartext
      CL.Sent
      (M.TlsHandshake (M.Finished cf)) == false);
    assert_norm (CS.protected_record_count
      CL.Sent
      (M.TlsHandshake (M.Finished cf)) == 1);
    assert (CS.raw_records_exactly delta_sent T.ApplicationData 1);
    assert (Seq.equal tail_sent B.empty);
    Seq.lemma_eq_elim tail_sent B.empty;
    Seq.append_empty_r delta_sent;
    assert (Seq.equal raw_sent delta_sent);
    Seq.lemma_eq_elim raw_sent delta_sent
  )

let rec lemma_empty_sent_until_finished_raw_slice
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (cf:M.finished)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        empty_sent_until_finished events cf /\
        CS.conn_events_raw_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (ensures
        exists finished_raw.
          Seq.equal raw_sent finished_raw /\
          CS.raw_records_exactly finished_raw T.ApplicationData 1)
      (decreases events)
=
  match events with
  | [] ->
    assert False
  | ev :: rest ->
    (match rest with
    | [] ->
      assert (ev == sent_finished_event cf);
      assert (events == [sent_finished_event cf]);
      assert (CS.conn_events_raw_replay
        model
        [sent_finished_event cf]
        raw_sent
        raw_received
        final_model);
      lemma_finished_event_raw_slice
        model
        cf
        raw_sent
        raw_received
        final_model;
      assert (exists finished_raw.
        Seq.equal raw_sent finished_raw /\
        CS.raw_records_exactly finished_raw T.ApplicationData 1)
    | _ ->
      PWR.lemma_conn_events_raw_replay_head
        model
        ev
        rest
        raw_sent
        raw_received
        final_model;
      eliminate exists model1 delta_sent delta_received tail_sent tail_received.
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1 /\
        CS.event_raw_delta_legal model ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        CS.conn_events_raw_replay
          model1
          rest
          tail_sent
          tail_received
          final_model
      returns
        exists finished_raw.
          Seq.equal raw_sent finished_raw /\
          CS.raw_records_exactly finished_raw T.ApplicationData 1
      with _.
      (
        assert (event_has_empty_sent_delta ev);
        lemma_event_raw_delta_legal_empty_sent
          model
          ev
          delta_sent
          delta_received;
        lemma_empty_sent_until_finished_raw_slice
          model1
          rest
          cf
          tail_sent
          tail_received
          final_model;
        eliminate exists finished_raw.
          Seq.equal tail_sent finished_raw /\
          CS.raw_records_exactly finished_raw T.ApplicationData 1
        returns
          exists finished_raw.
            Seq.equal raw_sent finished_raw /\
            CS.raw_records_exactly finished_raw T.ApplicationData 1
        with _.
        (
          Seq.lemma_eq_elim delta_sent B.empty;
          CL.lemma_append_empty_left tail_sent;
          assert (Seq.equal raw_sent tail_sent);
          Seq.lemma_eq_elim raw_sent tail_sent;
          assert (exists finished_raw0.
            Seq.equal raw_sent finished_raw0 /\
            CS.raw_records_exactly finished_raw0 T.ApplicationData 1)
        )
      ))

let lemma_handshake_install_event_empty_sent
  (ev:CS.conn_event)
  : Lemma
      (requires
        PCPS.client_no_tail_handshake_write_install_event ev \/
        PCPS.client_no_tail_handshake_read_install_event ev)
      (ensures event_has_empty_sent_delta ev)
=
  match ev with
  | CS.ConnLocalEvent _ -> ()
  | _ ->
    if PCPS.client_no_tail_handshake_write_install_event ev then (
      PCPS.lemma_client_no_tail_handshake_write_install_event_cases ev;
      assert False
    ) else (
      PCPS.lemma_client_no_tail_handshake_read_install_event_cases ev;
      assert False
    )

let lemma_application_install_event_empty_sent
  (ev:CS.conn_event)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_write_install_event ev \/
        PNTCAS.client_no_tail_application_read_install_event ev)
      (ensures event_has_empty_sent_delta ev)
=
  match ev with
  | CS.ConnLocalEvent _ -> ()
  | _ ->
    if PNTCAS.client_no_tail_application_write_install_event ev then (
      PNTCAS.lemma_client_no_tail_application_write_install_event_cases ev;
      assert False
    ) else (
      PNTCAS.lemma_client_no_tail_application_read_install_event_cases ev;
      assert False
    )

let lemma_tail_empty_sent_until_finished
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
        PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
        PNTCAS.client_no_tail_application_install_cover e13 e14)
      (ensures
        empty_sent_until_finished
          (CS.ConnNetworkEvent ({
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
           sent_finished_event cf ::
           [])
          cf)
=
  PCPS.lemma_client_no_tail_two_handshake_install_cover_cases e4 e5;
  PNTCAS.lemma_client_no_tail_application_install_cover_cases e13 e14;
  if PCPS.client_no_tail_handshake_write_install_event e4 then (
    lemma_handshake_install_event_empty_sent e4;
    lemma_handshake_install_event_empty_sent e5
  ) else (
    lemma_handshake_install_event_empty_sent e4;
    lemma_handshake_install_event_empty_sent e5
  );
  if PNTCAS.client_no_tail_application_write_install_event e13 then (
    lemma_application_install_event_empty_sent e13;
    lemma_application_install_event_empty_sent e14
  ) else (
    lemma_application_install_event_empty_sent e13;
    lemma_application_install_event_empty_sent e14
  );
  assert_norm (empty_sent_until_finished
    (CS.ConnNetworkEvent ({
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
     sent_finished_event cf ::
     [])
    cf)

let lemma_client_no_tail_finished_sent_raw_slices
  (client:CS.connection_state)
  : Lemma
      (requires
        PNTCAS.client_no_tail_finished_sent_shape client /\
        CS.connection_state_raw_event_replay_consistent client)
      (ensures client_sent_cleartext_and_finished_raw_slices client)
=
  eliminate exists start ch sh client_shared e4 e5 ee cert peer cv sf e13 e14 cf.
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
    PNTCAS.client_no_tail_application_install_cover e13 e14
  returns client_sent_cleartext_and_finished_raw_slices client
  with _.
  (
    let model0 = CS.initial_model client.CS.cs_model.CS.model_config in
    let ev0 = CS.ConnLocalEvent (CS.LocalStartHandshake start) in
    let ev1 = CS.ConnNetworkEvent ({
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    }) in
    let tail =
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
      sent_finished_event cf ::
      [] in
    assert (client.CS.cs_event_log == ev0 :: ev1 :: tail);
    assert (CS.conn_events_raw_replay
      model0
      (ev0 :: ev1 :: tail)
      client.CS.cs_wire_log.CL.raw_sent
      client.CS.cs_wire_log.CL.raw_received
      client.CS.cs_model);
    PWR.lemma_conn_events_raw_replay_head
      model0
      ev0
      (ev1 :: tail)
      client.CS.cs_wire_log.CL.raw_sent
      client.CS.cs_wire_log.CL.raw_received
      client.CS.cs_model;
    eliminate exists model1 delta0_sent delta0_received tail0_sent tail0_received.
      CS.legal_event model0 ev0 /\
      CS.step_model model0 ev0 == Some model1 /\
      CS.event_raw_delta_legal model0 ev0 delta0_sent delta0_received /\
      Seq.equal
        client.CS.cs_wire_log.CL.raw_sent
        (B.append delta0_sent tail0_sent) /\
      Seq.equal
        client.CS.cs_wire_log.CL.raw_received
        (B.append delta0_received tail0_received) /\
      CS.conn_events_raw_replay model1 (ev1 :: tail) tail0_sent tail0_received client.CS.cs_model
    returns client_sent_cleartext_and_finished_raw_slices client
    with _.
    (
      PWR.lemma_conn_events_raw_replay_head
        model1
        ev1
        tail
        tail0_sent
        tail0_received
        client.CS.cs_model;
      eliminate exists model2 delta1_sent delta1_received tail1_sent tail1_received.
        CS.legal_event model1 ev1 /\
        CS.step_model model1 ev1 == Some model2 /\
        CS.event_raw_delta_legal model1 ev1 delta1_sent delta1_received /\
        Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
        Seq.equal tail0_received (B.append delta1_received tail1_received) /\
        CS.conn_events_raw_replay model2 tail tail1_sent tail1_received client.CS.cs_model
      returns client_sent_cleartext_and_finished_raw_slices client
      with _.
      (
        lemma_event_raw_delta_legal_local
          model0
          (CS.LocalStartHandshake start)
          delta0_sent
          delta0_received;
        lemma_event_raw_delta_legal_sent_client_hello
          model1
          ch
          delta1_sent
          delta1_received;
        lemma_tail_empty_sent_until_finished
          sh
          client_shared
          e4
          e5
          ee
          cert
          peer
          cv
          sf
          e13
          e14
          cf;
        lemma_empty_sent_until_finished_raw_slice
          model2
          tail
          cf
          tail1_sent
          tail1_received
          client.CS.cs_model;
        eliminate exists finished_raw.
          Seq.equal tail1_sent finished_raw /\
          CS.raw_records_exactly finished_raw T.ApplicationData 1
        returns client_sent_cleartext_and_finished_raw_slices client
        with _.
        (
          Seq.lemma_eq_elim delta0_sent B.empty;
          CL.lemma_append_empty_left tail0_sent;
          assert (Seq.equal client.CS.cs_wire_log.CL.raw_sent tail0_sent);
          Seq.lemma_eq_elim tail0_sent (B.append delta1_sent tail1_sent);
          Seq.lemma_eq_elim tail1_sent finished_raw;
          assert (Seq.equal
            client.CS.cs_wire_log.CL.raw_sent
            (B.append delta1_sent finished_raw));
          assert (exists (ch0:M.client_hello) (cf0:M.finished) client_ch_raw client_finished_raw.
            Seq.equal
              client.CS.cs_wire_log.CL.raw_sent
              (B.append client_ch_raw client_finished_raw) /\
            CS.cleartext_tls_message_raw
              (M.TlsHandshake (M.ClientHello ch0))
              client_ch_raw /\
            CS.raw_records_exactly client_finished_raw T.ApplicationData 1)
        )
      )
    )
  )
