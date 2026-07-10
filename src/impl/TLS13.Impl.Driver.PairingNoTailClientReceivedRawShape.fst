module TLS13.Impl.Driver.PairingNoTailClientReceivedRawShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PWR = TLS13.ConnectionState.ProtectedWireReplay
module Seq = FStar.Seq
module T = TLS13.Types
module X = TLS13.X509.Spec

let event_has_empty_received_delta
  (ev:CS.conn_event)
  : Tot prop =
  match ev with
  | CS.ConnLocalEvent _ ->
    True
  | CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent

let lemma_event_raw_delta_legal_empty_received
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        event_has_empty_received_delta ev /\
        CS.event_raw_delta_legal model ev delta_sent delta_received)
      (ensures Seq.equal delta_received B.empty)
=
  match ev with
  | CS.ConnLocalEvent _ -> ()
  | CS.ConnNetworkEvent msg ->
    assert (msg.CL.message_direction == CL.Sent)

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

let lemma_event_raw_delta_legal_received_server_hello
  (model:CS.connection_model)
  (sh:M.server_hello)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.event_raw_delta_legal
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }))
          delta_sent
          delta_received)
      (ensures
        Seq.equal delta_sent B.empty /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello sh))
          delta_received)
=
  ()

let lemma_event_raw_delta_legal_received_encrypted_extensions
  (model:CS.connection_model)
  (ee:M.encrypted_extensions)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.event_raw_delta_legal
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
          }))
          delta_sent
          delta_received)
      (ensures
        Seq.equal delta_sent B.empty /\
        CS.raw_records_exactly delta_received T.Application_data 1)
=
  assert_norm (CS.network_message_is_cleartext
    CL.Received
    (M.TlsHandshake (M.EncryptedExtensions ee)) == false);
  assert_norm (CS.protected_record_count
    CL.Received
    (M.TlsHandshake (M.EncryptedExtensions ee)) == 1)

let lemma_event_raw_delta_legal_received_certificate
  (model:CS.connection_model)
  (cert:M.certificate_msg)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.event_raw_delta_legal
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Certificate cert);
          }))
          delta_sent
          delta_received)
      (ensures
        Seq.equal delta_sent B.empty /\
        CS.raw_records_exactly delta_received T.Application_data 1)
=
  assert_norm (CS.network_message_is_cleartext
    CL.Received
    (M.TlsHandshake (M.Certificate cert)) == false);
  assert_norm (CS.protected_record_count
    CL.Received
    (M.TlsHandshake (M.Certificate cert)) == 1)

let lemma_event_raw_delta_legal_received_certificate_verify
  (model:CS.connection_model)
  (cv:M.certificate_verify)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.event_raw_delta_legal
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
          }))
          delta_sent
          delta_received)
      (ensures
        Seq.equal delta_sent B.empty /\
        CS.raw_records_exactly delta_received T.Application_data 1)
=
  assert_norm (CS.network_message_is_cleartext
    CL.Received
    (M.TlsHandshake (M.CertificateVerify cv)) == false);
  assert_norm (CS.protected_record_count
    CL.Received
    (M.TlsHandshake (M.CertificateVerify cv)) == 1)

let lemma_event_raw_delta_legal_received_finished
  (model:CS.connection_model)
  (sf:M.finished)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.event_raw_delta_legal
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Finished sf);
          }))
          delta_sent
          delta_received)
      (ensures
        Seq.equal delta_sent B.empty /\
        CS.raw_records_exactly delta_received T.Application_data 1)
=
  assert_norm (CS.network_message_is_cleartext
    CL.Received
    (M.TlsHandshake (M.Finished sf)) == false);
  assert_norm (CS.protected_record_count
    CL.Received
    (M.TlsHandshake (M.Finished sf)) == 1)

let lemma_handshake_install_event_empty_received
  (ev:CS.conn_event)
  : Lemma
      (requires
        PCPS.client_no_tail_handshake_write_install_event ev \/
        PCPS.client_no_tail_handshake_read_install_event ev)
      (ensures event_has_empty_received_delta ev)
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

let lemma_application_install_event_empty_received
  (ev:CS.conn_event)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_write_install_event ev \/
        PNTCAS.client_no_tail_application_read_install_event ev)
      (ensures event_has_empty_received_delta ev)
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

let lemma_handshake_install_cover_empty_received
  (e4 e5:CS.conn_event)
  : Lemma
      (requires PCPS.client_no_tail_two_handshake_install_cover e4 e5)
      (ensures
        event_has_empty_received_delta e4 /\
        event_has_empty_received_delta e5)
=
  PCPS.lemma_client_no_tail_two_handshake_install_cover_cases e4 e5;
  if PCPS.client_no_tail_handshake_write_install_event e4 then (
    lemma_handshake_install_event_empty_received e4;
    lemma_handshake_install_event_empty_received e5
  ) else (
    lemma_handshake_install_event_empty_received e4;
    lemma_handshake_install_event_empty_received e5
  )

let lemma_application_install_cover_empty_received
  (e13 e14:CS.conn_event)
  : Lemma
      (requires PNTCAS.client_no_tail_application_install_cover e13 e14)
      (ensures
        event_has_empty_received_delta e13 /\
        event_has_empty_received_delta e14)
=
  PNTCAS.lemma_client_no_tail_application_install_cover_cases e13 e14;
  if PNTCAS.client_no_tail_application_write_install_event e13 then (
    lemma_application_install_event_empty_received e13;
    lemma_application_install_event_empty_received e14
  ) else (
    lemma_application_install_event_empty_received e13;
    lemma_application_install_event_empty_received e14
  )

let rec lemma_empty_received_suffix
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        (forall ev. FStar.List.Tot.mem ev events ==> event_has_empty_received_delta ev) /\
        CS.conn_events_raw_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (ensures Seq.equal raw_received B.empty)
      (decreases events)
=
  match events with
  | [] ->
    ()
  | ev :: rest ->
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
    returns Seq.equal raw_received B.empty
    with _.
    (
      assert (event_has_empty_received_delta ev);
      assert (forall ev0. FStar.List.Tot.mem ev0 rest ==> event_has_empty_received_delta ev0);
      lemma_event_raw_delta_legal_empty_received
        model
        ev
        delta_sent
        delta_received;
      lemma_empty_received_suffix
        model1
        rest
        tail_sent
        tail_received
        final_model;
      Seq.lemma_eq_elim delta_received B.empty;
      Seq.lemma_eq_elim tail_received B.empty;
      CL.lemma_append_empty_left tail_received;
      assert (Seq.equal raw_received B.empty)
    )

let lemma_conn_events_raw_replay_head_direct
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model1 delta_sent delta_received tail_sent tail_received.
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
            final_model)
=
  assert_norm (CS.conn_events_raw_replay
    model
    (ev :: rest)
    raw_sent
    raw_received
    final_model ==
    (exists model1 delta_sent delta_received tail_sent tail_received.
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
        final_model))

let lemma_two_events_all_empty_received
  (e0 e1:CS.conn_event)
  : Lemma
      (requires
        event_has_empty_received_delta e0 /\
        event_has_empty_received_delta e1)
      (ensures
        forall ev.
          FStar.List.Tot.mem ev (e0 :: e1 :: []) ==>
          event_has_empty_received_delta ev)
=
  ()

let lemma_local_event_empty_received
  (ev:CS.local_event)
  : Lemma (event_has_empty_received_delta (CS.ConnLocalEvent ev))
=
  ()

let lemma_sent_event_empty_received
  (msg:M.tls_message)
  : Lemma
      (event_has_empty_received_delta
        (CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = msg;
        })))
=
  ()

let lemma_four_events_all_empty_received
  (e0 e1 e2 e3:CS.conn_event)
  : Lemma
      (requires
        event_has_empty_received_delta e0 /\
        event_has_empty_received_delta e1 /\
        event_has_empty_received_delta e2 /\
        event_has_empty_received_delta e3)
      (ensures
        forall ev.
          FStar.List.Tot.mem ev (e0 :: e1 :: e2 :: e3 :: []) ==>
          event_has_empty_received_delta ev)
=
  ()

let lemma_raw_replay_step_local_event
  (model:CS.connection_model)
  (lev:CS.local_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model
          (CS.ConnLocalEvent lev :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model' tail_sent.
          CS.conn_events_raw_replay model' rest tail_sent raw_received final_model)
=
  let ev = CS.ConnLocalEvent lev in
  lemma_conn_events_raw_replay_head_direct model ev rest raw_sent raw_received final_model;
  eliminate exists model' delta_sent delta_received tail_sent tail_received.
    CS.legal_event model ev /\
    CS.step_model model ev == Some model' /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    CS.conn_events_raw_replay model' rest tail_sent tail_received final_model
  returns
    exists model'' tail_sent'.
      CS.conn_events_raw_replay model'' rest tail_sent' raw_received final_model
  with _.
  (
    lemma_event_raw_delta_legal_local model lev delta_sent delta_received;
    Seq.lemma_eq_elim delta_received B.empty;
    CL.lemma_append_empty_left tail_received;
    assert (Seq.equal raw_received tail_received);
    Seq.lemma_eq_elim raw_received tail_received;
    assert (exists model'' tail_sent'.
      CS.conn_events_raw_replay model'' rest tail_sent' raw_received final_model)
  )

let lemma_raw_replay_step_two_local_install_events
  (model:CS.connection_model)
  (e4 e5:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
        CS.conn_events_raw_replay model (e4 :: e5 :: rest) raw_sent raw_received final_model)
      (ensures
        exists model' tail_sent.
          CS.conn_events_raw_replay model' rest tail_sent raw_received final_model)
=
  lemma_handshake_install_cover_empty_received e4 e5;
  let install_events = e4 :: e5 :: [] in
  assert_norm (FStar.List.Tot.append install_events rest == e4 :: e5 :: rest);
  PWR.lemma_conn_events_raw_replay_append_split
    model
    install_events
    rest
    raw_sent
    raw_received
    final_model;
  eliminate exists model' install_sent install_received tail_sent tail_received.
    Seq.equal raw_sent (B.append install_sent tail_sent) /\
    Seq.equal raw_received (B.append install_received tail_received) /\
    CS.conn_events_raw_replay model install_events install_sent install_received model' /\
    CS.conn_events_raw_replay model' rest tail_sent tail_received final_model
  returns
    exists model'' tail_sent'.
      CS.conn_events_raw_replay model'' rest tail_sent' raw_received final_model
  with _.
  (
    lemma_two_events_all_empty_received e4 e5;
    lemma_empty_received_suffix
      model
      install_events
      install_sent
      install_received
      model';
    Seq.lemma_eq_elim install_received B.empty;
    CL.lemma_append_empty_left tail_received;
    assert (Seq.equal raw_received tail_received);
    Seq.lemma_eq_elim raw_received tail_received;
    assert (exists model'' tail_sent'.
      CS.conn_events_raw_replay model'' rest tail_sent' raw_received final_model)
  )

let lemma_raw_replay_step_received_encrypted_extensions
  (model:CS.connection_model)
  (ee:M.encrypted_extensions)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
          }) :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model' chunk tail_sent tail_received.
          Seq.equal raw_received (B.append chunk tail_received) /\
          CS.raw_records_exactly chunk T.Application_data 1 /\
          CS.conn_events_raw_replay model' rest tail_sent tail_received final_model)
=
  let ev = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
  }) in
  lemma_conn_events_raw_replay_head_direct model ev rest raw_sent raw_received final_model;
  eliminate exists model' delta_sent delta_received tail_sent tail_received.
    CS.legal_event model ev /\
    CS.step_model model ev == Some model' /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    CS.conn_events_raw_replay model' rest tail_sent tail_received final_model
  returns
    exists model'' chunk tail_sent' tail_received'.
      Seq.equal raw_received (B.append chunk tail_received') /\
      CS.raw_records_exactly chunk T.Application_data 1 /\
      CS.conn_events_raw_replay model'' rest tail_sent' tail_received' final_model
  with _.
  (
    lemma_event_raw_delta_legal_received_encrypted_extensions model ee delta_sent delta_received;
    assert (exists model'' chunk tail_sent' tail_received'.
      Seq.equal raw_received (B.append chunk tail_received') /\
      CS.raw_records_exactly chunk T.Application_data 1 /\
      CS.conn_events_raw_replay model'' rest tail_sent' tail_received' final_model)
  )

let lemma_raw_replay_step_received_certificate
  (model:CS.connection_model)
  (cert:M.certificate_msg)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Certificate cert);
          }) :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model' chunk tail_sent tail_received.
          Seq.equal raw_received (B.append chunk tail_received) /\
          CS.raw_records_exactly chunk T.Application_data 1 /\
          CS.conn_events_raw_replay model' rest tail_sent tail_received final_model)
=
  let ev = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.Certificate cert);
  }) in
  lemma_conn_events_raw_replay_head_direct model ev rest raw_sent raw_received final_model;
  eliminate exists model' delta_sent delta_received tail_sent tail_received.
    CS.legal_event model ev /\
    CS.step_model model ev == Some model' /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    CS.conn_events_raw_replay model' rest tail_sent tail_received final_model
  returns
    exists model'' chunk tail_sent' tail_received'.
      Seq.equal raw_received (B.append chunk tail_received') /\
      CS.raw_records_exactly chunk T.Application_data 1 /\
      CS.conn_events_raw_replay model'' rest tail_sent' tail_received' final_model
  with _.
  (
    lemma_event_raw_delta_legal_received_certificate model cert delta_sent delta_received;
    assert (exists model'' chunk tail_sent' tail_received'.
      Seq.equal raw_received (B.append chunk tail_received') /\
      CS.raw_records_exactly chunk T.Application_data 1 /\
      CS.conn_events_raw_replay model'' rest tail_sent' tail_received' final_model)
  )

let lemma_raw_replay_step_received_certificate_verify
  (model:CS.connection_model)
  (cv:M.certificate_verify)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
          }) :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model' chunk tail_sent tail_received.
          Seq.equal raw_received (B.append chunk tail_received) /\
          CS.raw_records_exactly chunk T.Application_data 1 /\
          CS.conn_events_raw_replay model' rest tail_sent tail_received final_model)
=
  let ev = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
  }) in
  lemma_conn_events_raw_replay_head_direct model ev rest raw_sent raw_received final_model;
  eliminate exists model' delta_sent delta_received tail_sent tail_received.
    CS.legal_event model ev /\
    CS.step_model model ev == Some model' /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    CS.conn_events_raw_replay model' rest tail_sent tail_received final_model
  returns
    exists model'' chunk tail_sent' tail_received'.
      Seq.equal raw_received (B.append chunk tail_received') /\
      CS.raw_records_exactly chunk T.Application_data 1 /\
      CS.conn_events_raw_replay model'' rest tail_sent' tail_received' final_model
  with _.
  (
    lemma_event_raw_delta_legal_received_certificate_verify model cv delta_sent delta_received;
    assert (exists model'' chunk tail_sent' tail_received'.
      Seq.equal raw_received (B.append chunk tail_received') /\
      CS.raw_records_exactly chunk T.Application_data 1 /\
      CS.conn_events_raw_replay model'' rest tail_sent' tail_received' final_model)
  )

let lemma_raw_replay_step_received_finished
  (model:CS.connection_model)
  (sf:M.finished)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Finished sf);
          }) :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model' chunk tail_sent tail_received.
          Seq.equal raw_received (B.append chunk tail_received) /\
          CS.raw_records_exactly chunk T.Application_data 1 /\
          CS.conn_events_raw_replay model' rest tail_sent tail_received final_model)
=
  let ev = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.Finished sf);
  }) in
  lemma_conn_events_raw_replay_head_direct model ev rest raw_sent raw_received final_model;
  eliminate exists model' delta_sent delta_received tail_sent tail_received.
    CS.legal_event model ev /\
    CS.step_model model ev == Some model' /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    CS.conn_events_raw_replay model' rest tail_sent tail_received final_model
  returns
    exists model'' chunk tail_sent' tail_received'.
      Seq.equal raw_received (B.append chunk tail_received') /\
      CS.raw_records_exactly chunk T.Application_data 1 /\
      CS.conn_events_raw_replay model'' rest tail_sent' tail_received' final_model
  with _.
  (
    lemma_event_raw_delta_legal_received_finished model sf delta_sent delta_received;
    assert (exists model'' chunk tail_sent' tail_received'.
      Seq.equal raw_received (B.append chunk tail_received') /\
      CS.raw_records_exactly chunk T.Application_data 1 /\
      CS.conn_events_raw_replay model'' rest tail_sent' tail_received' final_model)
  )

let lemma_server_flight_message_tail_slices
  (model6:CS.connection_model)
  (ee:M.encrypted_extensions)
  (cert:M.certificate_msg)
  (peer:X.peer_identity)
  (cv:M.certificate_verify)
  (sf:M.finished)
  (e13 e14:CS.conn_event)
  (cf:M.finished)
  (tail5_sent:B.bytes)
  (tail5_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_install_cover e13 e14 /\
        CS.conn_events_raw_replay
          model6
          (CS.ConnNetworkEvent ({
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
           [])
          tail5_sent
          tail5_received
          final_model)
      (ensures
        exists ee_raw cert_raw cv_raw sf_raw.
          Seq.equal
            tail5_received
            (B.append ee_raw (B.append cert_raw (B.append cv_raw sf_raw))) /\
          CS.raw_records_exactly ee_raw T.Application_data 1 /\
          CS.raw_records_exactly cert_raw T.Application_data 1 /\
          CS.raw_records_exactly cv_raw T.Application_data 1 /\
          CS.raw_records_exactly sf_raw T.Application_data 1)
=
  let ev7 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.Certificate cert);
  }) in
  let ev9 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
  }) in
  let ev11 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.Finished sf);
  }) in
  let ev12 = CS.ConnLocalEvent (CS.LocalVerifyFinished sf) in
  let ev15 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.Finished cf);
  }) in
  let suffix = ev12 :: e13 :: e14 :: ev15 :: [] in
  lemma_raw_replay_step_received_encrypted_extensions
    model6
    ee
    (ev7 :: CS.ConnLocalEvent (CS.LocalValidateCertificate peer) :: ev9 ::
     CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) :: ev11 :: suffix)
    tail5_sent
    tail5_received
    final_model;
  eliminate exists model7 ee_raw tail6_sent tail6_received.
    Seq.equal tail5_received (B.append ee_raw tail6_received) /\
    CS.raw_records_exactly ee_raw T.Application_data 1 /\
    CS.conn_events_raw_replay
      model7
      (ev7 :: CS.ConnLocalEvent (CS.LocalValidateCertificate peer) :: ev9 ::
       CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) :: ev11 :: suffix)
      tail6_sent
      tail6_received
      final_model
  returns
    exists ee_raw' cert_raw cv_raw sf_raw.
      Seq.equal
        tail5_received
        (B.append ee_raw' (B.append cert_raw (B.append cv_raw sf_raw))) /\
      CS.raw_records_exactly ee_raw' T.Application_data 1 /\
      CS.raw_records_exactly cert_raw T.Application_data 1 /\
      CS.raw_records_exactly cv_raw T.Application_data 1 /\
      CS.raw_records_exactly sf_raw T.Application_data 1
  with _.
  (
    lemma_raw_replay_step_received_certificate
      model7
      cert
      (CS.ConnLocalEvent (CS.LocalValidateCertificate peer) :: ev9 ::
       CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) :: ev11 :: suffix)
      tail6_sent
      tail6_received
      final_model;
    eliminate exists model8 cert_raw tail7_sent tail7_received.
      Seq.equal tail6_received (B.append cert_raw tail7_received) /\
      CS.raw_records_exactly cert_raw T.Application_data 1 /\
      CS.conn_events_raw_replay
        model8
        (CS.ConnLocalEvent (CS.LocalValidateCertificate peer) :: ev9 ::
         CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) :: ev11 :: suffix)
        tail7_sent
        tail7_received
        final_model
    returns
      exists ee_raw' cert_raw' cv_raw sf_raw.
        Seq.equal
          tail5_received
          (B.append ee_raw' (B.append cert_raw' (B.append cv_raw sf_raw))) /\
        CS.raw_records_exactly ee_raw' T.Application_data 1 /\
        CS.raw_records_exactly cert_raw' T.Application_data 1 /\
        CS.raw_records_exactly cv_raw T.Application_data 1 /\
        CS.raw_records_exactly sf_raw T.Application_data 1
    with _.
    (
      lemma_raw_replay_step_local_event
        model8
        (CS.LocalValidateCertificate peer)
        (ev9 :: CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) :: ev11 :: suffix)
        tail7_sent
        tail7_received
        final_model;
      eliminate exists model9 tail8_sent.
        CS.conn_events_raw_replay
          model9
          (ev9 :: CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) :: ev11 :: suffix)
          tail8_sent
          tail7_received
          final_model
      returns
        exists ee_raw' cert_raw' cv_raw sf_raw.
          Seq.equal
            tail5_received
            (B.append ee_raw' (B.append cert_raw' (B.append cv_raw sf_raw))) /\
          CS.raw_records_exactly ee_raw' T.Application_data 1 /\
          CS.raw_records_exactly cert_raw' T.Application_data 1 /\
          CS.raw_records_exactly cv_raw T.Application_data 1 /\
          CS.raw_records_exactly sf_raw T.Application_data 1
      with _.
      (
        lemma_raw_replay_step_received_certificate_verify
          model9
          cv
          (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) :: ev11 :: suffix)
          tail8_sent
          tail7_received
          final_model;
        eliminate exists model10 cv_raw tail9_sent tail9_received.
          Seq.equal tail7_received (B.append cv_raw tail9_received) /\
          CS.raw_records_exactly cv_raw T.Application_data 1 /\
          CS.conn_events_raw_replay
            model10
            (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) :: ev11 :: suffix)
            tail9_sent
            tail9_received
            final_model
        returns
          exists ee_raw' cert_raw' cv_raw' sf_raw.
            Seq.equal
              tail5_received
              (B.append ee_raw' (B.append cert_raw' (B.append cv_raw' sf_raw))) /\
            CS.raw_records_exactly ee_raw' T.Application_data 1 /\
            CS.raw_records_exactly cert_raw' T.Application_data 1 /\
            CS.raw_records_exactly cv_raw' T.Application_data 1 /\
            CS.raw_records_exactly sf_raw T.Application_data 1
        with _.
        (
          lemma_raw_replay_step_local_event
            model10
            (CS.LocalVerifyCertificateSignature cv)
            (ev11 :: suffix)
            tail9_sent
            tail9_received
            final_model;
          eliminate exists model11 tail10_sent.
            CS.conn_events_raw_replay
              model11
              (ev11 :: suffix)
              tail10_sent
              tail9_received
              final_model
          returns
            exists ee_raw' cert_raw' cv_raw' sf_raw.
              Seq.equal
                tail5_received
                (B.append ee_raw' (B.append cert_raw' (B.append cv_raw' sf_raw))) /\
              CS.raw_records_exactly ee_raw' T.Application_data 1 /\
              CS.raw_records_exactly cert_raw' T.Application_data 1 /\
              CS.raw_records_exactly cv_raw' T.Application_data 1 /\
              CS.raw_records_exactly sf_raw T.Application_data 1
          with _.
          (
            lemma_raw_replay_step_received_finished
              model11
              sf
              suffix
              tail10_sent
              tail9_received
              final_model;
            eliminate exists model12 sf_raw tail11_sent tail11_received.
              Seq.equal tail9_received (B.append sf_raw tail11_received) /\
              CS.raw_records_exactly sf_raw T.Application_data 1 /\
              CS.conn_events_raw_replay model12 suffix tail11_sent tail11_received final_model
            returns
              exists ee_raw' cert_raw' cv_raw' sf_raw'.
                Seq.equal
                  tail5_received
                  (B.append ee_raw' (B.append cert_raw' (B.append cv_raw' sf_raw'))) /\
                CS.raw_records_exactly ee_raw' T.Application_data 1 /\
                CS.raw_records_exactly cert_raw' T.Application_data 1 /\
                CS.raw_records_exactly cv_raw' T.Application_data 1 /\
                CS.raw_records_exactly sf_raw' T.Application_data 1
            with _.
            (
              lemma_local_event_empty_received (CS.LocalVerifyFinished sf);
              lemma_sent_event_empty_received (M.TlsHandshake (M.Finished cf));
              lemma_application_install_cover_empty_received e13 e14;
              lemma_four_events_all_empty_received ev12 e13 e14 ev15;
              lemma_empty_received_suffix model12 suffix tail11_sent tail11_received final_model;
              Seq.lemma_eq_elim tail11_received B.empty;
              CL.lemma_append_empty_right sf_raw;
              Seq.lemma_eq_elim tail9_received (B.append sf_raw tail11_received);
              Seq.lemma_eq_elim tail7_received (B.append cv_raw tail9_received);
              Seq.lemma_eq_elim tail6_received (B.append cert_raw tail7_received);
              Seq.lemma_eq_elim tail5_received (B.append ee_raw tail6_received);
              assert (Seq.equal
                tail5_received
                (B.append ee_raw (B.append cert_raw (B.append cv_raw sf_raw))))
            )
          )
        )
      )
    )
  )

let lemma_client_no_tail_server_flight_received_raw_slices_for_shape
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
 =
  lemma_handshake_install_cover_empty_received e4 e5;
  lemma_application_install_cover_empty_received e13 e14;
  let model0 = CS.initial_model client.CS.cs_model.CS.model_config in
  let ev0 = CS.ConnLocalEvent (CS.LocalStartHandshake start) in
  let ev1 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ClientHello ch);
  }) in
  let ev2 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  }) in
  let ev3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) in
  let ev6 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
  }) in
  let ev7 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.Certificate cert);
  }) in
  let ev8 = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
  let ev9 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
  }) in
  let ev10 = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
  let ev11 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.Finished sf);
  }) in
  let ev12 = CS.ConnLocalEvent (CS.LocalVerifyFinished sf) in
  let ev15 = CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.Finished cf);
  }) in
  let suffix = ev12 :: e13 :: e14 :: ev15 :: [] in
  let tail =
    ev3 ::
    e4 ::
    e5 ::
    ev6 ::
    ev7 ::
    ev8 ::
    ev9 ::
    ev10 ::
    ev11 ::
    suffix in
  assert (client.CS.cs_event_log == ev0 :: ev1 :: ev2 :: tail);
  assert (CS.conn_events_raw_replay
    model0
    (ev0 :: ev1 :: ev2 :: tail)
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model);
  lemma_conn_events_raw_replay_head_direct
    model0
    ev0
    (ev1 :: ev2 :: tail)
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
    CS.conn_events_raw_replay
      model1
      (ev1 :: ev2 :: tail)
      tail0_sent
      tail0_received
      client.CS.cs_model
  returns
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
      CS.raw_records_exactly sf_raw T.Application_data 1
  with _.
  (
    lemma_conn_events_raw_replay_head_direct
      model1
      ev1
      (ev2 :: tail)
      tail0_sent
      tail0_received
      client.CS.cs_model;
    eliminate exists model2 delta1_sent delta1_received tail1_sent tail1_received.
      CS.legal_event model1 ev1 /\
      CS.step_model model1 ev1 == Some model2 /\
      CS.event_raw_delta_legal model1 ev1 delta1_sent delta1_received /\
      Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
      Seq.equal tail0_received (B.append delta1_received tail1_received) /\
      CS.conn_events_raw_replay
        model2
        (ev2 :: tail)
        tail1_sent
        tail1_received
        client.CS.cs_model
    returns
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
        CS.raw_records_exactly sf_raw T.Application_data 1
    with _.
    (
      lemma_conn_events_raw_replay_head_direct
        model2
        ev2
        tail
        tail1_sent
        tail1_received
        client.CS.cs_model;
      eliminate exists model3 delta2_sent delta2_received tail2_sent tail2_received.
        CS.legal_event model2 ev2 /\
        CS.step_model model2 ev2 == Some model3 /\
        CS.event_raw_delta_legal model2 ev2 delta2_sent delta2_received /\
        Seq.equal tail1_sent (B.append delta2_sent tail2_sent) /\
        Seq.equal tail1_received (B.append delta2_received tail2_received) /\
        CS.conn_events_raw_replay
          model3
          tail
          tail2_sent
          tail2_received
          client.CS.cs_model
      returns
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
          CS.raw_records_exactly sf_raw T.Application_data 1
      with _.
      (
        lemma_conn_events_raw_replay_head_direct
          model3
          ev3
          (e4 :: e5 :: ev6 :: ev7 :: ev8 :: ev9 :: ev10 :: ev11 :: suffix)
          tail2_sent
          tail2_received
          client.CS.cs_model;
        eliminate exists model4 delta3_sent delta3_received tail3_sent tail3_received.
          CS.legal_event model3 ev3 /\
          CS.step_model model3 ev3 == Some model4 /\
          CS.event_raw_delta_legal model3 ev3 delta3_sent delta3_received /\
          Seq.equal tail2_sent (B.append delta3_sent tail3_sent) /\
          Seq.equal tail2_received (B.append delta3_received tail3_received) /\
          CS.conn_events_raw_replay
            model4
            (e4 :: e5 :: ev6 :: ev7 :: ev8 :: ev9 :: ev10 :: ev11 :: suffix)
            tail3_sent
            tail3_received
            client.CS.cs_model
        returns
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
            CS.raw_records_exactly sf_raw T.Application_data 1
        with _.
        (
          lemma_event_raw_delta_legal_local
            model0
            (CS.LocalStartHandshake start)
            delta0_sent
            delta0_received;
          lemma_event_raw_delta_legal_empty_received
            model1
            ev1
            delta1_sent
            delta1_received;
          lemma_event_raw_delta_legal_received_server_hello
            model2
            sh
            delta2_sent
            delta2_received;
          lemma_event_raw_delta_legal_local
            model3
            (CS.LocalDeriveSharedSecret client_shared)
            delta3_sent
            delta3_received;
          lemma_raw_replay_step_two_local_install_events
            model4
            e4
            e5
            (ev6 :: ev7 :: ev8 :: ev9 :: ev10 :: ev11 :: suffix)
            tail3_sent
            tail3_received
            client.CS.cs_model;
          eliminate exists model6 tail5_sent.
            CS.conn_events_raw_replay
              model6
              (ev6 :: ev7 :: ev8 :: ev9 :: ev10 :: ev11 :: suffix)
              tail5_sent
              tail3_received
              client.CS.cs_model
          returns
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
              CS.raw_records_exactly sf_raw T.Application_data 1
          with _.
          (
            lemma_server_flight_message_tail_slices
              model6
              ee
              cert
              peer
              cv
              sf
              e13
              e14
              cf
              tail5_sent
              tail3_received
              client.CS.cs_model;
            eliminate exists ee_raw cert_raw cv_raw sf_raw.
              Seq.equal
                tail3_received
                (B.append ee_raw (B.append cert_raw (B.append cv_raw sf_raw))) /\
              CS.raw_records_exactly ee_raw T.Application_data 1 /\
              CS.raw_records_exactly cert_raw T.Application_data 1 /\
              CS.raw_records_exactly cv_raw T.Application_data 1 /\
              CS.raw_records_exactly sf_raw T.Application_data 1
            returns
              exists server_sh_raw ee_raw' cert_raw' cv_raw' sf_raw'.
                Seq.equal
                  client.CS.cs_wire_log.CL.raw_received
                  (B.append
                    server_sh_raw
                    (B.append ee_raw' (B.append cert_raw' (B.append cv_raw' sf_raw')))) /\
                CS.received_cleartext_tls_message_raw
                  (M.TlsHandshake (M.ServerHello sh))
                  server_sh_raw /\
                CS.raw_records_exactly ee_raw' T.Application_data 1 /\
                CS.raw_records_exactly cert_raw' T.Application_data 1 /\
                CS.raw_records_exactly cv_raw' T.Application_data 1 /\
                CS.raw_records_exactly sf_raw' T.Application_data 1
            with _.
            (
              Seq.lemma_eq_elim delta0_received B.empty;
              Seq.lemma_eq_elim delta1_received B.empty;
              Seq.lemma_eq_elim delta3_received B.empty;
              Seq.lemma_eq_elim
                tail3_received
                (B.append ee_raw (B.append cert_raw (B.append cv_raw sf_raw)));
              Seq.lemma_eq_elim tail2_received (B.append delta3_received tail3_received);
              CL.lemma_append_empty_left
                (B.append ee_raw (B.append cert_raw (B.append cv_raw sf_raw)));
              Seq.lemma_eq_elim tail1_received (B.append delta2_received tail2_received);
              Seq.lemma_eq_elim tail0_received (B.append delta1_received tail1_received);
              CL.lemma_append_empty_left
                (B.append
                  delta2_received
                  (B.append ee_raw (B.append cert_raw (B.append cv_raw sf_raw))));
              Seq.lemma_eq_elim
                client.CS.cs_wire_log.CL.raw_received
                (B.append delta0_received tail0_received);
              assert (Seq.equal
                client.CS.cs_wire_log.CL.raw_received
                (B.append
                  delta2_received
                  (B.append ee_raw (B.append cert_raw (B.append cv_raw sf_raw)))));
              assert (exists server_sh_raw ee_raw' cert_raw' cv_raw' sf_raw'.
                Seq.equal
                  client.CS.cs_wire_log.CL.raw_received
                  (B.append
                    server_sh_raw
                    (B.append ee_raw' (B.append cert_raw' (B.append cv_raw' sf_raw')))) /\
                CS.received_cleartext_tls_message_raw
                  (M.TlsHandshake (M.ServerHello sh))
                  server_sh_raw /\
                CS.raw_records_exactly ee_raw' T.Application_data 1 /\
                CS.raw_records_exactly cert_raw' T.Application_data 1 /\
                CS.raw_records_exactly cv_raw' T.Application_data 1 /\
                CS.raw_records_exactly sf_raw' T.Application_data 1)
            )
          )
        )
        )
      )
    )
let lemma_client_no_tail_server_flight_received_raw_slices
    (client:CS.connection_state)
  : Lemma
    (requires
      PNTCAS.client_no_tail_finished_sent_shape client /\
      CS.connection_state_raw_event_replay_consistent client)
    (ensures client_received_cleartext_and_server_flight_raw_slices client)
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
  returns client_received_cleartext_and_server_flight_raw_slices client
  with _.
  (
  lemma_client_no_tail_server_flight_received_raw_slices_for_shape
    client
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
    e13
    e14
    cf;
  eliminate exists server_sh_raw ee_raw cert_raw cv_raw sf_raw.
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
  returns client_received_cleartext_and_server_flight_raw_slices client
  with _.
  (
    assert (exists
      (sh0:M.server_hello)
      (ee0:M.encrypted_extensions)
      (cert0:M.certificate_msg)
      (cv0:M.certificate_verify)
      (sf0:M.finished)
      server_sh_raw0
      ee_raw0
      cert_raw0
      cv_raw0
      sf_raw0.
      Seq.equal
        client.CS.cs_wire_log.CL.raw_received
        (B.append
          server_sh_raw0
          (B.append ee_raw0 (B.append cert_raw0 (B.append cv_raw0 sf_raw0)))) /\
      CS.received_cleartext_tls_message_raw
        (M.TlsHandshake (M.ServerHello sh0))
        server_sh_raw0 /\
      CS.raw_records_exactly ee_raw0 T.Application_data 1 /\
      CS.raw_records_exactly cert_raw0 T.Application_data 1 /\
      CS.raw_records_exactly cv_raw0 T.Application_data 1 /\
      CS.raw_records_exactly sf_raw0 T.Application_data 1)
  )
  )
