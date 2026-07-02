module TLS13.ConnectionState.ProtectedWireLemmas

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CSL = TLS13.ConnectionState.Lemmas
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas
module WRT = TLS13.Wire.Spec.Reveal.FinishedRoundTrip

open TLS13.Spec.ConnectionState

#push-options "--split_queries always --z3rlimit 10"
let lemma_protected_handshake_wire_equal_from_sent_seal_peer
  (sender:connection_model)
  (receiver:connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (raw:B.bytes)
  : Lemma
      (requires
        sender.model_record.record_write.R.seq ==
          receiver.model_record.record_read.R.seq /\
        (match
          record_direction_material sender.model_record.record_write,
          record_direction_material receiver.model_record.record_read
        with
        | Some sender_write, Some receiver_read ->
          record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        sent_single_protected_message_seal
          sender
          (M.TlsHandshake sent_msg)
          raw /\
        received_single_protected_message_decode
          receiver
          (M.TlsHandshake received_msg)
          raw /\
        protected_handshake_wire_round_trip_message received_msg)
      (ensures
        Seq.equal
          (W.serialize_handshake sent_msg)
          (W.serialize_handshake received_msg))
=
  let sent_tls_msg = M.TlsHandshake sent_msg in
  CSL.lemma_received_record_opened_from_sent_single_protected_message_seal_peer
    sender
    receiver
    sent_tls_msg
    raw;
  eliminate exists (sent_outer:B.bytes).
    W.parse_record raw == Some (T.ApplicationData, sent_outer, B.length raw) /\
    received_record_opened
      receiver
      raw
      sent_outer
      (sent_tls_inner_plaintext_fragment sent_tls_msg)
  returns
    Seq.equal
      (W.serialize_handshake sent_msg)
      (W.serialize_handshake received_msg)
  with _.
  ( eliminate exists
      (received_outer:B.bytes)
      (opened:B.bytes)
      (plaintext:M.plaintext).
      W.parse_record_wire raw ==
        Some (T.ApplicationData, received_outer, B.length raw) /\
      received_record_opened receiver raw received_outer opened /\
      W.parse_plaintext opened == Some plaintext /\
      W.parse_tls_message plaintext.M.content_type plaintext.M.fragment ==
        Some (M.TlsHandshake received_msg)
    returns
      Seq.equal
        (W.serialize_handshake sent_msg)
        (W.serialize_handshake received_msg)
    with _.
    ( W.lemma_parse_record_implies_parse_record_wire raw;
      assert (received_outer == sent_outer);
      eliminate exists (sent_read_state':R.direction_state).
        R.open_record
          receiver.model_record.record_read
          (record_header_aad raw)
          sent_outer ==
          Some (sent_tls_inner_plaintext_fragment sent_tls_msg, sent_read_state')
      returns
        Seq.equal
          (W.serialize_handshake sent_msg)
          (W.serialize_handshake received_msg)
      with _.
      ( eliminate exists (received_read_state':R.direction_state).
          R.open_record
            receiver.model_record.record_read
            (record_header_aad raw)
            received_outer ==
            Some (opened, received_read_state')
        returns
          Seq.equal
            (W.serialize_handshake sent_msg)
            (W.serialize_handshake received_msg)
        with _.
        ( assert (opened == sent_tls_inner_plaintext_fragment sent_tls_msg);
          W.lemma_serialize_tls_message_handshake sent_msg;
          let sent_plaintext = {
            M.content_type = T.Handshake;
            M.fragment = W.serialize_handshake sent_msg;
          } in
          assert (sent_tls_inner_plaintext_fragment sent_tls_msg ==
                  W.serialize_plaintext sent_plaintext);
          W.lemma_parse_plaintext_serialize_plaintext sent_plaintext;
          assert (W.parse_plaintext
            (sent_tls_inner_plaintext_fragment sent_tls_msg) ==
            Some sent_plaintext);
          assert (plaintext == sent_plaintext);
          assert (W.parse_tls_message
            T.Handshake
            (W.serialize_handshake sent_msg) ==
            Some (M.TlsHandshake received_msg));
          match received_msg with
          | M.EncryptedExtensions _
          | M.Certificate _
          | M.CertificateVerify _ ->
            W.lemma_parse_tls_message_round_trip
              T.Handshake
              (W.serialize_handshake sent_msg)
          | M.Finished fin ->
            WRT.lemma_parse_finished_handshake_round_trip
              (W.serialize_handshake sent_msg)
              fin
          | _ ->
            assert False ) ) ) )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_protected_handshake_wire_equal_from_event_projections_peer
  (sender:connection_model)
  (receiver:connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires
        sender.model_record.record_write.R.seq ==
          receiver.model_record.record_read.R.seq /\
        (match
          record_direction_material sender.model_record.record_write,
          record_direction_material receiver.model_record.record_read
        with
        | Some sender_write, Some receiver_read ->
          record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal raw_sent raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        sent_event_seal_projection
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          raw_sent /\
        received_event_decode_projection
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          })
          raw_received)
      (ensures
        Seq.equal
          (W.serialize_handshake sent_msg)
          (W.serialize_handshake received_msg))
=
  match sent_msg, received_msg with
  | M.EncryptedExtensions _, M.EncryptedExtensions _
  | M.EncryptedExtensions _, M.Certificate _
  | M.EncryptedExtensions _, M.CertificateVerify _
  | M.EncryptedExtensions _, M.Finished _
  | M.Certificate _, M.EncryptedExtensions _
  | M.Certificate _, M.Certificate _
  | M.Certificate _, M.CertificateVerify _
  | M.Certificate _, M.Finished _
  | M.CertificateVerify _, M.EncryptedExtensions _
  | M.CertificateVerify _, M.Certificate _
  | M.CertificateVerify _, M.CertificateVerify _
  | M.CertificateVerify _, M.Finished _
  | M.Finished _, M.EncryptedExtensions _
  | M.Finished _, M.Certificate _
  | M.Finished _, M.CertificateVerify _
  | M.Finished _, M.Finished _ ->
    assert (network_message_is_cleartext CL.Sent (M.TlsHandshake sent_msg) == false);
    assert (network_message_is_cleartext CL.Received (M.TlsHandshake received_msg) == false);
    assert (protected_record_count CL.Sent (M.TlsHandshake sent_msg) == 1);
    assert (protected_record_count CL.Received (M.TlsHandshake received_msg) == 1);
    assert (sent_single_protected_message_seal
      sender
      (M.TlsHandshake sent_msg)
      raw_sent);
    assert (received_single_protected_message_decode
      receiver
      (M.TlsHandshake received_msg)
      raw_received);
    Seq.lemma_eq_elim raw_sent raw_received;
    assert (received_single_protected_message_decode
      receiver
      (M.TlsHandshake received_msg)
      raw_sent);
    lemma_protected_handshake_wire_equal_from_sent_seal_peer
      sender
      receiver
      sent_msg
      received_msg
      raw_sent
  | _, _ ->
    assert False
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_paired_protected_handshake_wire_equivalent_from_event_projection_pairs
  (client:connection_state)
  (server:connection_state)
  (server_ee:protected_message_replay)
  (server_cert:protected_message_replay)
  (server_cv:protected_message_replay)
  (server_finished:protected_message_replay)
  (client_finished:protected_message_replay)
  : Lemma
      (requires
        paired_protected_handshake_event_projection_pairs
          client
          server
          server_ee
          server_cert
          server_cv
          server_finished
          client_finished)
      (ensures WFL.paired_protected_handshake_wire_equivalent client server)
=
  let client_hs = client.cs_model.model_handshake in
  let server_hs = server.cs_model.model_handshake in
  match
    client_hs.hs_encrypted_extensions,
    server_hs.hs_encrypted_extensions,
    client_hs.hs_certificate,
    server_hs.hs_certificate,
    client_hs.hs_certificate_verify,
    server_hs.hs_certificate_verify,
    client_hs.hs_server_finished,
    server_hs.hs_server_finished,
    client_hs.hs_client_finished,
    server_hs.hs_client_finished
  with
  | Some client_ee, Some server_ee_msg,
    Some client_cert, Some server_cert_msg,
    Some client_cv, Some server_cv_msg,
    Some client_sf, Some server_sf,
    Some client_cf, Some server_cf ->
    lemma_protected_handshake_wire_equal_from_event_projections_peer
      server_ee.pm_sender
      server_ee.pm_receiver
      (M.EncryptedExtensions server_ee_msg)
      (M.EncryptedExtensions client_ee)
      server_ee.pm_raw_sent
      server_ee.pm_raw_received;
    lemma_protected_handshake_wire_equal_from_event_projections_peer
      server_cert.pm_sender
      server_cert.pm_receiver
      (M.Certificate server_cert_msg)
      (M.Certificate client_cert)
      server_cert.pm_raw_sent
      server_cert.pm_raw_received;
    lemma_protected_handshake_wire_equal_from_event_projections_peer
      server_cv.pm_sender
      server_cv.pm_receiver
      (M.CertificateVerify server_cv_msg)
      (M.CertificateVerify client_cv)
      server_cv.pm_raw_sent
      server_cv.pm_raw_received;
    lemma_protected_handshake_wire_equal_from_event_projections_peer
      server_finished.pm_sender
      server_finished.pm_receiver
      (M.Finished server_sf)
      (M.Finished client_sf)
      server_finished.pm_raw_sent
      server_finished.pm_raw_received;
    lemma_protected_handshake_wire_equal_from_event_projections_peer
      client_finished.pm_sender
      client_finished.pm_receiver
      (M.Finished client_cf)
      (M.Finished server_cf)
      client_finished.pm_raw_sent
      client_finished.pm_raw_received;
    assert (WFL.paired_protected_handshake_wire_equivalent client server)
  | _, _, _, _, _, _, _, _, _, _ ->
    assert False
#pop-options

let lemma_conn_events_sent_seal_replay_head
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_sent_seal_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model1 delta_sent delta_received tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          sent_event_nonempty_seal_projection model ev delta_sent /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_sent_seal_replay
            model1
            rest
            tail_sent
            tail_received
            final_model)
=
  eliminate exists
    (model1:connection_model)
    (delta_sent:B.bytes)
    (delta_received:B.bytes)
    (tail_sent:B.bytes)
    (tail_received:B.bytes).
    legal_event model ev /\
    step_model model ev == Some model1 /\
    event_raw_delta_legal model ev delta_sent delta_received /\
    sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    conn_events_sent_seal_replay
      model1
      rest
      tail_sent
      tail_received
      final_model
  returns
    exists model1 delta_sent delta_received tail_sent tail_received.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_sent_seal_replay
        model1
        rest
        tail_sent
        tail_received
        final_model
  with _.
  ( introduce exists
      (model1':connection_model)
      (delta_sent':B.bytes)
      (delta_received':B.bytes)
      (tail_sent':B.bytes)
      (tail_received':B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1' /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      sent_event_nonempty_seal_projection model ev delta_sent' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_sent_seal_replay
        model1'
        rest
        tail_sent'
        tail_received'
        final_model
    with model1 delta_sent delta_received tail_sent tail_received
    and () )

let lemma_conn_events_received_decode_replay_head
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_received_decode_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model1 delta_sent delta_received tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          received_event_nonempty_decode_projection model ev delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_received_decode_replay
            model1
            rest
            tail_sent
            tail_received
            final_model)
=
  eliminate exists
    (model1:connection_model)
    (delta_sent:B.bytes)
    (delta_received:B.bytes)
    (tail_sent:B.bytes)
    (tail_received:B.bytes).
    legal_event model ev /\
    step_model model ev == Some model1 /\
    event_raw_delta_legal model ev delta_sent delta_received /\
    received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    conn_events_received_decode_replay
      model1
      rest
      tail_sent
      tail_received
      final_model
  returns
    exists model1 delta_sent delta_received tail_sent tail_received.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_received_decode_replay
        model1
        rest
        tail_sent
        tail_received
        final_model
  with _.
  ( introduce exists
      (model1':connection_model)
      (delta_sent':B.bytes)
      (delta_received':B.bytes)
      (tail_sent':B.bytes)
      (tail_received':B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1' /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      received_event_nonempty_decode_projection model ev delta_received' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_received_decode_replay
        model1'
        rest
        tail_sent'
        tail_received'
        final_model
    with model1 delta_sent delta_received tail_sent tail_received
    and () )
