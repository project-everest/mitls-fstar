module TLS13.ConnectionState.ProtectedWireLemmas

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CSL = TLS13.ConnectionState.Lemmas
module M = TLS13.Messages
module R = TLS13.Record.Spec
module RD = TLS13.Wire.Spec.RevealDecode
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas
module WRT = TLS13.Wire.Spec.Reveal.FinishedRoundTrip
module WU = TLS13.Wire.Spec.Reveal.Util

open TLS13.Spec.ConnectionState

let lemma_append_heads_equal_same_len
  #a
  (left:Seq.seq a)
  (left_tail:Seq.seq a)
  (right:Seq.seq a)
  (right_tail:Seq.seq a)
  : Lemma
    (requires
      Seq.equal (Seq.append left left_tail) (Seq.append right right_tail) /\
      Seq.length left == Seq.length right)
    (ensures Seq.equal left right)
=
  let left_full = Seq.append left left_tail in
  let right_full = Seq.append right right_tail in
  WU.lemma_slice_append_left left left_tail;
  WU.lemma_slice_append_left right right_tail;
  Seq.lemma_eq_elim left_full right_full;
  assert (Seq.equal (Seq.slice right_full 0 (Seq.length left)) right);
  assert (Seq.equal (Seq.slice left_full 0 (Seq.length left)) right);
  Seq.lemma_eq_elim (Seq.slice left_full 0 (Seq.length left)) left

let lemma_raw_delta_heads_equal_same_len
  (sender_delta:B.bytes)
  (sender_tail:B.bytes)
  (receiver_delta:B.bytes)
  (receiver_tail:B.bytes)
  : Lemma
    (requires
      Seq.equal
        (B.append sender_delta sender_tail)
        (B.append receiver_delta receiver_tail) /\
      B.length sender_delta == B.length receiver_delta)
    (ensures Seq.equal sender_delta receiver_delta)
=
  lemma_append_heads_equal_same_len
    sender_delta
    sender_tail
    receiver_delta
    receiver_tail

#push-options "--split_queries always --z3rlimit 10"
let lemma_equal_stream_record_head_lengths
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (left_head:B.bytes)
  (left_tail:B.bytes)
  (right_head:B.bytes)
  (right_tail:B.bytes)
  (left_ct:T.content_type)
  (left_fragment:M.sealed_record)
  (right_ct:T.content_type)
  (right_fragment:M.sealed_record)
  : Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal left_stream (B.append left_head left_tail) /\
      Seq.equal right_stream (B.append right_head right_tail) /\
      W.parse_record_wire left_head ==
        Some (left_ct, left_fragment, B.length left_head) /\
      W.parse_record_wire right_head ==
        Some (right_ct, right_fragment, B.length right_head))
    (ensures B.length left_head == B.length right_head)
=
  WU.lemma_slice_append_left left_head left_tail;
  WU.lemma_slice_append_left right_head right_tail;
  Seq.lemma_len_append left_head left_tail;
  Seq.lemma_len_append right_head right_tail;
  Seq.lemma_eq_elim left_stream (B.append left_head left_tail);
  assert (Seq.equal (Seq.slice left_stream 0 (B.length left_head)) left_head);
  Seq.lemma_eq_elim (Seq.slice left_stream 0 (B.length left_head)) left_head;
  RD.lemma_parse_record_wire_from_prefix
    left_stream
    left_ct
    left_fragment
    (B.length left_head);
  assert (W.parse_record_wire left_stream ==
    Some (left_ct, left_fragment, B.length left_head));
  Seq.lemma_eq_elim right_stream (B.append right_head right_tail);
  assert (Seq.equal (Seq.slice right_stream 0 (B.length right_head)) right_head);
  Seq.lemma_eq_elim (Seq.slice right_stream 0 (B.length right_head)) right_head;
  RD.lemma_parse_record_wire_from_prefix
    right_stream
    right_ct
    right_fragment
    (B.length right_head);
  assert (W.parse_record_wire right_stream ==
    Some (right_ct, right_fragment, B.length right_head));
  Seq.lemma_eq_elim left_stream right_stream;
  assert (Some (left_ct, left_fragment, B.length left_head) ==
          Some (right_ct, right_fragment, B.length right_head))
#pop-options

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

#push-options "--split_queries always --z3rlimit 10"
let lemma_sent_event_nonempty_seal_projection_protected
  (model:connection_model)
  (msg:M.tls_message)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        network_message_is_cleartext CL.Sent msg == false /\
        protected_record_count CL.Sent msg == 1 /\
        event_raw_delta_legal
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          })
          delta_sent
          delta_received /\
        sent_event_nonempty_seal_projection
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          })
          delta_sent)
      (ensures
        sent_event_seal_projection
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          })
          delta_sent)
=
  if B.length delta_sent == 0 then
    begin
      assert (raw_records_exactly delta_sent T.ApplicationData 1);
      CSL.lemma_raw_records_exactly_one_parse_record delta_sent T.ApplicationData;
      eliminate exists (fragment:B.bytes).
        W.parse_record delta_sent ==
          Some (T.ApplicationData, fragment, B.length delta_sent)
      returns
        sent_event_seal_projection
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          })
          delta_sent
      with _.
      ( W.lemma_parse_record_implies_parse_record_wire delta_sent;
        W.lemma_parse_record_wire_some_consumed_positive
          delta_sent
          T.ApplicationData
          fragment
          (B.length delta_sent);
        assert False )
    end
  else
    assert (sent_event_seal_projection
      model
      (ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = msg;
      })
      delta_sent)

let lemma_received_event_nonempty_decode_projection_protected
  (model:connection_model)
  (msg:M.tls_message)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        network_message_is_cleartext CL.Received msg == false /\
        protected_record_count CL.Received msg == 1 /\
        event_raw_delta_legal
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          })
          delta_sent
          delta_received /\
        received_event_nonempty_decode_projection
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          })
          delta_received)
      (ensures
        received_event_decode_projection
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          })
          delta_received)
=
  if B.length delta_received == 0 then
    begin
      assert (raw_records_exactly delta_received T.ApplicationData 1);
      CSL.lemma_raw_records_exactly_one_parse_record delta_received T.ApplicationData;
      eliminate exists (fragment:B.bytes).
        W.parse_record delta_received ==
          Some (T.ApplicationData, fragment, B.length delta_received)
      returns
        received_event_decode_projection
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          })
          delta_received
      with _.
      ( W.lemma_parse_record_implies_parse_record_wire delta_received;
        W.lemma_parse_record_wire_some_consumed_positive
          delta_received
          T.ApplicationData
          fragment
          (B.length delta_received);
        assert False )
    end
  else
    assert (received_event_decode_projection
      model
      (ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = msg;
      })
      delta_received)
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_protected_handshake_event_projection_pair_from_aligned_heads
  (sender:connection_model)
  (receiver:connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_stream:B.bytes)
  (receiver_stream:B.bytes)
  (sender_delta:B.bytes)
  (sender_tail:B.bytes)
  (receiver_delta:B.bytes)
  (receiver_tail:B.bytes)
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
        Seq.equal sender_stream receiver_stream /\
        Seq.equal sender_stream (B.append sender_delta sender_tail) /\
        Seq.equal receiver_stream (B.append receiver_delta receiver_tail) /\
        B.length sender_delta == B.length receiver_delta /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        sent_event_seal_projection
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          sender_delta /\
        received_event_decode_projection
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          })
          receiver_delta)
      (ensures
        protected_handshake_event_projection_pair
          {
            pm_sender = sender;
            pm_receiver = receiver;
            pm_raw_sent = sender_delta;
            pm_raw_received = receiver_delta;
          }
          sent_msg
          received_msg)
=
  Seq.lemma_eq_elim sender_stream receiver_stream;
  Seq.lemma_eq_elim sender_stream (B.append sender_delta sender_tail);
  assert (Seq.equal
    (B.append sender_delta sender_tail)
    (B.append receiver_delta receiver_tail));
  lemma_raw_delta_heads_equal_same_len
    sender_delta
    sender_tail
    receiver_delta
    receiver_tail;
  assert (Seq.equal sender_delta receiver_delta)
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_protected_handshake_event_projection_pair_from_equal_stream_heads
  (sender:connection_model)
  (receiver:connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_stream:B.bytes)
  (receiver_stream:B.bytes)
  (sender_delta:B.bytes)
  (sender_tail:B.bytes)
  (receiver_delta:B.bytes)
  (receiver_tail:B.bytes)
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
        Seq.equal sender_stream receiver_stream /\
        Seq.equal sender_stream (B.append sender_delta sender_tail) /\
        Seq.equal receiver_stream (B.append receiver_delta receiver_tail) /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        sent_event_seal_projection
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          sender_delta /\
        received_event_decode_projection
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          })
          receiver_delta)
      (ensures
        protected_handshake_event_projection_pair
          {
            pm_sender = sender;
            pm_receiver = receiver;
            pm_raw_sent = sender_delta;
            pm_raw_received = receiver_delta;
          }
          sent_msg
          received_msg)
=
  match sent_msg with
  | M.EncryptedExtensions _
  | M.Certificate _
  | M.CertificateVerify _
  | M.Finished _ ->
    match received_msg with
    | M.EncryptedExtensions _
    | M.Certificate _
    | M.CertificateVerify _
    | M.Finished _ ->
      assert (network_message_is_cleartext CL.Sent (M.TlsHandshake sent_msg) == false);
      assert (network_message_is_cleartext CL.Received (M.TlsHandshake received_msg) == false);
      assert (protected_record_count CL.Sent (M.TlsHandshake sent_msg) == 1);
      assert (protected_record_count CL.Received (M.TlsHandshake received_msg) == 1);
      assert (sent_single_protected_message_seal
        sender
        (M.TlsHandshake sent_msg)
        sender_delta);
      assert (received_single_protected_message_decode
        receiver
        (M.TlsHandshake received_msg)
        receiver_delta);
      eliminate exists (sender_ciphertext:B.bytes).
        W.parse_record sender_delta ==
          Some (T.ApplicationData, sender_ciphertext, B.length sender_delta) /\
        R.seal
          sender.model_record.record_write
          (record_header_aad sender_delta)
          {
            R.content_type = T.ApplicationData;
            R.fragment = sent_tls_inner_plaintext_fragment (M.TlsHandshake sent_msg);
          } ==
          Some (sender_ciphertext, R.next_seq sender.model_record.record_write)
      returns
        protected_handshake_event_projection_pair
          {
            pm_sender = sender;
            pm_receiver = receiver;
            pm_raw_sent = sender_delta;
            pm_raw_received = receiver_delta;
          }
          sent_msg
          received_msg
      with _.
      ( W.lemma_parse_record_implies_parse_record_wire sender_delta;
        assert (W.parse_record_wire sender_delta ==
          Some (T.ApplicationData, sender_ciphertext, B.length sender_delta));
        eliminate exists
          (receiver_fragment:B.bytes)
          (opened:B.bytes)
          (plaintext:M.plaintext).
          W.parse_record_wire receiver_delta ==
            Some (T.ApplicationData, receiver_fragment, B.length receiver_delta) /\
          received_record_opened receiver receiver_delta receiver_fragment opened /\
          W.parse_plaintext opened == Some plaintext /\
          W.parse_tls_message plaintext.M.content_type plaintext.M.fragment ==
            Some (M.TlsHandshake received_msg)
        returns
          protected_handshake_event_projection_pair
            {
              pm_sender = sender;
              pm_receiver = receiver;
              pm_raw_sent = sender_delta;
              pm_raw_received = receiver_delta;
            }
            sent_msg
            received_msg
        with _.
        ( lemma_equal_stream_record_head_lengths
            sender_stream
            receiver_stream
            sender_delta
            sender_tail
            receiver_delta
            receiver_tail
            T.ApplicationData
            sender_ciphertext
            T.ApplicationData
            receiver_fragment;
          assert (B.length sender_delta == B.length receiver_delta);
          lemma_protected_handshake_event_projection_pair_from_aligned_heads
            sender
            receiver
            sent_msg
            received_msg
            sender_stream
            receiver_stream
            sender_delta
            sender_tail
            receiver_delta
            receiver_tail ) )
    | _ ->
      assert False
  | _ ->
    assert False
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_protected_handshake_event_projection_pair_from_head_replays
  (sender:connection_model)
  (receiver:connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list conn_event)
  (receiver_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
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
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair.
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)
=
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  match sent_msg with
  | M.EncryptedExtensions _
  | M.Certificate _
  | M.CertificateVerify _
  | M.Finished _ ->
    match received_msg with
    | M.EncryptedExtensions _
    | M.Certificate _
    | M.CertificateVerify _
    | M.Finished _ ->
      lemma_conn_events_sent_seal_replay_head
        sender
        sent_ev
        sender_rest
        sender_raw_sent
        sender_raw_received
        sender_final;
      eliminate exists
        (sender_model1:connection_model)
        (sender_delta_sent:B.bytes)
        (sender_delta_received:B.bytes)
        (sender_tail_sent:B.bytes)
        (sender_tail_received:B.bytes).
        legal_event sender sent_ev /\
        step_model sender sent_ev == Some sender_model1 /\
        event_raw_delta_legal sender sent_ev sender_delta_sent sender_delta_received /\
        sent_event_nonempty_seal_projection sender sent_ev sender_delta_sent /\
        Seq.equal sender_raw_sent (B.append sender_delta_sent sender_tail_sent) /\
        Seq.equal sender_raw_received (B.append sender_delta_received sender_tail_received) /\
        conn_events_sent_seal_replay
          sender_model1
          sender_rest
          sender_tail_sent
          sender_tail_received
          sender_final
      returns
        exists pair.
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg
      with _.
      ( lemma_conn_events_received_decode_replay_head
          receiver
          received_ev
          receiver_rest
          receiver_raw_sent
          receiver_raw_received
          receiver_final;
        eliminate exists
          (receiver_model1:connection_model)
          (receiver_delta_sent:B.bytes)
          (receiver_delta_received:B.bytes)
          (receiver_tail_sent:B.bytes)
          (receiver_tail_received:B.bytes).
          legal_event receiver received_ev /\
          step_model receiver received_ev == Some receiver_model1 /\
          event_raw_delta_legal receiver received_ev receiver_delta_sent receiver_delta_received /\
          received_event_nonempty_decode_projection receiver received_ev receiver_delta_received /\
          Seq.equal receiver_raw_sent (B.append receiver_delta_sent receiver_tail_sent) /\
          Seq.equal receiver_raw_received (B.append receiver_delta_received receiver_tail_received) /\
          conn_events_received_decode_replay
            receiver_model1
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final
        returns
          exists pair.
            pair.pm_sender == sender /\
            pair.pm_receiver == receiver /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg
        with _.
        ( assert (network_message_is_cleartext CL.Sent (M.TlsHandshake sent_msg) == false);
          assert (network_message_is_cleartext CL.Received (M.TlsHandshake received_msg) == false);
          assert (protected_record_count CL.Sent (M.TlsHandshake sent_msg) == 1);
          assert (protected_record_count CL.Received (M.TlsHandshake received_msg) == 1);
          lemma_sent_event_nonempty_seal_projection_protected
            sender
            (M.TlsHandshake sent_msg)
            sender_delta_sent
            sender_delta_received;
          lemma_received_event_nonempty_decode_projection_protected
            receiver
            (M.TlsHandshake received_msg)
            receiver_delta_sent
            receiver_delta_received;
          lemma_protected_handshake_event_projection_pair_from_equal_stream_heads
            sender
            receiver
            sent_msg
            received_msg
            sender_raw_sent
            receiver_raw_received
            sender_delta_sent
            sender_tail_sent
            receiver_delta_received
            receiver_tail_received;
          introduce exists (pair:protected_message_replay).
            pair.pm_sender == sender /\
            pair.pm_receiver == receiver /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg
          with ({
            pm_sender = sender;
            pm_receiver = receiver;
            pm_raw_sent = sender_delta_sent;
            pm_raw_received = receiver_delta_received;
          })
          and () ) )
    | _ ->
      assert False
  | _ ->
    assert False
#pop-options
