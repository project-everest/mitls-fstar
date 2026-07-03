module TLS13.ConnectionState.ProtectedWireLemmas

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CSL = TLS13.ConnectionState.Lemmas
module M = TLS13.Messages
module R = TLS13.Record.Spec
module RD = TLS13.Wire.Spec.RevealDecode
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties
module T = TLS13.Types
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas
module WRT = TLS13.Wire.Spec.Reveal.FinishedRoundTrip
module WU = TLS13.Wire.Spec.Reveal.Util

open TLS13.Spec.ConnectionState

let lemma_client_traffic_peer_record_material_agrees_and_seq_write_read_aligned
  (epoch:traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        client.cs_model.model_record.record_write.R.seq ==
          server.cs_model.model_record.record_read.R.seq /\
        peer_record_material_agrees
          (traffic_id epoch ClientTraffic)
          client
          server)
      (ensures
        write_read_record_material_aligned
          client.cs_model
          server.cs_model)
=
  match
    record_direction_material client.cs_model.model_record.record_write,
    record_direction_material server.cs_model.model_record.record_read
  with
  | Some client_write, Some server_read ->
    assert (client.cs_model.model_record.record_write.R.seq ==
      server.cs_model.model_record.record_read.R.seq);
    assert (record_key_iv_material_agrees client_write server_read)
  | _, _ ->
    assert False

let lemma_server_traffic_peer_record_material_agrees_and_seq_write_read_aligned
  (epoch:traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        server.cs_model.model_record.record_write.R.seq ==
          client.cs_model.model_record.record_read.R.seq /\
        peer_record_material_agrees
          (traffic_id epoch ServerTraffic)
          client
          server)
      (ensures
        write_read_record_material_aligned
          server.cs_model
          client.cs_model)
=
  match
    record_direction_material server.cs_model.model_record.record_write,
    record_direction_material client.cs_model.model_record.record_read
  with
  | Some server_write, Some client_read ->
    assert (server.cs_model.model_record.record_write.R.seq ==
      client.cs_model.model_record.record_read.R.seq);
    assert (record_key_iv_material_agrees server_write client_read)
  | _, _ ->
    assert False

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

let lemma_append_tails_equal_same_len
  #a
  (left:Seq.seq a)
  (left_tail:Seq.seq a)
  (right:Seq.seq a)
  (right_tail:Seq.seq a)
  : Lemma
    (requires
      Seq.equal (Seq.append left left_tail) (Seq.append right right_tail) /\
      Seq.length left == Seq.length right)
    (ensures Seq.equal left_tail right_tail)
=
  SeqProps.lemma_append_inj left left_tail right right_tail;
  assert (Seq.equal left_tail right_tail)

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

let lemma_equal_streams_skip_empty_left
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (left_tail:B.bytes)
  : Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal left_stream (B.append B.empty left_tail))
    (ensures Seq.equal left_tail right_stream)
=
  Seq.append_empty_l left_tail;
  Seq.lemma_eq_elim left_stream right_stream;
  Seq.lemma_eq_elim left_stream (B.append B.empty left_tail)

let lemma_equal_streams_skip_empty_right
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (right_tail:B.bytes)
  : Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal right_stream (B.append B.empty right_tail))
    (ensures Seq.equal left_stream right_tail)
=
  Seq.append_empty_l right_tail;
  Seq.lemma_eq_elim left_stream right_stream;
  Seq.lemma_eq_elim right_stream (B.append B.empty right_tail)

let lemma_equal_streams_skip_empty_both
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (left_tail:B.bytes)
  (right_tail:B.bytes)
  : Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal left_stream (B.append B.empty left_tail) /\
      Seq.equal right_stream (B.append B.empty right_tail))
    (ensures Seq.equal left_tail right_tail)
=
  lemma_equal_streams_skip_empty_left left_stream right_stream left_tail;
  lemma_equal_streams_skip_empty_right left_tail right_stream right_tail

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
let lemma_step_received_network_event_preserves_record_write
  (model:connection_model)
  (msg:M.tls_message)
  (model_after:connection_model)
  : Lemma
      (requires
        step_model
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          }) == Some model_after)
      (ensures
        model_after.model_record.record_write ==
          model.model_record.record_write)
=
  ()

let lemma_step_sent_network_event_preserves_record_read
  (model:connection_model)
  (msg:M.tls_message)
  (model_after:connection_model)
  : Lemma
      (requires
        step_model
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          }) == Some model_after)
      (ensures
        model_after.model_record.record_read ==
          model.model_record.record_read)
=
  ()

let lemma_step_received_network_event_preserves_write_read_record_material_alignment
  (sender:connection_model)
  (msg:M.tls_message)
  (sender_after:connection_model)
  (receiver:connection_model)
  : Lemma
      (requires
        step_model
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          }) == Some sender_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver)
=
  lemma_step_received_network_event_preserves_record_write
    sender
    msg
    sender_after

let lemma_step_sent_network_event_preserves_write_read_record_material_alignment
  (sender:connection_model)
  (receiver:connection_model)
  (msg:M.tls_message)
  (receiver_after:connection_model)
  : Lemma
      (requires
        step_model
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          }) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender receiver_after)
=
  lemma_step_sent_network_event_preserves_record_read
    receiver
    msg
    receiver_after

let lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
  (sender:connection_model)
  (sender_msg:M.tls_message)
  (sender_after:connection_model)
  (receiver:connection_model)
  (receiver_msg:M.tls_message)
  (receiver_after:connection_model)
  : Lemma
      (requires
        step_model
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = sender_msg;
          }) == Some sender_after /\
        step_model
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = receiver_msg;
          }) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver_after)
=
  lemma_step_received_network_event_preserves_write_read_record_material_alignment
    sender
    sender_msg
    sender_after
    receiver;
  lemma_step_sent_network_event_preserves_write_read_record_material_alignment
    sender_after
    receiver
    receiver_msg
    receiver_after

let lemma_step_non_install_local_event_preserves_record_layer
  (model:connection_model)
  (ev:local_event)
  (model_after:connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys ev /\
        step_model
          model
          (ConnLocalEvent ev) == Some model_after)
      (ensures model_after.model_record == model.model_record)
=
  match ev with
  | LocalInstallTrafficKeys _
  | LocalInstallTrafficKeysForRole _ ->
    assert False
  | LocalStartHandshake _
  | LocalStartServer
  | LocalSelectServerParameters _
  | LocalDeriveSharedSecret _
  | LocalValidateCertificate _
  | LocalVerifyCertificateSignature _
  | LocalSignCertificateVerify _
  | LocalVerifyFinished _
  | LocalVerifyClientFinished _
  | LocalDeliverApplicationData _
  | LocalFail _ ->
    ()

let lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
  (sender:connection_model)
  (ev:local_event)
  (sender_after:connection_model)
  (receiver:connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys ev /\
        step_model
          sender
          (ConnLocalEvent ev) == Some sender_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver)
=
  lemma_step_non_install_local_event_preserves_record_layer
    sender
    ev
    sender_after

let lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
  (sender:connection_model)
  (receiver:connection_model)
  (ev:local_event)
  (receiver_after:connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys ev /\
        step_model
          receiver
          (ConnLocalEvent ev) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender receiver_after)
=
  lemma_step_non_install_local_event_preserves_record_layer
    receiver
    ev
    receiver_after

let lemma_next_seq_models_preserve_write_read_record_material_alignment
  (sender:connection_model)
  (receiver:connection_model)
  (sender_after:connection_model)
  (receiver_after:connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        sender_after.model_record.record_write ==
          R.next_seq sender.model_record.record_write /\
        receiver_after.model_record.record_read ==
          R.next_seq receiver.model_record.record_read)
      (ensures write_read_record_material_aligned sender_after receiver_after)
=
  match
    record_direction_material sender.model_record.record_write,
    record_direction_material receiver.model_record.record_read
  with
  | Some sender_write, Some receiver_read ->
    assert (record_key_iv_material_agrees sender_write receiver_read);
    assert (record_direction_material sender_after.model_record.record_write ==
      record_direction_material sender.model_record.record_write);
    assert (record_direction_material receiver_after.model_record.record_read ==
      record_direction_material receiver.model_record.record_read)
  | _, _ ->
    assert False

let lemma_server_handshake_write_client_handshake_read_install_aligned
  (server:connection_model)
  (client:connection_model)
  (material:traffic_key_material)
  (server_after:connection_model)
  (client_after:connection_model)
  : Lemma
      (requires
        step_model
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = material;
              };
            })) == Some server_after /\
        step_model
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = material;
            })) == Some client_after)
      (ensures write_read_record_material_aligned server_after client_after)
=
  assert (server_after.model_record.record_write ==
    R.install_keys
      server.model_record.record_write
      R.Handshake
      material.traffic_key
      material.traffic_iv);
  assert (client_after.model_record.record_read ==
    R.install_keys
      client.model_record.record_read
      R.Handshake
      material.traffic_key
      material.traffic_iv)

let lemma_server_handshake_write_client_handshake_read_install_materials_aligned
  (server:connection_model)
  (client:connection_model)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (server_after:connection_model)
  (client_after:connection_model)
  : Lemma
      (requires
        record_key_iv_material_agrees
          (record_material_of_traffic_material server_material)
          (record_material_of_traffic_material client_material) /\
        step_model
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = server_material;
              };
            })) == Some server_after /\
        step_model
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            })) == Some client_after)
      (ensures write_read_record_material_aligned server_after client_after)
=
  assert (server_after.model_record.record_write ==
    R.install_keys
      server.model_record.record_write
      R.Handshake
      server_material.traffic_key
      server_material.traffic_iv);
  assert (client_after.model_record.record_read ==
    R.install_keys
      client.model_record.record_read
      R.Handshake
      client_material.traffic_key
      client_material.traffic_iv)

let lemma_client_handshake_write_server_handshake_read_install_aligned
  (client:connection_model)
  (server:connection_model)
  (material:traffic_key_material)
  (client_after:connection_model)
  (server_after:connection_model)
  : Lemma
      (requires
        step_model
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficWrite;
              install_material = material;
            })) == Some client_after /\
        step_model
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficRead;
                install_material = material;
              };
            })) == Some server_after)
      (ensures write_read_record_material_aligned client_after server_after)
=
  assert (client_after.model_record.record_write ==
    R.install_keys
      client.model_record.record_write
      R.Handshake
      material.traffic_key
      material.traffic_iv);
  assert (server_after.model_record.record_read ==
    R.install_keys
      server.model_record.record_read
      R.Handshake
      material.traffic_key
      material.traffic_iv)

let lemma_client_handshake_write_server_handshake_read_install_materials_aligned
  (client:connection_model)
  (server:connection_model)
  (client_material:traffic_key_material)
  (server_material:traffic_key_material)
  (client_after:connection_model)
  (server_after:connection_model)
  : Lemma
      (requires
        record_key_iv_material_agrees
          (record_material_of_traffic_material client_material)
          (record_material_of_traffic_material server_material) /\
        step_model
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficWrite;
              install_material = client_material;
            })) == Some client_after /\
        step_model
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficRead;
                install_material = server_material;
              };
            })) == Some server_after)
      (ensures write_read_record_material_aligned client_after server_after)
=
  assert (client_after.model_record.record_write ==
    R.install_keys
      client.model_record.record_write
      R.Handshake
      client_material.traffic_key
      client_material.traffic_iv);
  assert (server_after.model_record.record_read ==
    R.install_keys
      server.model_record.record_read
      R.Handshake
      server_material.traffic_key
      server_material.traffic_iv)
#pop-options

let lemma_sent_replay_skip_empty_head_preserves_peer_stream
  (sender:connection_model)
  (ev:conn_event)
  (sender_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  : Lemma
      (requires
        Seq.equal sender_raw_sent receiver_raw_received /\
        conn_events_sent_seal_replay
          sender
          (ev :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        (match ev with
         | ConnLocalEvent _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received))
      (ensures
        exists sender1 sender_tail_sent sender_tail_received.
          legal_event sender ev /\
          step_model sender ev == Some sender1 /\
          Seq.equal sender_tail_sent receiver_raw_received /\
          conn_events_sent_seal_replay
            sender1
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final)
=
  lemma_conn_events_sent_seal_replay_head
    sender
    ev
    sender_rest
    sender_raw_sent
    sender_raw_received
    sender_final;
  eliminate exists
    (sender1:connection_model)
    (delta_sent:B.bytes)
    (delta_received:B.bytes)
    (tail_sent:B.bytes)
    (tail_received:B.bytes).
    legal_event sender ev /\
    step_model sender ev == Some sender1 /\
    event_raw_delta_legal sender ev delta_sent delta_received /\
    sent_event_nonempty_seal_projection sender ev delta_sent /\
    Seq.equal sender_raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal sender_raw_received (B.append delta_received tail_received) /\
    conn_events_sent_seal_replay
      sender1
      sender_rest
      tail_sent
      tail_received
      sender_final
  returns
    exists sender1 sender_tail_sent sender_tail_received.
      legal_event sender ev /\
      step_model sender ev == Some sender1 /\
      Seq.equal sender_tail_sent receiver_raw_received /\
      conn_events_sent_seal_replay
        sender1
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final
  with _.
  ( match ev with
    | ConnLocalEvent _ ->
      assert (Seq.equal delta_sent B.empty)
    | ConnNetworkEvent msg ->
      assert (msg.CL.message_direction == CL.Received);
      assert (Seq.equal delta_sent B.empty);
    lemma_equal_streams_skip_empty_left
      sender_raw_sent
      receiver_raw_received
      tail_sent;
    introduce exists
      (sender1':connection_model)
      (sender_tail_sent':B.bytes)
      (sender_tail_received':B.bytes).
      legal_event sender ev /\
      step_model sender ev == Some sender1' /\
      Seq.equal sender_tail_sent' receiver_raw_received /\
      conn_events_sent_seal_replay
        sender1'
        sender_rest
        sender_tail_sent'
        sender_tail_received'
        sender_final
    with sender1 tail_sent tail_received
    and () )

let lemma_received_replay_skip_empty_head_preserves_peer_stream
  (sender_raw_sent:B.bytes)
  (receiver:connection_model)
  (ev:conn_event)
  (receiver_rest:list conn_event)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (receiver_final:connection_model)
  : Lemma
      (requires
        Seq.equal sender_raw_sent receiver_raw_received /\
        conn_events_received_decode_replay
          receiver
          (ev :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final /\
        (match ev with
         | ConnLocalEvent _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent))
      (ensures
        exists receiver1 receiver_tail_sent receiver_tail_received.
          legal_event receiver ev /\
          step_model receiver ev == Some receiver1 /\
          Seq.equal sender_raw_sent receiver_tail_received /\
          conn_events_received_decode_replay
            receiver1
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  lemma_conn_events_received_decode_replay_head
    receiver
    ev
    receiver_rest
    receiver_raw_sent
    receiver_raw_received
    receiver_final;
  eliminate exists
    (receiver1:connection_model)
    (delta_sent:B.bytes)
    (delta_received:B.bytes)
    (tail_sent:B.bytes)
    (tail_received:B.bytes).
    legal_event receiver ev /\
    step_model receiver ev == Some receiver1 /\
    event_raw_delta_legal receiver ev delta_sent delta_received /\
    received_event_nonempty_decode_projection receiver ev delta_received /\
    Seq.equal receiver_raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal receiver_raw_received (B.append delta_received tail_received) /\
    conn_events_received_decode_replay
      receiver1
      receiver_rest
      tail_sent
      tail_received
      receiver_final
  returns
    exists receiver1 receiver_tail_sent receiver_tail_received.
      legal_event receiver ev /\
      step_model receiver ev == Some receiver1 /\
      Seq.equal sender_raw_sent receiver_tail_received /\
      conn_events_received_decode_replay
        receiver1
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( match ev with
    | ConnLocalEvent _ ->
      assert (Seq.equal delta_received B.empty)
    | ConnNetworkEvent msg ->
      assert (msg.CL.message_direction == CL.Sent);
      assert (Seq.equal delta_received B.empty);
    lemma_equal_streams_skip_empty_right
      sender_raw_sent
      receiver_raw_received
      tail_received;
    introduce exists
      (receiver1':connection_model)
      (receiver_tail_sent':B.bytes)
      (receiver_tail_received':B.bytes).
      legal_event receiver ev /\
      step_model receiver ev == Some receiver1' /\
      Seq.equal sender_raw_sent receiver_tail_received' /\
      conn_events_received_decode_replay
        receiver1'
        receiver_rest
        receiver_tail_sent'
        receiver_tail_received'
        receiver_final
    with receiver1 tail_sent tail_received
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
let lemma_protected_handshake_event_tails_equal_from_equal_stream_heads
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
      (ensures Seq.equal sender_tail receiver_tail)
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
      eliminate exists (sender_ciphertext:M.sealed_record).
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
      returns Seq.equal sender_tail receiver_tail
      with _.
      ( W.lemma_parse_record_implies_parse_record_wire sender_delta;
        assert (W.parse_record_wire sender_delta ==
          Some (T.ApplicationData, sender_ciphertext, B.length sender_delta));
        eliminate exists
          (receiver_fragment:M.sealed_record)
          (opened:B.bytes)
          (plaintext:M.plaintext).
          W.parse_record_wire receiver_delta ==
            Some (T.ApplicationData, receiver_fragment, B.length receiver_delta) /\
          received_record_opened receiver receiver_delta receiver_fragment opened /\
          W.parse_plaintext opened == Some plaintext /\
          W.parse_tls_message plaintext.M.content_type plaintext.M.fragment ==
            Some (M.TlsHandshake received_msg)
        returns Seq.equal sender_tail receiver_tail
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
          Seq.lemma_eq_elim sender_stream receiver_stream;
          Seq.lemma_eq_elim sender_stream (B.append sender_delta sender_tail);
          assert (Seq.equal
            (B.append sender_delta sender_tail)
            (B.append receiver_delta receiver_tail));
          lemma_append_tails_equal_same_len
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

#push-options "--split_queries always --z3rlimit 10"
let lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
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
        write_read_record_material_aligned sender receiver /\
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
        exists sender_after receiver_after pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          step_model
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after /\
          step_model
            receiver
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after /\
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_raw_sent (B.append pair.pm_raw_sent sender_tail_sent) /\
          Seq.equal receiver_raw_received (B.append pair.pm_raw_received receiver_tail_received) /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          conn_events_sent_seal_replay
            sender_after
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
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
        exists sender_after receiver_after pair
          sender_tail_sent' sender_tail_received'
          receiver_tail_sent receiver_tail_received.
          step_model sender sent_ev == Some sender_after /\
          step_model receiver received_ev == Some receiver_after /\
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_raw_sent (B.append pair.pm_raw_sent sender_tail_sent') /\
          Seq.equal receiver_raw_received (B.append pair.pm_raw_received receiver_tail_received) /\
          Seq.equal sender_tail_sent' receiver_tail_received /\
          conn_events_sent_seal_replay
            sender_after
            sender_rest
            sender_tail_sent'
            sender_tail_received'
            sender_final /\
          conn_events_received_decode_replay
            receiver_after
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final
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
          exists sender_after receiver_after pair
            sender_tail_sent' sender_tail_received'
            receiver_tail_sent' receiver_tail_received'.
            step_model sender sent_ev == Some sender_after /\
            step_model receiver received_ev == Some receiver_after /\
            pair.pm_sender == sender /\
            pair.pm_receiver == receiver /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg /\
            Seq.equal sender_raw_sent (B.append pair.pm_raw_sent sender_tail_sent') /\
            Seq.equal receiver_raw_received (B.append pair.pm_raw_received receiver_tail_received') /\
            Seq.equal sender_tail_sent' receiver_tail_received' /\
            conn_events_sent_seal_replay
              sender_after
              sender_rest
              sender_tail_sent'
              sender_tail_received'
              sender_final /\
            conn_events_received_decode_replay
              receiver_after
              receiver_rest
              receiver_tail_sent'
              receiver_tail_received'
              receiver_final
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
          lemma_protected_handshake_event_tails_equal_from_equal_stream_heads
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
          introduce exists
            (sender_after:connection_model)
            (receiver_after:connection_model)
            (pair:protected_message_replay)
            (sender_tail_sent':B.bytes)
            (sender_tail_received':B.bytes)
            (receiver_tail_sent':B.bytes)
            (receiver_tail_received':B.bytes).
            step_model sender sent_ev == Some sender_after /\
            step_model receiver received_ev == Some receiver_after /\
            pair.pm_sender == sender /\
            pair.pm_receiver == receiver /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg /\
            Seq.equal sender_raw_sent (B.append pair.pm_raw_sent sender_tail_sent') /\
            Seq.equal receiver_raw_received (B.append pair.pm_raw_received receiver_tail_received') /\
            Seq.equal sender_tail_sent' receiver_tail_received' /\
            conn_events_sent_seal_replay
              sender_after
              sender_rest
              sender_tail_sent'
              sender_tail_received'
              sender_final /\
            conn_events_received_decode_replay
              receiver_after
              receiver_rest
              receiver_tail_sent'
              receiver_tail_received'
              receiver_final
          with
            sender_model1
            receiver_model1
            ({
              pm_sender = sender;
              pm_receiver = receiver;
              pm_raw_sent = sender_delta_sent;
              pm_raw_received = receiver_delta_received;
            })
            sender_tail_sent
            sender_tail_received
            receiver_tail_sent
            receiver_tail_received
          and () ) )
    | _ ->
      assert False
  | _ ->
    assert False
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_protected_handshake_event_projection_pair_from_head_replays_with_next_alignment
  (sender:connection_model)
  (receiver:connection_model)
  (sender_after:connection_model)
  (receiver_after:connection_model)
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
        write_read_record_material_aligned sender receiver /\
        step_model
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some sender_after /\
        step_model
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some receiver_after /\
        sender_after.model_record.record_write ==
          R.next_seq sender.model_record.record_write /\
        receiver_after.model_record.record_read ==
          R.next_seq receiver.model_record.record_read /\
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
            received_msg /\
          write_read_record_material_aligned sender_after receiver_after)
=
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_conn_events_sent_seal_replay_head
    sender
    sent_ev
    sender_rest
    sender_raw_sent
    sender_raw_received
    sender_final;
  eliminate exists
    (sender_after0:connection_model)
    (sender_delta_sent:B.bytes)
    (sender_delta_received:B.bytes)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender sent_ev /\
    step_model sender sent_ev == Some sender_after0 /\
    event_raw_delta_legal sender sent_ev sender_delta_sent sender_delta_received /\
    sent_event_nonempty_seal_projection sender sent_ev sender_delta_sent /\
    Seq.equal sender_raw_sent (B.append sender_delta_sent sender_tail_sent) /\
    Seq.equal sender_raw_received (B.append sender_delta_received sender_tail_received) /\
    conn_events_sent_seal_replay
      sender_after0
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
        received_msg /\
      write_read_record_material_aligned sender_after receiver_after
  with _.
  ( lemma_conn_events_received_decode_replay_head
      receiver
      received_ev
      receiver_rest
      receiver_raw_sent
      receiver_raw_received
      receiver_final;
    eliminate exists
      (receiver_after0:connection_model)
      (receiver_delta_sent:B.bytes)
      (receiver_delta_received:B.bytes)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      legal_event receiver received_ev /\
      step_model receiver received_ev == Some receiver_after0 /\
      event_raw_delta_legal receiver received_ev receiver_delta_sent receiver_delta_received /\
      received_event_nonempty_decode_projection receiver received_ev receiver_delta_received /\
      Seq.equal receiver_raw_sent (B.append receiver_delta_sent receiver_tail_sent) /\
      Seq.equal receiver_raw_received (B.append receiver_delta_received receiver_tail_received) /\
      conn_events_received_decode_replay
        receiver_after0
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
          received_msg /\
        write_read_record_material_aligned sender_after receiver_after
    with _.
    ( assert (sender_after0 == sender_after);
      assert (receiver_after0 == receiver_after);
      assert (sender_after.model_record.record_write ==
        R.next_seq sender.model_record.record_write);
      assert (receiver_after.model_record.record_read ==
        R.next_seq receiver.model_record.record_read);
      lemma_next_seq_models_preserve_write_read_record_material_alignment
        sender
        receiver
        sender_after
        receiver_after;
      lemma_protected_handshake_event_projection_pair_from_head_replays
        sender
        receiver
        sent_msg
        received_msg
        sender_rest
        receiver_rest
        sender_raw_sent
        sender_raw_received
        receiver_raw_sent
        receiver_raw_received
        sender_final
        receiver_final;
      eliminate exists (pair:protected_message_replay).
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg
      returns
        exists pair.
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          write_read_record_material_aligned sender_after receiver_after
      with _.
      ( introduce exists
          (pair':protected_message_replay).
          pair'.pm_sender == sender /\
          pair'.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair'
            sent_msg
            received_msg /\
          write_read_record_material_aligned sender_after receiver_after
        with pair
        and () ) ) )

let lemma_protected_handshake_event_projection_pair_from_head_replays_with_next_alignment_and_tails
  (sender:connection_model)
  (receiver:connection_model)
  (sender_after:connection_model)
  (receiver_after:connection_model)
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
        write_read_record_material_aligned sender receiver /\
        step_model
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some sender_after /\
        step_model
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some receiver_after /\
        sender_after.model_record.record_write ==
          R.next_seq sender.model_record.record_write /\
        receiver_after.model_record.record_read ==
          R.next_seq receiver.model_record.record_read /\
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
        exists pair sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          write_read_record_material_aligned sender_after receiver_after /\
          Seq.equal sender_raw_sent (B.append pair.pm_raw_sent sender_tail_sent) /\
          Seq.equal receiver_raw_received (B.append pair.pm_raw_received receiver_tail_received) /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          conn_events_sent_seal_replay
            sender_after
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
    sender
    receiver
    sent_msg
    received_msg
    sender_rest
    receiver_rest
    sender_raw_sent
    sender_raw_received
    receiver_raw_sent
    receiver_raw_received
    sender_final
    receiver_final;
  eliminate exists
    (sender_after0:connection_model)
    (receiver_after0:connection_model)
    (pair:protected_message_replay)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes)
    (receiver_tail_sent:B.bytes)
    (receiver_tail_received:B.bytes).
    step_model sender sent_ev == Some sender_after0 /\
    step_model receiver received_ev == Some receiver_after0 /\
    pair.pm_sender == sender /\
    pair.pm_receiver == receiver /\
    protected_handshake_event_projection_pair
      pair
      sent_msg
      received_msg /\
    Seq.equal sender_raw_sent (B.append pair.pm_raw_sent sender_tail_sent) /\
    Seq.equal receiver_raw_received (B.append pair.pm_raw_received receiver_tail_received) /\
    Seq.equal sender_tail_sent receiver_tail_received /\
    conn_events_sent_seal_replay
      sender_after0
      sender_rest
      sender_tail_sent
      sender_tail_received
      sender_final /\
    conn_events_received_decode_replay
      receiver_after0
      receiver_rest
      receiver_tail_sent
      receiver_tail_received
      receiver_final
  returns
    exists pair sender_tail_sent sender_tail_received
      receiver_tail_sent receiver_tail_received.
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      write_read_record_material_aligned sender_after receiver_after /\
      Seq.equal sender_raw_sent (B.append pair.pm_raw_sent sender_tail_sent) /\
      Seq.equal receiver_raw_received (B.append pair.pm_raw_received receiver_tail_received) /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( assert (sender_after0 == sender_after);
    assert (receiver_after0 == receiver_after);
    lemma_next_seq_models_preserve_write_read_record_material_alignment
      sender
      receiver
      sender_after
      receiver_after;
    introduce exists
      (pair':protected_message_replay)
      (sender_tail_sent':B.bytes)
      (sender_tail_received':B.bytes)
      (receiver_tail_sent':B.bytes)
      (receiver_tail_received':B.bytes).
      pair'.pm_sender == sender /\
      pair'.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair'
        sent_msg
        received_msg /\
      write_read_record_material_aligned sender_after receiver_after /\
      Seq.equal sender_raw_sent (B.append pair'.pm_raw_sent sender_tail_sent') /\
      Seq.equal receiver_raw_received (B.append pair'.pm_raw_received receiver_tail_received') /\
      Seq.equal sender_tail_sent' receiver_tail_received' /\
      conn_events_sent_seal_replay
        sender_after
        sender_rest
        sender_tail_sent'
        sender_tail_received'
        sender_final /\
      conn_events_received_decode_replay
        receiver_after
        receiver_rest
        receiver_tail_sent'
        receiver_tail_received'
        receiver_final
    with pair sender_tail_sent sender_tail_received receiver_tail_sent receiver_tail_received
    and () )

let lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head
  (sender:connection_model)
  (sender_after:connection_model)
  (receiver:connection_model)
  (skip_ev:conn_event)
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
        step_model sender skip_ev == Some sender_after /\
        (match skip_ev with
         | ConnLocalEvent _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        sender_after.model_record.record_write.R.seq ==
          receiver.model_record.record_read.R.seq /\
        (match
          record_direction_material sender_after.model_record.record_write,
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
          (skip_ev :: ConnNetworkEvent {
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
          pair.pm_sender == sender_after /\
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
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender1:connection_model)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender skip_ev /\
    step_model sender skip_ev == Some sender1 /\
    Seq.equal sender_tail_sent receiver_raw_received /\
    conn_events_sent_seal_replay
      sender1
      (sent_ev :: sender_rest)
      sender_tail_sent
      sender_tail_received
      sender_final
  returns
    exists pair.
      pair.pm_sender == sender_after /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
  with _.
  ( assert (sender1 == sender_after);
    assert (
      conn_events_sent_seal_replay
        sender_after
        (sent_ev :: sender_rest)
        sender_tail_sent
        sender_tail_received
        sender_final);
    lemma_protected_handshake_event_projection_pair_from_head_replays
      sender_after
      receiver
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_tail_sent
      sender_tail_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final )

let lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head_with_tails
  (sender:connection_model)
  (sender_after:connection_model)
  (receiver:connection_model)
  (skip_ev:conn_event)
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
        step_model sender skip_ev == Some sender_after /\
        (match skip_ev with
         | ConnLocalEvent _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        write_read_record_material_aligned sender_after receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (skip_ev :: ConnNetworkEvent {
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
        exists sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          step_model
            sender_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          step_model
            receiver
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender1:connection_model)
    (sender_tail_sent0:B.bytes)
    (sender_tail_received0:B.bytes).
    legal_event sender skip_ev /\
    step_model sender skip_ev == Some sender1 /\
    Seq.equal sender_tail_sent0 receiver_raw_received /\
    conn_events_sent_seal_replay
      sender1
      (sent_ev :: sender_rest)
      sender_tail_sent0
      sender_tail_received0
      sender_final
  returns
    exists sender_after_head receiver_after_head pair
      sender_tail_sent sender_tail_received
      receiver_tail_sent receiver_tail_received.
      step_model sender_after sent_ev == Some sender_after_head /\
      step_model receiver received_ev == Some receiver_after_head /\
      pair.pm_sender == sender_after /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( assert (sender1 == sender_after);
    lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
      sender_after
      receiver
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_tail_sent0
      sender_tail_received0
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists
      (sender_after_head0:connection_model)
      (receiver_after_head0:connection_model)
      (pair0:protected_message_replay)
      (sender_tail_sent:B.bytes)
      (sender_tail_received:B.bytes)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      step_model sender_after sent_ev == Some sender_after_head0 /\
      step_model receiver received_ev == Some receiver_after_head0 /\
      pair0.pm_sender == sender_after /\
      pair0.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair0
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent0 (B.append pair0.pm_raw_sent sender_tail_sent) /\
      Seq.equal receiver_raw_received (B.append pair0.pm_raw_received receiver_tail_received) /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head0
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head0
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    returns
      exists sender_after_head receiver_after_head pair
        sender_tail_sent' sender_tail_received'
        receiver_tail_sent' receiver_tail_received'.
        step_model sender_after sent_ev == Some sender_after_head /\
        step_model receiver received_ev == Some receiver_after_head /\
        pair.pm_sender == sender_after /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
    with _.
    ( introduce exists
        (sender_after_head:connection_model)
        (receiver_after_head:connection_model)
        (pair:protected_message_replay)
        (sender_tail_sent':B.bytes)
        (sender_tail_received':B.bytes)
        (receiver_tail_sent':B.bytes)
        (receiver_tail_received':B.bytes).
        step_model sender_after sent_ev == Some sender_after_head /\
        step_model receiver received_ev == Some receiver_after_head /\
        pair.pm_sender == sender_after /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
      with
        sender_after_head0
        receiver_after_head0
        pair0
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head
  (sender:connection_model)
  (receiver:connection_model)
  (receiver_after:connection_model)
  (skip_ev:conn_event)
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
        step_model receiver skip_ev == Some receiver_after /\
        (match skip_ev with
         | ConnLocalEvent _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        sender.model_record.record_write.R.seq ==
          receiver_after.model_record.record_read.R.seq /\
        (match
          record_direction_material sender.model_record.record_write,
          record_direction_material receiver_after.model_record.record_read
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
          (skip_ev :: ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair.
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver_after /\
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
  lemma_received_replay_skip_empty_head_preserves_peer_stream
    sender_raw_sent
    receiver
    skip_ev
    (received_ev :: receiver_rest)
    receiver_raw_sent
    receiver_raw_received
    receiver_final;
  eliminate exists
    (receiver1:connection_model)
    (receiver_tail_sent:B.bytes)
    (receiver_tail_received:B.bytes).
    legal_event receiver skip_ev /\
    step_model receiver skip_ev == Some receiver1 /\
    Seq.equal sender_raw_sent receiver_tail_received /\
    conn_events_received_decode_replay
      receiver1
      (received_ev :: receiver_rest)
      receiver_tail_sent
      receiver_tail_received
      receiver_final
  returns
    exists pair.
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
  with _.
  ( assert (receiver1 == receiver_after);
    assert (
      conn_events_received_decode_replay
        receiver_after
        (received_ev :: receiver_rest)
        receiver_tail_sent
        receiver_tail_received
        receiver_final);
    lemma_protected_handshake_event_projection_pair_from_head_replays
      sender
      receiver_after
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_tail_sent
      receiver_tail_received
      sender_final
      receiver_final )

let lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head_with_tails
  (sender:connection_model)
  (receiver:connection_model)
  (receiver_after:connection_model)
  (skip_ev:conn_event)
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
        step_model receiver skip_ev == Some receiver_after /\
        (match skip_ev with
         | ConnLocalEvent _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        write_read_record_material_aligned sender receiver_after /\
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
          (skip_ev :: ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          step_model
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          step_model
            receiver_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_received_replay_skip_empty_head_preserves_peer_stream
    sender_raw_sent
    receiver
    skip_ev
    (received_ev :: receiver_rest)
    receiver_raw_sent
    receiver_raw_received
    receiver_final;
  eliminate exists
    (receiver1:connection_model)
    (receiver_tail_sent0:B.bytes)
    (receiver_tail_received0:B.bytes).
    legal_event receiver skip_ev /\
    step_model receiver skip_ev == Some receiver1 /\
    Seq.equal sender_raw_sent receiver_tail_received0 /\
    conn_events_received_decode_replay
      receiver1
      (received_ev :: receiver_rest)
      receiver_tail_sent0
      receiver_tail_received0
      receiver_final
  returns
    exists sender_after_head receiver_after_head pair
      sender_tail_sent sender_tail_received
      receiver_tail_sent receiver_tail_received.
      step_model sender sent_ev == Some sender_after_head /\
      step_model receiver_after received_ev == Some receiver_after_head /\
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( assert (receiver1 == receiver_after);
    lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
      sender
      receiver_after
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_tail_sent0
      receiver_tail_received0
      sender_final
      receiver_final;
    eliminate exists
      (sender_after_head0:connection_model)
      (receiver_after_head0:connection_model)
      (pair0:protected_message_replay)
      (sender_tail_sent:B.bytes)
      (sender_tail_received:B.bytes)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      step_model sender sent_ev == Some sender_after_head0 /\
      step_model receiver_after received_ev == Some receiver_after_head0 /\
      pair0.pm_sender == sender /\
      pair0.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair0
        sent_msg
        received_msg /\
      Seq.equal sender_raw_sent (B.append pair0.pm_raw_sent sender_tail_sent) /\
      Seq.equal receiver_tail_received0 (B.append pair0.pm_raw_received receiver_tail_received) /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head0
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head0
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    returns
      exists sender_after_head receiver_after_head pair
        sender_tail_sent' sender_tail_received'
        receiver_tail_sent' receiver_tail_received'.
        step_model sender sent_ev == Some sender_after_head /\
        step_model receiver_after received_ev == Some receiver_after_head /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
    with _.
    ( introduce exists
        (sender_after_head:connection_model)
        (receiver_after_head:connection_model)
        (pair:protected_message_replay)
        (sender_tail_sent':B.bytes)
        (sender_tail_received':B.bytes)
        (receiver_tail_sent':B.bytes)
        (receiver_tail_received':B.bytes).
        step_model sender sent_ev == Some sender_after_head /\
        step_model receiver_after received_ev == Some receiver_after_head /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
      with
        sender_after_head0
        receiver_after_head0
        pair0
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_both_skip_empty_heads
  (sender:connection_model)
  (sender_after:connection_model)
  (receiver:connection_model)
  (receiver_after:connection_model)
  (sender_skip_ev:conn_event)
  (receiver_skip_ev:conn_event)
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
        step_model sender sender_skip_ev == Some sender_after /\
        step_model receiver receiver_skip_ev == Some receiver_after /\
        (match sender_skip_ev with
         | ConnLocalEvent _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        (match receiver_skip_ev with
         | ConnLocalEvent _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        sender_after.model_record.record_write.R.seq ==
          receiver_after.model_record.record_read.R.seq /\
        (match
          record_direction_material sender_after.model_record.record_write,
          record_direction_material receiver_after.model_record.record_read
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
          (sender_skip_ev :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (receiver_skip_ev :: ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair.
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver_after /\
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
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    sender_skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender1:connection_model)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender sender_skip_ev /\
    step_model sender sender_skip_ev == Some sender1 /\
    Seq.equal sender_tail_sent receiver_raw_received /\
    conn_events_sent_seal_replay
      sender1
      (sent_ev :: sender_rest)
      sender_tail_sent
      sender_tail_received
      sender_final
  returns
    exists pair.
      pair.pm_sender == sender_after /\
      pair.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
  with _.
  ( assert (sender1 == sender_after);
    lemma_received_replay_skip_empty_head_preserves_peer_stream
      sender_tail_sent
      receiver
      receiver_skip_ev
      (received_ev :: receiver_rest)
      receiver_raw_sent
      receiver_raw_received
      receiver_final;
    eliminate exists
      (receiver1:connection_model)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      legal_event receiver receiver_skip_ev /\
      step_model receiver receiver_skip_ev == Some receiver1 /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_received_decode_replay
        receiver1
        (received_ev :: receiver_rest)
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    returns
      exists pair.
        pair.pm_sender == sender_after /\
        pair.pm_receiver == receiver_after /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg
    with _.
    ( assert (receiver1 == receiver_after);
      assert (
        conn_events_sent_seal_replay
          sender_after
          (sent_ev :: sender_rest)
          sender_tail_sent
          sender_tail_received
          sender_final);
      assert (
        conn_events_received_decode_replay
          receiver_after
          (received_ev :: receiver_rest)
          receiver_tail_sent
          receiver_tail_received
          receiver_final);
      lemma_protected_handshake_event_projection_pair_from_head_replays
        sender_after
        receiver_after
        sent_msg
        received_msg
        sender_rest
        receiver_rest
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
        sender_final
        receiver_final ) )

let lemma_protected_handshake_event_projection_pair_after_both_skip_empty_heads_with_tails
  (sender:connection_model)
  (sender_after:connection_model)
  (receiver:connection_model)
  (receiver_after:connection_model)
  (sender_skip_ev:conn_event)
  (receiver_skip_ev:conn_event)
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
        step_model sender sender_skip_ev == Some sender_after /\
        step_model receiver receiver_skip_ev == Some receiver_after /\
        (match sender_skip_ev with
         | ConnLocalEvent _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        (match receiver_skip_ev with
         | ConnLocalEvent _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        write_read_record_material_aligned sender_after receiver_after /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (sender_skip_ev :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (receiver_skip_ev :: ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          step_model
            sender_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          step_model
            receiver_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    sender_skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender1:connection_model)
    (sender_tail_sent0:B.bytes)
    (sender_tail_received0:B.bytes).
    legal_event sender sender_skip_ev /\
    step_model sender sender_skip_ev == Some sender1 /\
    Seq.equal sender_tail_sent0 receiver_raw_received /\
    conn_events_sent_seal_replay
      sender1
      (sent_ev :: sender_rest)
      sender_tail_sent0
      sender_tail_received0
      sender_final
  returns
    exists sender_after_head receiver_after_head pair
      sender_tail_sent sender_tail_received
      receiver_tail_sent receiver_tail_received.
      step_model sender_after sent_ev == Some sender_after_head /\
      step_model receiver_after received_ev == Some receiver_after_head /\
      pair.pm_sender == sender_after /\
      pair.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( assert (sender1 == sender_after);
    lemma_received_replay_skip_empty_head_preserves_peer_stream
      sender_tail_sent0
      receiver
      receiver_skip_ev
      (received_ev :: receiver_rest)
      receiver_raw_sent
      receiver_raw_received
      receiver_final;
    eliminate exists
      (receiver1:connection_model)
      (receiver_tail_sent0:B.bytes)
      (receiver_tail_received0:B.bytes).
      legal_event receiver receiver_skip_ev /\
      step_model receiver receiver_skip_ev == Some receiver1 /\
      Seq.equal sender_tail_sent0 receiver_tail_received0 /\
      conn_events_received_decode_replay
        receiver1
        (received_ev :: receiver_rest)
        receiver_tail_sent0
        receiver_tail_received0
        receiver_final
    returns
      exists sender_after_head receiver_after_head pair
        sender_tail_sent sender_tail_received
        receiver_tail_sent receiver_tail_received.
        step_model sender_after sent_ev == Some sender_after_head /\
        step_model receiver_after received_ev == Some receiver_after_head /\
        pair.pm_sender == sender_after /\
        pair.pm_receiver == receiver_after /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent receiver_tail_received /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent
          sender_tail_received
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent
          receiver_tail_received
          receiver_final
    with _.
    ( assert (receiver1 == receiver_after);
      lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
        sender_after
        receiver_after
        sent_msg
        received_msg
        sender_rest
        receiver_rest
        sender_tail_sent0
        sender_tail_received0
        receiver_tail_sent0
        receiver_tail_received0
        sender_final
        receiver_final;
      eliminate exists
        (sender_after_head0:connection_model)
        (receiver_after_head0:connection_model)
        (pair0:protected_message_replay)
        (sender_tail_sent:B.bytes)
        (sender_tail_received:B.bytes)
        (receiver_tail_sent:B.bytes)
        (receiver_tail_received:B.bytes).
        step_model sender_after sent_ev == Some sender_after_head0 /\
        step_model receiver_after received_ev == Some receiver_after_head0 /\
        pair0.pm_sender == sender_after /\
        pair0.pm_receiver == receiver_after /\
        protected_handshake_event_projection_pair
          pair0
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent0 (B.append pair0.pm_raw_sent sender_tail_sent) /\
        Seq.equal receiver_tail_received0 (B.append pair0.pm_raw_received receiver_tail_received) /\
        Seq.equal sender_tail_sent receiver_tail_received /\
        conn_events_sent_seal_replay
          sender_after_head0
          sender_rest
          sender_tail_sent
          sender_tail_received
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head0
          receiver_rest
          receiver_tail_sent
          receiver_tail_received
          receiver_final
      returns
        exists sender_after_head receiver_after_head pair
          sender_tail_sent' sender_tail_received'
          receiver_tail_sent' receiver_tail_received'.
          step_model sender_after sent_ev == Some sender_after_head /\
          step_model receiver_after received_ev == Some receiver_after_head /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent' receiver_tail_received' /\
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent'
            sender_tail_received'
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent'
            receiver_tail_received'
            receiver_final
      with _.
      ( introduce exists
          (sender_after_head:connection_model)
          (receiver_after_head:connection_model)
          (pair:protected_message_replay)
          (sender_tail_sent':B.bytes)
          (sender_tail_received':B.bytes)
          (receiver_tail_sent':B.bytes)
          (receiver_tail_received':B.bytes).
          step_model sender_after sent_ev == Some sender_after_head /\
          step_model receiver_after received_ev == Some receiver_after_head /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent' receiver_tail_received' /\
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent'
            sender_tail_received'
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent'
            receiver_tail_received'
            receiver_final
        with
          sender_after_head0
          receiver_after_head0
          pair0
          sender_tail_sent
          sender_tail_received
          receiver_tail_sent
          receiver_tail_received
        and () ) ) )

let lemma_protected_handshake_event_projection_pair_after_sender_received_network_head
  (sender:connection_model)
  (receiver:connection_model)
  (skip_msg:M.tls_message)
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
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = skip_msg;
          } :: ConnNetworkEvent {
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
        exists sender_after pair.
          step_model
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = skip_msg;
            }) == Some sender_after /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)
=
  let skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = skip_msg;
  } in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender_after:connection_model)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender skip_ev /\
    step_model sender skip_ev == Some sender_after /\
    Seq.equal sender_tail_sent receiver_raw_received /\
    conn_events_sent_seal_replay
      sender_after
      (sent_ev :: sender_rest)
      sender_tail_sent
      sender_tail_received
      sender_final
  returns
    exists sender_after' pair.
      step_model sender skip_ev == Some sender_after' /\
      pair.pm_sender == sender_after' /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
  with _.
  ( lemma_step_received_network_event_preserves_write_read_record_material_alignment
      sender
      skip_msg
      sender_after
      receiver;
    lemma_protected_handshake_event_projection_pair_from_head_replays
      sender_after
      receiver
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_tail_sent
      sender_tail_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists (pair:protected_message_replay).
      pair.pm_sender == sender_after /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
    returns
      exists sender_after' pair.
        step_model sender skip_ev == Some sender_after' /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg
    with _.
    ( introduce exists
        (sender_after':connection_model)
        (pair':protected_message_replay).
        step_model sender skip_ev == Some sender_after' /\
        pair'.pm_sender == sender_after' /\
        pair'.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair'
          sent_msg
          received_msg
      with sender_after pair
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_sender_received_network_head_with_tails
  (sender:connection_model)
  (receiver:connection_model)
  (skip_msg:M.tls_message)
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
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = skip_msg;
          } :: ConnNetworkEvent {
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
        exists sender_after sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          step_model
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = skip_msg;
            }) == Some sender_after /\
          step_model
            sender_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          step_model
            receiver
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = skip_msg;
  } in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender_after:connection_model)
    (sender_tail_sent0:B.bytes)
    (sender_tail_received0:B.bytes).
    legal_event sender skip_ev /\
    step_model sender skip_ev == Some sender_after /\
    Seq.equal sender_tail_sent0 receiver_raw_received /\
    conn_events_sent_seal_replay
      sender_after
      (sent_ev :: sender_rest)
      sender_tail_sent0
      sender_tail_received0
      sender_final
  returns
    exists sender_after' sender_after_head receiver_after_head pair
      sender_tail_sent sender_tail_received
      receiver_tail_sent receiver_tail_received.
      step_model sender skip_ev == Some sender_after' /\
      step_model sender_after' sent_ev == Some sender_after_head /\
      step_model receiver received_ev == Some receiver_after_head /\
      pair.pm_sender == sender_after' /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( lemma_step_received_network_event_preserves_write_read_record_material_alignment
      sender
      skip_msg
      sender_after
      receiver;
    lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head_with_tails
      sender
      sender_after
      receiver
      skip_ev
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists
      (sender_after_head0:connection_model)
      (receiver_after_head0:connection_model)
      (pair0:protected_message_replay)
      (sender_tail_sent:B.bytes)
      (sender_tail_received:B.bytes)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      step_model sender_after sent_ev == Some sender_after_head0 /\
      step_model receiver received_ev == Some receiver_after_head0 /\
      pair0.pm_sender == sender_after /\
      pair0.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair0
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head0
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head0
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    returns
      exists sender_after' sender_after_head receiver_after_head pair
        sender_tail_sent' sender_tail_received'
        receiver_tail_sent' receiver_tail_received'.
        step_model sender skip_ev == Some sender_after' /\
        step_model sender_after' sent_ev == Some sender_after_head /\
        step_model receiver received_ev == Some receiver_after_head /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
    with _.
    ( introduce exists
        (sender_after':connection_model)
        (sender_after_head:connection_model)
        (receiver_after_head:connection_model)
        (pair:protected_message_replay)
        (sender_tail_sent':B.bytes)
        (sender_tail_received':B.bytes)
        (receiver_tail_sent':B.bytes)
        (receiver_tail_received':B.bytes).
        step_model sender skip_ev == Some sender_after' /\
        step_model sender_after' sent_ev == Some sender_after_head /\
        step_model receiver received_ev == Some receiver_after_head /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
      with
        sender_after
        sender_after_head0
        receiver_after_head0
        pair0
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_receiver_sent_network_head
  (sender:connection_model)
  (receiver:connection_model)
  (skip_msg:M.tls_message)
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
        write_read_record_material_aligned sender receiver /\
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
            CL.message_direction = CL.Sent;
            CL.message_value = skip_msg;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists receiver_after pair.
          step_model
            receiver
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = skip_msg;
            }) == Some receiver_after /\
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)
=
  let skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = skip_msg;
  } in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_received_replay_skip_empty_head_preserves_peer_stream
    sender_raw_sent
    receiver
    skip_ev
    (received_ev :: receiver_rest)
    receiver_raw_sent
    receiver_raw_received
    receiver_final;
  eliminate exists
    (receiver_after:connection_model)
    (receiver_tail_sent:B.bytes)
    (receiver_tail_received:B.bytes).
    legal_event receiver skip_ev /\
    step_model receiver skip_ev == Some receiver_after /\
    Seq.equal sender_raw_sent receiver_tail_received /\
    conn_events_received_decode_replay
      receiver_after
      (received_ev :: receiver_rest)
      receiver_tail_sent
      receiver_tail_received
      receiver_final
  returns
    exists receiver_after' pair.
      step_model receiver skip_ev == Some receiver_after' /\
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after' /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
  with _.
  ( lemma_step_sent_network_event_preserves_write_read_record_material_alignment
      sender
      receiver
      skip_msg
      receiver_after;
    lemma_protected_handshake_event_projection_pair_from_head_replays
      sender
      receiver_after
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_tail_sent
      receiver_tail_received
      sender_final
      receiver_final;
    eliminate exists (pair:protected_message_replay).
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
    returns
      exists receiver_after' pair.
        step_model receiver skip_ev == Some receiver_after' /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg
    with _.
    ( introduce exists
        (receiver_after':connection_model)
        (pair':protected_message_replay).
        step_model receiver skip_ev == Some receiver_after' /\
        pair'.pm_sender == sender /\
        pair'.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
          pair'
          sent_msg
          received_msg
      with receiver_after pair
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_receiver_sent_network_head_with_tails
  (sender:connection_model)
  (receiver:connection_model)
  (skip_msg:M.tls_message)
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
        write_read_record_material_aligned sender receiver /\
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
            CL.message_direction = CL.Sent;
            CL.message_value = skip_msg;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists receiver_after sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          step_model
            receiver
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = skip_msg;
            }) == Some receiver_after /\
          step_model
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          step_model
            receiver_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = skip_msg;
  } in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_received_replay_skip_empty_head_preserves_peer_stream
    sender_raw_sent
    receiver
    skip_ev
    (received_ev :: receiver_rest)
    receiver_raw_sent
    receiver_raw_received
    receiver_final;
  eliminate exists
    (receiver_after:connection_model)
    (receiver_tail_sent0:B.bytes)
    (receiver_tail_received0:B.bytes).
    legal_event receiver skip_ev /\
    step_model receiver skip_ev == Some receiver_after /\
    Seq.equal sender_raw_sent receiver_tail_received0 /\
    conn_events_received_decode_replay
      receiver_after
      (received_ev :: receiver_rest)
      receiver_tail_sent0
      receiver_tail_received0
      receiver_final
  returns
    exists receiver_after' sender_after_head receiver_after_head pair
      sender_tail_sent sender_tail_received
      receiver_tail_sent receiver_tail_received.
      step_model receiver skip_ev == Some receiver_after' /\
      step_model sender sent_ev == Some sender_after_head /\
      step_model receiver_after' received_ev == Some receiver_after_head /\
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after' /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( lemma_step_sent_network_event_preserves_write_read_record_material_alignment
      sender
      receiver
      skip_msg
      receiver_after;
    lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head_with_tails
      sender
      receiver
      receiver_after
      skip_ev
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists
      (sender_after_head0:connection_model)
      (receiver_after_head0:connection_model)
      (pair0:protected_message_replay)
      (sender_tail_sent:B.bytes)
      (sender_tail_received:B.bytes)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      step_model sender sent_ev == Some sender_after_head0 /\
      step_model receiver_after received_ev == Some receiver_after_head0 /\
      pair0.pm_sender == sender /\
      pair0.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair0
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head0
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head0
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    returns
      exists receiver_after' sender_after_head receiver_after_head pair
        sender_tail_sent' sender_tail_received'
        receiver_tail_sent' receiver_tail_received'.
        step_model receiver skip_ev == Some receiver_after' /\
        step_model sender sent_ev == Some sender_after_head /\
        step_model receiver_after' received_ev == Some receiver_after_head /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
    with _.
    ( introduce exists
        (receiver_after':connection_model)
        (sender_after_head:connection_model)
        (receiver_after_head:connection_model)
        (pair:protected_message_replay)
        (sender_tail_sent':B.bytes)
        (sender_tail_received':B.bytes)
        (receiver_tail_sent':B.bytes)
        (receiver_tail_received':B.bytes).
        step_model receiver skip_ev == Some receiver_after' /\
        step_model sender sent_ev == Some sender_after_head /\
        step_model receiver_after' received_ev == Some receiver_after_head /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
      with
        receiver_after
        sender_after_head0
        receiver_after_head0
        pair0
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_opposite_network_heads
  (sender:connection_model)
  (receiver:connection_model)
  (sender_skip_msg:M.tls_message)
  (receiver_skip_msg:M.tls_message)
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
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = sender_skip_msg;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = receiver_skip_msg;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after receiver_after pair.
          step_model
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = sender_skip_msg;
            }) == Some sender_after /\
          step_model
            receiver
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = receiver_skip_msg;
            }) == Some receiver_after /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)
=
  let sender_skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = sender_skip_msg;
  } in
  let receiver_skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = receiver_skip_msg;
  } in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    sender_skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender_after:connection_model)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender sender_skip_ev /\
    step_model sender sender_skip_ev == Some sender_after /\
    Seq.equal sender_tail_sent receiver_raw_received /\
    conn_events_sent_seal_replay
      sender_after
      (sent_ev :: sender_rest)
      sender_tail_sent
      sender_tail_received
      sender_final
  returns
    exists sender_after' receiver_after pair.
      step_model sender sender_skip_ev == Some sender_after' /\
      step_model receiver receiver_skip_ev == Some receiver_after /\
      pair.pm_sender == sender_after' /\
      pair.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
  with _.
  ( lemma_received_replay_skip_empty_head_preserves_peer_stream
      sender_tail_sent
      receiver
      receiver_skip_ev
      (received_ev :: receiver_rest)
      receiver_raw_sent
      receiver_raw_received
      receiver_final;
    eliminate exists
      (receiver_after:connection_model)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      legal_event receiver receiver_skip_ev /\
      step_model receiver receiver_skip_ev == Some receiver_after /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_received_decode_replay
        receiver_after
        (received_ev :: receiver_rest)
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    returns
      exists sender_after' receiver_after' pair.
        step_model sender sender_skip_ev == Some sender_after' /\
        step_model receiver receiver_skip_ev == Some receiver_after' /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg
    with _.
    ( lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
        sender
        sender_skip_msg
        sender_after
        receiver
        receiver_skip_msg
        receiver_after;
      lemma_protected_handshake_event_projection_pair_from_head_replays
        sender_after
        receiver_after
        sent_msg
        received_msg
        sender_rest
        receiver_rest
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
        sender_final
        receiver_final;
      eliminate exists (pair:protected_message_replay).
        pair.pm_sender == sender_after /\
        pair.pm_receiver == receiver_after /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg
      returns
        exists sender_after' receiver_after' pair.
          step_model sender sender_skip_ev == Some sender_after' /\
          step_model receiver receiver_skip_ev == Some receiver_after' /\
          pair.pm_sender == sender_after' /\
          pair.pm_receiver == receiver_after' /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg
      with _.
      ( introduce exists
          (sender_after':connection_model)
          (receiver_after':connection_model)
          (pair':protected_message_replay).
          step_model sender sender_skip_ev == Some sender_after' /\
          step_model receiver receiver_skip_ev == Some receiver_after' /\
          pair'.pm_sender == sender_after' /\
          pair'.pm_receiver == receiver_after' /\
          protected_handshake_event_projection_pair
            pair'
            sent_msg
            received_msg
        with sender_after receiver_after pair
        and () ) ) )

let lemma_protected_handshake_event_projection_pair_after_opposite_network_heads_with_tails
  (sender:connection_model)
  (receiver:connection_model)
  (sender_skip_msg:M.tls_message)
  (receiver_skip_msg:M.tls_message)
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
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = sender_skip_msg;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            } :: sender_rest)
            sender_raw_sent
            sender_raw_received
            sender_final /\
        conn_events_received_decode_replay
            receiver
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = receiver_skip_msg;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            } :: receiver_rest)
            receiver_raw_sent
            receiver_raw_received
            receiver_final)
      (ensures
        exists sender_after receiver_after sender_after_head receiver_after_head pair
            sender_tail_sent sender_tail_received
            receiver_tail_sent receiver_tail_received.
            step_model
              sender
              (ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = sender_skip_msg;
              }) == Some sender_after /\
            step_model
              receiver
              (ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = receiver_skip_msg;
              }) == Some receiver_after /\
            step_model
              sender_after
              (ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake sent_msg;
              }) == Some sender_after_head /\
            step_model
              receiver_after
              (ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake received_msg;
              }) == Some receiver_after_head /\
            pair.pm_sender == sender_after /\
            pair.pm_receiver == receiver_after /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg /\
            Seq.equal sender_tail_sent receiver_tail_received /\
            conn_events_sent_seal_replay
              sender_after_head
              sender_rest
              sender_tail_sent
              sender_tail_received
              sender_final /\
            conn_events_received_decode_replay
              receiver_after_head
              receiver_rest
              receiver_tail_sent
              receiver_tail_received
              receiver_final)
=
  let sender_skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = sender_skip_msg;
  } in
  let receiver_skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = receiver_skip_msg;
  } in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    sender_skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender_after:connection_model)
    (sender_tail_sent0:B.bytes)
    (sender_tail_received0:B.bytes).
    legal_event sender sender_skip_ev /\
    step_model sender sender_skip_ev == Some sender_after /\
    Seq.equal sender_tail_sent0 receiver_raw_received /\
    conn_events_sent_seal_replay
      sender_after
      (sent_ev :: sender_rest)
      sender_tail_sent0
      sender_tail_received0
      sender_final
  returns
    exists sender_after' receiver_after sender_after_head receiver_after_head pair
      sender_tail_sent sender_tail_received
      receiver_tail_sent receiver_tail_received.
      step_model sender sender_skip_ev == Some sender_after' /\
      step_model receiver receiver_skip_ev == Some receiver_after /\
      step_model sender_after' sent_ev == Some sender_after_head /\
      step_model receiver_after received_ev == Some receiver_after_head /\
      pair.pm_sender == sender_after' /\
      pair.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( lemma_received_replay_skip_empty_head_preserves_peer_stream
      sender_tail_sent0
      receiver
      receiver_skip_ev
      (received_ev :: receiver_rest)
      receiver_raw_sent
      receiver_raw_received
      receiver_final;
    eliminate exists
      (receiver_after:connection_model)
      (receiver_tail_sent0:B.bytes)
      (receiver_tail_received0:B.bytes).
      legal_event receiver receiver_skip_ev /\
      step_model receiver receiver_skip_ev == Some receiver_after /\
      Seq.equal sender_tail_sent0 receiver_tail_received0 /\
      conn_events_received_decode_replay
        receiver_after
        (received_ev :: receiver_rest)
        receiver_tail_sent0
        receiver_tail_received0
        receiver_final
    returns
      exists sender_after' receiver_after' sender_after_head receiver_after_head pair
        sender_tail_sent sender_tail_received
        receiver_tail_sent receiver_tail_received.
        step_model sender sender_skip_ev == Some sender_after' /\
        step_model receiver receiver_skip_ev == Some receiver_after' /\
        step_model sender_after' sent_ev == Some sender_after_head /\
        step_model receiver_after' received_ev == Some receiver_after_head /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
        Seq.equal sender_tail_sent receiver_tail_received /\
        conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
        conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final
    with _.
    ( lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
        sender
        sender_skip_msg
        sender_after
        receiver
        receiver_skip_msg
        receiver_after;
      lemma_protected_handshake_event_projection_pair_after_both_skip_empty_heads_with_tails
        sender
        sender_after
        receiver
        receiver_after
        sender_skip_ev
        receiver_skip_ev
        sent_msg
        received_msg
        sender_rest
        receiver_rest
        sender_raw_sent
        sender_raw_received
        receiver_raw_sent
        receiver_raw_received
        sender_final
        receiver_final;
      eliminate exists
        (sender_after_head0:connection_model)
        (receiver_after_head0:connection_model)
        (pair0:protected_message_replay)
        (sender_tail_sent:B.bytes)
        (sender_tail_received:B.bytes)
        (receiver_tail_sent:B.bytes)
        (receiver_tail_received:B.bytes).
        step_model sender_after sent_ev == Some sender_after_head0 /\
        step_model receiver_after received_ev == Some receiver_after_head0 /\
        pair0.pm_sender == sender_after /\
        pair0.pm_receiver == receiver_after /\
        protected_handshake_event_projection_pair
            pair0
            sent_msg
            received_msg /\
        Seq.equal sender_tail_sent receiver_tail_received /\
        conn_events_sent_seal_replay
            sender_after_head0
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
        conn_events_received_decode_replay
            receiver_after_head0
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final
      returns
        exists sender_after' receiver_after' sender_after_head receiver_after_head pair
            sender_tail_sent' sender_tail_received'
            receiver_tail_sent' receiver_tail_received'.
            step_model sender sender_skip_ev == Some sender_after' /\
            step_model receiver receiver_skip_ev == Some receiver_after' /\
            step_model sender_after' sent_ev == Some sender_after_head /\
            step_model receiver_after' received_ev == Some receiver_after_head /\
            pair.pm_sender == sender_after' /\
            pair.pm_receiver == receiver_after' /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg /\
            Seq.equal sender_tail_sent' receiver_tail_received' /\
            conn_events_sent_seal_replay
              sender_after_head
              sender_rest
              sender_tail_sent'
              sender_tail_received'
              sender_final /\
            conn_events_received_decode_replay
              receiver_after_head
              receiver_rest
              receiver_tail_sent'
              receiver_tail_received'
              receiver_final
      with _.
      ( introduce exists
            (sender_after':connection_model)
            (receiver_after':connection_model)
            (sender_after_head:connection_model)
            (receiver_after_head:connection_model)
            (pair:protected_message_replay)
            (sender_tail_sent':B.bytes)
            (sender_tail_received':B.bytes)
            (receiver_tail_sent':B.bytes)
            (receiver_tail_received':B.bytes).
            step_model sender sender_skip_ev == Some sender_after' /\
            step_model receiver receiver_skip_ev == Some receiver_after' /\
            step_model sender_after' sent_ev == Some sender_after_head /\
            step_model receiver_after' received_ev == Some receiver_after_head /\
            pair.pm_sender == sender_after' /\
            pair.pm_receiver == receiver_after' /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg /\
            Seq.equal sender_tail_sent' receiver_tail_received' /\
            conn_events_sent_seal_replay
              sender_after_head
              sender_rest
              sender_tail_sent'
              sender_tail_received'
              sender_final /\
            conn_events_received_decode_replay
              receiver_after_head
              receiver_rest
              receiver_tail_sent'
              receiver_tail_received'
              receiver_final
        with
            sender_after
            receiver_after
            sender_after_head0
            receiver_after_head0
            pair0
            sender_tail_sent
            sender_tail_received
            receiver_tail_sent
            receiver_tail_received
        and () ) ) )

let lemma_protected_handshake_event_projection_pair_after_sender_non_install_local_head
  (sender:connection_model)
  (receiver:connection_model)
  (skip:local_event)
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
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
            sender
            (ConnLocalEvent skip :: ConnNetworkEvent {
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
        exists sender_after pair.
            step_model sender (ConnLocalEvent skip) == Some sender_after /\
            pair.pm_sender == sender_after /\
            pair.pm_receiver == receiver /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg)
=
  let skip_ev = ConnLocalEvent skip in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender_after:connection_model)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender skip_ev /\
    step_model sender skip_ev == Some sender_after /\
    Seq.equal sender_tail_sent receiver_raw_received /\
    conn_events_sent_seal_replay
      sender_after
      (sent_ev :: sender_rest)
      sender_tail_sent
      sender_tail_received
      sender_final
  returns
    exists sender_after' pair.
      step_model sender skip_ev == Some sender_after' /\
      pair.pm_sender == sender_after' /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
  with _.
  ( lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
      sender
      skip
      sender_after
      receiver;
    lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head
      sender
      sender_after
      receiver
      skip_ev
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists (pair:protected_message_replay).
      pair.pm_sender == sender_after /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
    returns
      exists sender_after' pair.
        step_model sender skip_ev == Some sender_after' /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg
    with _.
    ( introduce exists
        (sender_after':connection_model)
        (pair':protected_message_replay).
        step_model sender skip_ev == Some sender_after' /\
        pair'.pm_sender == sender_after' /\
        pair'.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
            pair'
            sent_msg
            received_msg
      with sender_after pair
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_sender_non_install_local_head_with_tails
  (sender:connection_model)
  (receiver:connection_model)
  (skip:local_event)
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
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (ConnLocalEvent skip :: ConnNetworkEvent {
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
        exists sender_after sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          step_model sender (ConnLocalEvent skip) == Some sender_after /\
          step_model
            sender_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          step_model
            receiver
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let skip_ev = ConnLocalEvent skip in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender_after:connection_model)
    (sender_tail_sent0:B.bytes)
    (sender_tail_received0:B.bytes).
    legal_event sender skip_ev /\
    step_model sender skip_ev == Some sender_after /\
    Seq.equal sender_tail_sent0 receiver_raw_received /\
    conn_events_sent_seal_replay
      sender_after
      (sent_ev :: sender_rest)
      sender_tail_sent0
      sender_tail_received0
      sender_final
  returns
    exists sender_after' sender_after_head receiver_after_head pair
      sender_tail_sent sender_tail_received
      receiver_tail_sent receiver_tail_received.
      step_model sender skip_ev == Some sender_after' /\
      step_model sender_after' sent_ev == Some sender_after_head /\
      step_model receiver received_ev == Some receiver_after_head /\
      pair.pm_sender == sender_after' /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
      sender
      skip
      sender_after
      receiver;
    lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head_with_tails
      sender
      sender_after
      receiver
      skip_ev
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists
      (sender_after_head0:connection_model)
      (receiver_after_head0:connection_model)
      (pair0:protected_message_replay)
      (sender_tail_sent:B.bytes)
      (sender_tail_received:B.bytes)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      step_model sender_after sent_ev == Some sender_after_head0 /\
      step_model receiver received_ev == Some receiver_after_head0 /\
      pair0.pm_sender == sender_after /\
      pair0.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair0
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head0
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head0
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    returns
      exists sender_after' sender_after_head receiver_after_head pair
        sender_tail_sent' sender_tail_received'
        receiver_tail_sent' receiver_tail_received'.
        step_model sender skip_ev == Some sender_after' /\
        step_model sender_after' sent_ev == Some sender_after_head /\
        step_model receiver received_ev == Some receiver_after_head /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
    with _.
    ( introduce exists
        (sender_after':connection_model)
        (sender_after_head:connection_model)
        (receiver_after_head:connection_model)
        (pair:protected_message_replay)
        (sender_tail_sent':B.bytes)
        (sender_tail_received':B.bytes)
        (receiver_tail_sent':B.bytes)
        (receiver_tail_received':B.bytes).
        step_model sender skip_ev == Some sender_after' /\
        step_model sender_after' sent_ev == Some sender_after_head /\
        step_model receiver received_ev == Some receiver_after_head /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
      with
        sender_after
        sender_after_head0
        receiver_after_head0
        pair0
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_receiver_non_install_local_head
  (sender:connection_model)
  (receiver:connection_model)
  (skip:local_event)
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
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
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
            (ConnLocalEvent skip :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            } :: receiver_rest)
            receiver_raw_sent
            receiver_raw_received
            receiver_final)
      (ensures
        exists receiver_after pair.
            step_model receiver (ConnLocalEvent skip) == Some receiver_after /\
            pair.pm_sender == sender /\
            pair.pm_receiver == receiver_after /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg)
=
  let skip_ev = ConnLocalEvent skip in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_received_replay_skip_empty_head_preserves_peer_stream
    sender_raw_sent
    receiver
    skip_ev
    (received_ev :: receiver_rest)
    receiver_raw_sent
    receiver_raw_received
    receiver_final;
  eliminate exists
    (receiver_after:connection_model)
    (receiver_tail_sent:B.bytes)
    (receiver_tail_received:B.bytes).
    legal_event receiver skip_ev /\
    step_model receiver skip_ev == Some receiver_after /\
    Seq.equal sender_raw_sent receiver_tail_received /\
    conn_events_received_decode_replay
      receiver_after
      (received_ev :: receiver_rest)
      receiver_tail_sent
      receiver_tail_received
      receiver_final
  returns
    exists receiver_after' pair.
      step_model receiver skip_ev == Some receiver_after' /\
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after' /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
  with _.
  ( lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
      sender
      receiver
      skip
      receiver_after;
    lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head
      sender
      receiver
      receiver_after
      skip_ev
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists (pair:protected_message_replay).
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
    returns
      exists receiver_after' pair.
        step_model receiver skip_ev == Some receiver_after' /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg
    with _.
    ( introduce exists
        (receiver_after':connection_model)
        (pair':protected_message_replay).
        step_model receiver skip_ev == Some receiver_after' /\
        pair'.pm_sender == sender /\
        pair'.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
            pair'
            sent_msg
            received_msg
      with receiver_after pair
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_receiver_non_install_local_head_with_tails
  (sender:connection_model)
  (receiver:connection_model)
  (skip:local_event)
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
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
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
          (ConnLocalEvent skip :: ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists receiver_after sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          step_model receiver (ConnLocalEvent skip) == Some receiver_after /\
          step_model
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          step_model
            receiver_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let skip_ev = ConnLocalEvent skip in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_received_replay_skip_empty_head_preserves_peer_stream
    sender_raw_sent
    receiver
    skip_ev
    (received_ev :: receiver_rest)
    receiver_raw_sent
    receiver_raw_received
    receiver_final;
  eliminate exists
    (receiver_after:connection_model)
    (receiver_tail_sent0:B.bytes)
    (receiver_tail_received0:B.bytes).
    legal_event receiver skip_ev /\
    step_model receiver skip_ev == Some receiver_after /\
    Seq.equal sender_raw_sent receiver_tail_received0 /\
    conn_events_received_decode_replay
      receiver_after
      (received_ev :: receiver_rest)
      receiver_tail_sent0
      receiver_tail_received0
      receiver_final
  returns
    exists receiver_after' sender_after_head receiver_after_head pair
      sender_tail_sent sender_tail_received
      receiver_tail_sent receiver_tail_received.
      step_model receiver skip_ev == Some receiver_after' /\
      step_model sender sent_ev == Some sender_after_head /\
      step_model receiver_after' received_ev == Some receiver_after_head /\
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after' /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
      sender
      receiver
      skip
      receiver_after;
    lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head_with_tails
      sender
      receiver
      receiver_after
      skip_ev
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists
      (sender_after_head0:connection_model)
      (receiver_after_head0:connection_model)
      (pair0:protected_message_replay)
      (sender_tail_sent:B.bytes)
      (sender_tail_received:B.bytes)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      step_model sender sent_ev == Some sender_after_head0 /\
      step_model receiver_after received_ev == Some receiver_after_head0 /\
      pair0.pm_sender == sender /\
      pair0.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair0
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head0
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head0
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    returns
      exists receiver_after' sender_after_head receiver_after_head pair
        sender_tail_sent' sender_tail_received'
        receiver_tail_sent' receiver_tail_received'.
        step_model receiver skip_ev == Some receiver_after' /\
        step_model sender sent_ev == Some sender_after_head /\
        step_model receiver_after' received_ev == Some receiver_after_head /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
    with _.
    ( introduce exists
        (receiver_after':connection_model)
        (sender_after_head:connection_model)
        (receiver_after_head:connection_model)
        (pair:protected_message_replay)
        (sender_tail_sent':B.bytes)
        (sender_tail_received':B.bytes)
        (receiver_tail_sent':B.bytes)
        (receiver_tail_received':B.bytes).
        step_model receiver skip_ev == Some receiver_after' /\
        step_model sender sent_ev == Some sender_after_head /\
        step_model receiver_after' received_ev == Some receiver_after_head /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
      with
        receiver_after
        sender_after_head0
        receiver_after_head0
        pair0
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
      and () ) )
#pop-options
