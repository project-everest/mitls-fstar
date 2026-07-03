module TLS13.ConnectionState.ProtectedWireSegmentation

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PWL = TLS13.ConnectionState.ProtectedWireLemmas
module Seq = FStar.Seq
module WFL = TLS13.Spec.WireFormatLemmas

open TLS13.Spec.ConnectionState

#push-options "--split_queries always --z3rlimit 10"
let lemma_received_client_hello_raw_from_sent_replay_single
  (model:connection_model)
  (ch:M.client_hello)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_sent_seal_replay
          model
          [ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }]
          raw_sent
          raw_received
          final_model)
      (ensures
        Seq.equal raw_sent B.empty /\
        received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello ch))
          raw_received)
=
  let ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ClientHello ch);
  } in
  PWL.lemma_conn_events_sent_seal_replay_head
    model
    ev
    []
    raw_sent
    raw_received
    final_model;
  eliminate exists model1 delta_sent delta_received tail_sent tail_received.
    legal_event model ev /\
    step_model model ev == Some model1 /\
    event_raw_delta_legal model ev delta_sent delta_received /\
    sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    conn_events_sent_seal_replay
      model1
      []
      tail_sent
      tail_received
      final_model
  returns
    Seq.equal raw_sent B.empty /\
    received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello ch))
      raw_received
  with _.
  ( assert (Seq.equal delta_sent B.empty);
    assert (received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello ch))
      delta_received);
    assert (Seq.equal tail_sent B.empty);
    assert (Seq.equal tail_received B.empty);
    Seq.lemma_eq_elim tail_sent B.empty;
    Seq.lemma_eq_elim tail_received B.empty;
    assert (Seq.equal (B.append delta_sent tail_sent) B.empty);
    assert (Seq.equal (B.append delta_received tail_received) delta_received);
    Seq.lemma_eq_elim raw_sent (B.append delta_sent tail_sent);
    Seq.lemma_eq_elim raw_received (B.append delta_received tail_received);
    assert (Seq.equal raw_sent B.empty);
    assert (Seq.equal raw_received delta_received);
    Seq.lemma_eq_elim raw_received delta_received;
    assert (received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello ch))
      raw_received) )

let lemma_received_client_hello_raw_from_received_replay_single
  (model:connection_model)
  (ch:M.client_hello)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_received_decode_replay
          model
          [ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }]
          raw_sent
          raw_received
          final_model)
      (ensures
        Seq.equal raw_sent B.empty /\
        received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello ch))
          raw_received)
=
  let ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ClientHello ch);
  } in
  PWL.lemma_conn_events_received_decode_replay_head
    model
    ev
    []
    raw_sent
    raw_received
    final_model;
  eliminate exists model1 delta_sent delta_received tail_sent tail_received.
    legal_event model ev /\
    step_model model ev == Some model1 /\
    event_raw_delta_legal model ev delta_sent delta_received /\
    received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    conn_events_received_decode_replay
      model1
      []
      tail_sent
      tail_received
      final_model
  returns
    Seq.equal raw_sent B.empty /\
    received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello ch))
      raw_received
  with _.
  ( assert (Seq.equal delta_sent B.empty);
    assert (received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello ch))
      delta_received);
    assert (Seq.equal tail_sent B.empty);
    assert (Seq.equal tail_received B.empty);
    Seq.lemma_eq_elim tail_sent B.empty;
    Seq.lemma_eq_elim tail_received B.empty;
    assert (Seq.equal (B.append delta_sent tail_sent) B.empty);
    assert (Seq.equal (B.append delta_received tail_received) delta_received);
    Seq.lemma_eq_elim raw_sent (B.append delta_sent tail_sent);
    Seq.lemma_eq_elim raw_received (B.append delta_received tail_received);
    assert (Seq.equal raw_sent B.empty);
    assert (Seq.equal raw_received delta_received);
    Seq.lemma_eq_elim raw_received delta_received;
    assert (received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello ch))
      raw_received) )

let lemma_paired_replay_split_prefixes_equal_from_full_streams
  (server_model:connection_model)
  (client_model:connection_model)
  (server_prefix:list conn_event)
  (server_suffix:list conn_event)
  (client_prefix:list conn_event)
  (client_suffix:list conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        Seq.equal server_full_sent client_full_received /\
        Seq.equal client_full_sent server_full_received /\
        paired_replay_split_prefixes_equal_with_full_streams
          server_model
          client_model
          server_prefix
          server_suffix
          client_prefix
          client_suffix
          server_full_sent
          server_full_received
          client_full_sent
          client_full_received
          server_final
          client_final)
      (ensures
        paired_replay_split_prefixes_equal
          server_model
          client_model
          server_prefix
          server_suffix
          client_prefix
          client_suffix
          server_full_sent
          server_full_received
          client_full_sent
          client_full_received
          server_final
          client_final)
=
  introduce forall
    (server_mid:connection_model)
    (client_mid:connection_model)
    (server_prefix_sent:B.bytes)
    (server_prefix_received:B.bytes)
    (server_suffix_sent:B.bytes)
    (server_suffix_received:B.bytes)
    (client_prefix_sent:B.bytes)
    (client_prefix_received:B.bytes)
    (client_suffix_sent:B.bytes)
    (client_suffix_received:B.bytes).
    Seq.equal server_full_sent
      (B.append server_prefix_sent server_suffix_sent) /\
    Seq.equal server_full_received
      (B.append server_prefix_received server_suffix_received) /\
    Seq.equal client_full_sent
      (B.append client_prefix_sent client_suffix_sent) /\
    Seq.equal client_full_received
      (B.append client_prefix_received client_suffix_received) /\
    conn_events_sent_seal_replay
      server_model
      server_prefix
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_sent_seal_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_received_decode_replay
      server_model
      server_prefix
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_received_decode_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_sent_seal_replay
      client_model
      client_prefix
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_sent_seal_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final /\
    conn_events_received_decode_replay
      client_model
      client_prefix
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_received_decode_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final ==>
    Seq.equal server_prefix_sent client_prefix_received /\
    Seq.equal client_prefix_sent server_prefix_received
  with
    introduce _ ==> _ with _.
    ( assert (Seq.equal server_prefix_sent client_prefix_received);
      assert (Seq.equal client_prefix_sent server_prefix_received) )

let lemma_paired_replay_split_prefixes_equal_with_full_streams_from_plain
  (server_model:connection_model)
  (client_model:connection_model)
  (server_prefix:list conn_event)
  (server_suffix:list conn_event)
  (client_prefix:list conn_event)
  (client_suffix:list conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        paired_replay_split_prefixes_equal
          server_model
          client_model
          server_prefix
          server_suffix
          client_prefix
          client_suffix
          server_full_sent
          server_full_received
          client_full_sent
          client_full_received
          server_final
          client_final)
      (ensures
        paired_replay_split_prefixes_equal_with_full_streams
          server_model
          client_model
          server_prefix
          server_suffix
          client_prefix
          client_suffix
          server_full_sent
          server_full_received
          client_full_sent
          client_full_received
          server_final
          client_final)
=
  introduce forall
    (server_mid:connection_model)
    (client_mid:connection_model)
    (server_prefix_sent:B.bytes)
    (server_prefix_received:B.bytes)
    (server_suffix_sent:B.bytes)
    (server_suffix_received:B.bytes)
    (client_prefix_sent:B.bytes)
    (client_prefix_received:B.bytes)
    (client_suffix_sent:B.bytes)
    (client_suffix_received:B.bytes).
    Seq.equal server_full_sent client_full_received /\
    Seq.equal client_full_sent server_full_received /\
    Seq.equal server_full_sent
      (B.append server_prefix_sent server_suffix_sent) /\
    Seq.equal server_full_received
      (B.append server_prefix_received server_suffix_received) /\
    Seq.equal client_full_sent
      (B.append client_prefix_sent client_suffix_sent) /\
    Seq.equal client_full_received
      (B.append client_prefix_received client_suffix_received) /\
    conn_events_sent_seal_replay
      server_model
      server_prefix
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_sent_seal_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_received_decode_replay
      server_model
      server_prefix
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_received_decode_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_sent_seal_replay
      client_model
      client_prefix
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_sent_seal_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final /\
    conn_events_received_decode_replay
      client_model
      client_prefix
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_received_decode_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final ==>
    Seq.equal server_prefix_sent client_prefix_received /\
    Seq.equal client_prefix_sent server_prefix_received
  with
    introduce _ ==> _ with _.
    ( assert (Seq.equal server_prefix_sent client_prefix_received);
      assert (Seq.equal client_prefix_sent server_prefix_received) )

let lemma_same_endpoint_replay_split_prefixes_equal_empty
  (model:connection_model)
  (suffix:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (same_endpoint_replay_split_prefixes_equal
        model
        []
        suffix
        raw_sent
        raw_received
        final_model)
=
  introduce forall
    (sent_mid:connection_model)
    (received_mid:connection_model)
    (sent_prefix_sent:B.bytes)
    (sent_prefix_received:B.bytes)
    (sent_suffix_sent:B.bytes)
    (sent_suffix_received:B.bytes)
    (received_prefix_sent:B.bytes)
    (received_prefix_received:B.bytes)
    (received_suffix_sent:B.bytes)
    (received_suffix_received:B.bytes).
    Seq.equal raw_sent (B.append sent_prefix_sent sent_suffix_sent) /\
    Seq.equal raw_received
      (B.append sent_prefix_received sent_suffix_received) /\
    Seq.equal raw_sent
      (B.append received_prefix_sent received_suffix_sent) /\
    Seq.equal raw_received
      (B.append received_prefix_received received_suffix_received) /\
    conn_events_sent_seal_replay
      model
      []
      sent_prefix_sent
      sent_prefix_received
      sent_mid /\
    conn_events_sent_seal_replay
      sent_mid
      suffix
      sent_suffix_sent
      sent_suffix_received
      final_model /\
    conn_events_received_decode_replay
      model
      []
      received_prefix_sent
      received_prefix_received
      received_mid /\
    conn_events_received_decode_replay
      received_mid
      suffix
      received_suffix_sent
      received_suffix_received
      final_model ==>
    Seq.equal sent_prefix_sent received_prefix_sent /\
    Seq.equal sent_prefix_received received_prefix_received
  with
    introduce _ ==> _ with _.
    ( assert (Seq.equal sent_prefix_sent B.empty);
      assert (Seq.equal sent_prefix_received B.empty);
      assert (Seq.equal received_prefix_sent B.empty);
      assert (Seq.equal received_prefix_received B.empty) )

let lemma_same_endpoint_replay_split_prefixes_equal_single_local
  (model:connection_model)
  (ev:local_event)
  (suffix:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (same_endpoint_replay_split_prefixes_equal
        model
        [ConnLocalEvent ev]
        suffix
        raw_sent
        raw_received
        final_model)
=
  introduce forall
    (sent_mid:connection_model)
    (received_mid:connection_model)
    (sent_prefix_sent:B.bytes)
    (sent_prefix_received:B.bytes)
    (sent_suffix_sent:B.bytes)
    (sent_suffix_received:B.bytes)
    (received_prefix_sent:B.bytes)
    (received_prefix_received:B.bytes)
    (received_suffix_sent:B.bytes)
    (received_suffix_received:B.bytes).
    Seq.equal raw_sent (B.append sent_prefix_sent sent_suffix_sent) /\
    Seq.equal raw_received
      (B.append sent_prefix_received sent_suffix_received) /\
    Seq.equal raw_sent
      (B.append received_prefix_sent received_suffix_sent) /\
    Seq.equal raw_received
      (B.append received_prefix_received received_suffix_received) /\
    conn_events_sent_seal_replay
      model
      [ConnLocalEvent ev]
      sent_prefix_sent
      sent_prefix_received
      sent_mid /\
    conn_events_sent_seal_replay
      sent_mid
      suffix
      sent_suffix_sent
      sent_suffix_received
      final_model /\
    conn_events_received_decode_replay
      model
      [ConnLocalEvent ev]
      received_prefix_sent
      received_prefix_received
      received_mid /\
    conn_events_received_decode_replay
      received_mid
      suffix
      received_suffix_sent
      received_suffix_received
      final_model ==>
    Seq.equal sent_prefix_sent received_prefix_sent /\
    Seq.equal sent_prefix_received received_prefix_received
  with
    introduce _ ==> _ with _.
    ( assert (Seq.equal sent_prefix_sent B.empty);
      assert (Seq.equal sent_prefix_received B.empty);
      assert (Seq.equal received_prefix_sent B.empty);
      assert (Seq.equal received_prefix_received B.empty) )

let lemma_same_endpoint_replay_split_prefixes_equal_cons_local
  (model:connection_model)
  (ev:local_event)
  (tail:list conn_event)
  (suffix:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (post_model:connection_model)
  : Lemma
      (requires
        step_model model (ConnLocalEvent ev) == Some post_model /\
        same_endpoint_replay_split_prefixes_equal
          post_model
          tail
          suffix
          raw_sent
          raw_received
          final_model)
      (ensures
        same_endpoint_replay_split_prefixes_equal
          model
          (ConnLocalEvent ev :: tail)
          suffix
          raw_sent
          raw_received
          final_model)
=
  introduce forall
    (sent_mid:connection_model)
    (received_mid:connection_model)
    (sent_prefix_sent:B.bytes)
    (sent_prefix_received:B.bytes)
    (sent_suffix_sent:B.bytes)
    (sent_suffix_received:B.bytes)
    (received_prefix_sent:B.bytes)
    (received_prefix_received:B.bytes)
    (received_suffix_sent:B.bytes)
    (received_suffix_received:B.bytes).
    Seq.equal raw_sent (B.append sent_prefix_sent sent_suffix_sent) /\
    Seq.equal raw_received
      (B.append sent_prefix_received sent_suffix_received) /\
    Seq.equal raw_sent
      (B.append received_prefix_sent received_suffix_sent) /\
    Seq.equal raw_received
      (B.append received_prefix_received received_suffix_received) /\
    conn_events_sent_seal_replay
      model
      (ConnLocalEvent ev :: tail)
      sent_prefix_sent
      sent_prefix_received
      sent_mid /\
    conn_events_sent_seal_replay
      sent_mid
      suffix
      sent_suffix_sent
      sent_suffix_received
      final_model /\
    conn_events_received_decode_replay
      model
      (ConnLocalEvent ev :: tail)
      received_prefix_sent
      received_prefix_received
      received_mid /\
    conn_events_received_decode_replay
      received_mid
      suffix
      received_suffix_sent
      received_suffix_received
      final_model ==>
    Seq.equal sent_prefix_sent received_prefix_sent /\
    Seq.equal sent_prefix_received received_prefix_received
  with
    introduce _ ==> _ with _.
    ( PWL.lemma_conn_events_sent_seal_replay_head
        model
        (ConnLocalEvent ev)
        tail
        sent_prefix_sent
        sent_prefix_received
        sent_mid;
      eliminate exists sent_head_model sent_delta_sent sent_delta_received
        sent_tail_sent sent_tail_received.
        legal_event model (ConnLocalEvent ev) /\
        step_model model (ConnLocalEvent ev) == Some sent_head_model /\
        event_raw_delta_legal
          model
          (ConnLocalEvent ev)
          sent_delta_sent
          sent_delta_received /\
        sent_event_nonempty_seal_projection model (ConnLocalEvent ev) sent_delta_sent /\
        Seq.equal sent_prefix_sent (B.append sent_delta_sent sent_tail_sent) /\
        Seq.equal sent_prefix_received
          (B.append sent_delta_received sent_tail_received) /\
        conn_events_sent_seal_replay
          sent_head_model
          tail
          sent_tail_sent
          sent_tail_received
          sent_mid
      returns
        Seq.equal sent_prefix_sent received_prefix_sent /\
        Seq.equal sent_prefix_received received_prefix_received
      with _.
      ( PWL.lemma_conn_events_received_decode_replay_head
          model
          (ConnLocalEvent ev)
          tail
          received_prefix_sent
          received_prefix_received
          received_mid;
        eliminate exists received_head_model received_delta_sent received_delta_received
          received_tail_sent received_tail_received.
          legal_event model (ConnLocalEvent ev) /\
          step_model model (ConnLocalEvent ev) == Some received_head_model /\
          event_raw_delta_legal
            model
            (ConnLocalEvent ev)
            received_delta_sent
            received_delta_received /\
          received_event_nonempty_decode_projection
            model
            (ConnLocalEvent ev)
            received_delta_received /\
          Seq.equal received_prefix_sent
            (B.append received_delta_sent received_tail_sent) /\
          Seq.equal received_prefix_received
            (B.append received_delta_received received_tail_received) /\
          conn_events_received_decode_replay
            received_head_model
            tail
            received_tail_sent
            received_tail_received
            received_mid
        returns
          Seq.equal sent_prefix_sent received_prefix_sent /\
          Seq.equal sent_prefix_received received_prefix_received
        with _.
        ( assert (sent_head_model == post_model);
          assert (received_head_model == post_model);
          assert (Seq.equal sent_delta_sent B.empty);
          assert (Seq.equal sent_delta_received B.empty);
          assert (Seq.equal received_delta_sent B.empty);
          assert (Seq.equal received_delta_received B.empty);
          Seq.lemma_eq_elim sent_delta_sent B.empty;
          Seq.lemma_eq_elim sent_delta_received B.empty;
          Seq.lemma_eq_elim received_delta_sent B.empty;
          Seq.lemma_eq_elim received_delta_received B.empty;
          assert (Seq.equal (B.append sent_delta_sent sent_tail_sent) sent_tail_sent);
          assert (Seq.equal (B.append sent_delta_received sent_tail_received) sent_tail_received);
          assert (Seq.equal (B.append received_delta_sent received_tail_sent) received_tail_sent);
          assert (Seq.equal (B.append received_delta_received received_tail_received) received_tail_received);
          Seq.lemma_eq_elim sent_prefix_sent (B.append sent_delta_sent sent_tail_sent);
          Seq.lemma_eq_elim sent_prefix_received
            (B.append sent_delta_received sent_tail_received);
          Seq.lemma_eq_elim received_prefix_sent
            (B.append received_delta_sent received_tail_sent);
          Seq.lemma_eq_elim received_prefix_received
            (B.append received_delta_received received_tail_received);
          assert (Seq.equal sent_prefix_sent sent_tail_sent);
          assert (Seq.equal sent_prefix_received sent_tail_received);
          assert (Seq.equal received_prefix_sent received_tail_sent);
          assert (Seq.equal received_prefix_received received_tail_received);
          Seq.lemma_eq_elim sent_prefix_sent sent_tail_sent;
          Seq.lemma_eq_elim sent_prefix_received sent_tail_received;
          Seq.lemma_eq_elim received_prefix_sent received_tail_sent;
          Seq.lemma_eq_elim received_prefix_received received_tail_received;
          assert (Seq.equal raw_sent (B.append sent_tail_sent sent_suffix_sent));
          assert (Seq.equal raw_received
            (B.append sent_tail_received sent_suffix_received));
          assert (Seq.equal raw_sent
            (B.append received_tail_sent received_suffix_sent));
          assert (Seq.equal raw_received
            (B.append received_tail_received received_suffix_received));
          assert (Seq.equal sent_tail_sent received_tail_sent);
          assert (Seq.equal sent_tail_received received_tail_received);
          assert (Seq.equal sent_prefix_sent received_prefix_sent);
          assert (Seq.equal sent_prefix_received received_prefix_received) ) ) )

let lemma_same_endpoint_replay_split_prefixes_equal_single_sent_cleartext
  (model:connection_model)
  (msg:M.tls_message)
  (suffix:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        network_message_is_cleartext CL.Sent msg == true)
      (ensures
        same_endpoint_replay_split_prefixes_equal
          model
          [ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          }]
          suffix
          raw_sent
          raw_received
          final_model)
=
  introduce forall
    (sent_mid:connection_model)
    (received_mid:connection_model)
    (sent_prefix_sent:B.bytes)
    (sent_prefix_received:B.bytes)
    (sent_suffix_sent:B.bytes)
    (sent_suffix_received:B.bytes)
    (received_prefix_sent:B.bytes)
    (received_prefix_received:B.bytes)
    (received_suffix_sent:B.bytes)
    (received_suffix_received:B.bytes).
    Seq.equal raw_sent (B.append sent_prefix_sent sent_suffix_sent) /\
    Seq.equal raw_received
      (B.append sent_prefix_received sent_suffix_received) /\
    Seq.equal raw_sent
      (B.append received_prefix_sent received_suffix_sent) /\
    Seq.equal raw_received
      (B.append received_prefix_received received_suffix_received) /\
    conn_events_sent_seal_replay
      model
      [ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = msg;
      }]
      sent_prefix_sent
      sent_prefix_received
      sent_mid /\
    conn_events_sent_seal_replay
      sent_mid
      suffix
      sent_suffix_sent
      sent_suffix_received
      final_model /\
    conn_events_received_decode_replay
      model
      [ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = msg;
      }]
      received_prefix_sent
      received_prefix_received
      received_mid /\
    conn_events_received_decode_replay
      received_mid
      suffix
      received_suffix_sent
      received_suffix_received
      final_model ==>
    Seq.equal sent_prefix_sent received_prefix_sent /\
    Seq.equal sent_prefix_received received_prefix_received
  with
    introduce _ ==> _ with _.
    ( assert (
        Seq.equal
          sent_prefix_sent
          (serialized_cleartext_tls_message msg));
      assert (
        Seq.equal
          received_prefix_sent
          (serialized_cleartext_tls_message msg));
      assert (Seq.equal sent_prefix_received B.empty);
      assert (Seq.equal received_prefix_received B.empty) )

let lemma_same_endpoint_replay_split_prefixes_equal_single_received_server_hello
  (model:connection_model)
  (sh:M.server_hello)
  (suffix:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (same_endpoint_replay_split_prefixes_equal
        model
        [ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ServerHello sh);
        }]
        suffix
        raw_sent
        raw_received
        final_model)
=
  introduce forall
    (sent_mid:connection_model)
    (received_mid:connection_model)
    (sent_prefix_sent:B.bytes)
    (sent_prefix_received:B.bytes)
    (sent_suffix_sent:B.bytes)
    (sent_suffix_received:B.bytes)
    (received_prefix_sent:B.bytes)
    (received_prefix_received:B.bytes)
    (received_suffix_sent:B.bytes)
    (received_suffix_received:B.bytes).
    Seq.equal raw_sent (B.append sent_prefix_sent sent_suffix_sent) /\
    Seq.equal raw_received
      (B.append sent_prefix_received sent_suffix_received) /\
    Seq.equal raw_sent
      (B.append received_prefix_sent received_suffix_sent) /\
    Seq.equal raw_received
      (B.append received_prefix_received received_suffix_received) /\
    conn_events_sent_seal_replay
      model
      [ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }]
      sent_prefix_sent
      sent_prefix_received
      sent_mid /\
    conn_events_sent_seal_replay
      sent_mid
      suffix
      sent_suffix_sent
      sent_suffix_received
      final_model /\
    conn_events_received_decode_replay
      model
      [ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }]
      received_prefix_sent
      received_prefix_received
      received_mid /\
    conn_events_received_decode_replay
      received_mid
      suffix
      received_suffix_sent
      received_suffix_received
      final_model ==>
    Seq.equal sent_prefix_sent received_prefix_sent /\
    Seq.equal sent_prefix_received received_prefix_received
  with
    introduce _ ==> _ with _.
    ( assert (Seq.equal sent_prefix_sent B.empty);
      assert (Seq.equal received_prefix_sent B.empty);
      assert (
        Seq.equal
          sent_prefix_received
          (serialized_cleartext_tls_message
            (M.TlsHandshake (M.ServerHello sh))));
      assert (
        Seq.equal
          received_prefix_received
          (serialized_cleartext_tls_message
            (M.TlsHandshake (M.ServerHello sh)))) )

let lemma_same_endpoint_replay_split_prefixes_equal_single_received_client_hello
  (model:connection_model)
  (ch:M.client_hello)
  (suffix:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (same_endpoint_replay_split_prefixes_equal
       model
       [ConnNetworkEvent {
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ClientHello ch);
       }]
       suffix
       raw_sent
       raw_received
       final_model)
=
  introduce forall
    (sent_mid:connection_model)
    (received_mid:connection_model)
    (sent_prefix_sent:B.bytes)
    (sent_prefix_received:B.bytes)
    (sent_suffix_sent:B.bytes)
    (sent_suffix_received:B.bytes)
    (received_prefix_sent:B.bytes)
    (received_prefix_received:B.bytes)
    (received_suffix_sent:B.bytes)
    (received_suffix_received:B.bytes).
    Seq.equal raw_sent (B.append sent_prefix_sent sent_suffix_sent) /\
    Seq.equal raw_received
      (B.append sent_prefix_received sent_suffix_received) /\
    Seq.equal raw_sent
      (B.append received_prefix_sent received_suffix_sent) /\
    Seq.equal raw_received
      (B.append received_prefix_received received_suffix_received) /\
    conn_events_sent_seal_replay
      model
      [ConnNetworkEvent {
       CL.message_direction = CL.Received;
       CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }]
      sent_prefix_sent
      sent_prefix_received
      sent_mid /\
    conn_events_sent_seal_replay
      sent_mid
      suffix
      sent_suffix_sent
      sent_suffix_received
      final_model /\
    conn_events_received_decode_replay
      model
      [ConnNetworkEvent {
       CL.message_direction = CL.Received;
       CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }]
      received_prefix_sent
      received_prefix_received
      received_mid /\
    conn_events_received_decode_replay
      received_mid
      suffix
      received_suffix_sent
      received_suffix_received
      final_model ==>
    Seq.equal sent_prefix_sent received_prefix_sent /\
    Seq.equal sent_prefix_received received_prefix_received
  with
    introduce _ ==> _ with _.
    ( lemma_received_client_hello_raw_from_sent_replay_single
        model
        ch
        sent_prefix_sent
        sent_prefix_received
        sent_mid;
      lemma_received_client_hello_raw_from_received_replay_single
        model
        ch
        received_prefix_sent
        received_prefix_received
        received_mid;
      assert (Seq.equal sent_prefix_sent B.empty);
      assert (Seq.equal received_prefix_sent B.empty);
      WFL.lemma_received_client_hello_raw_length ch sent_prefix_received;
      WFL.lemma_received_client_hello_raw_length ch received_prefix_received;
      assert (B.length sent_prefix_received ==
       B.length received_prefix_received);
      Seq.lemma_eq_elim
       raw_received
       (B.append sent_prefix_received sent_suffix_received);
      Seq.lemma_eq_elim
       raw_received
       (B.append received_prefix_received received_suffix_received);
      assert (Seq.equal
       (B.append sent_prefix_received sent_suffix_received)
       (B.append received_prefix_received received_suffix_received));
      PWL.lemma_append_heads_equal_same_len
       sent_prefix_received
       sent_suffix_received
       received_prefix_received
       received_suffix_received )

let lemma_paired_replay_split_prefixes_equal_empty
  (server_model:connection_model)
  (client_model:connection_model)
  (server_suffix:list conn_event)
  (client_suffix:list conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (paired_replay_split_prefixes_equal
        server_model
        client_model
        []
        server_suffix
        []
        client_suffix
        server_full_sent
        server_full_received
        client_full_sent
        client_full_received
        server_final
        client_final)
=
  introduce forall
    (server_mid:connection_model)
    (client_mid:connection_model)
    (server_prefix_sent:B.bytes)
    (server_prefix_received:B.bytes)
    (server_suffix_sent:B.bytes)
    (server_suffix_received:B.bytes)
    (client_prefix_sent:B.bytes)
    (client_prefix_received:B.bytes)
    (client_suffix_sent:B.bytes)
    (client_suffix_received:B.bytes).
    Seq.equal server_full_sent
      (B.append server_prefix_sent server_suffix_sent) /\
    Seq.equal server_full_received
      (B.append server_prefix_received server_suffix_received) /\
    Seq.equal client_full_sent
      (B.append client_prefix_sent client_suffix_sent) /\
    Seq.equal client_full_received
      (B.append client_prefix_received client_suffix_received) /\
    conn_events_sent_seal_replay
      server_model
      []
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_sent_seal_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_received_decode_replay
      server_model
      []
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_received_decode_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_sent_seal_replay
      client_model
      []
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_sent_seal_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final /\
    conn_events_received_decode_replay
      client_model
      []
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_received_decode_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final ==>
    Seq.equal server_prefix_sent client_prefix_received /\
    Seq.equal client_prefix_sent server_prefix_received
  with
    introduce _ ==> _ with _.
    ( assert (Seq.equal server_prefix_sent B.empty);
      assert (Seq.equal server_prefix_received B.empty);
      assert (Seq.equal client_prefix_sent B.empty);
      assert (Seq.equal client_prefix_received B.empty) )

let lemma_paired_replay_split_prefixes_equal_single_local
  (server_model:connection_model)
  (client_model:connection_model)
  (server_ev:local_event)
  (client_ev:local_event)
  (server_suffix:list conn_event)
  (client_suffix:list conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (paired_replay_split_prefixes_equal
        server_model
        client_model
        [ConnLocalEvent server_ev]
        server_suffix
        [ConnLocalEvent client_ev]
        client_suffix
        server_full_sent
        server_full_received
        client_full_sent
        client_full_received
        server_final
        client_final)
=
  introduce forall
    (server_mid:connection_model)
    (client_mid:connection_model)
    (server_prefix_sent:B.bytes)
    (server_prefix_received:B.bytes)
    (server_suffix_sent:B.bytes)
    (server_suffix_received:B.bytes)
    (client_prefix_sent:B.bytes)
    (client_prefix_received:B.bytes)
    (client_suffix_sent:B.bytes)
    (client_suffix_received:B.bytes).
    Seq.equal server_full_sent
      (B.append server_prefix_sent server_suffix_sent) /\
    Seq.equal server_full_received
      (B.append server_prefix_received server_suffix_received) /\
    Seq.equal client_full_sent
      (B.append client_prefix_sent client_suffix_sent) /\
    Seq.equal client_full_received
      (B.append client_prefix_received client_suffix_received) /\
    conn_events_sent_seal_replay
      server_model
      [ConnLocalEvent server_ev]
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_sent_seal_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_received_decode_replay
      server_model
      [ConnLocalEvent server_ev]
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_received_decode_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_sent_seal_replay
      client_model
      [ConnLocalEvent client_ev]
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_sent_seal_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final /\
    conn_events_received_decode_replay
      client_model
      [ConnLocalEvent client_ev]
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_received_decode_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final ==>
    Seq.equal server_prefix_sent client_prefix_received /\
    Seq.equal client_prefix_sent server_prefix_received
  with
    introduce _ ==> _ with _.
    ( assert (Seq.equal server_prefix_sent B.empty);
      assert (Seq.equal server_prefix_received B.empty);
      assert (Seq.equal client_prefix_sent B.empty);
      assert (Seq.equal client_prefix_received B.empty) )

let lemma_paired_replay_split_prefixes_equal_with_full_streams_cons_server_local
  (server_model:connection_model)
  (client_model:connection_model)
  (server_ev:local_event)
  (server_tail:list conn_event)
  (server_suffix:list conn_event)
  (client_prefix:list conn_event)
  (client_suffix:list conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  (server_post:connection_model)
  : Lemma
      (requires
        step_model server_model (ConnLocalEvent server_ev) == Some server_post /\
        paired_replay_split_prefixes_equal_with_full_streams
          server_post
          client_model
          server_tail
          server_suffix
          client_prefix
          client_suffix
          server_full_sent
          server_full_received
          client_full_sent
          client_full_received
          server_final
          client_final)
      (ensures
        paired_replay_split_prefixes_equal_with_full_streams
          server_model
          client_model
          (ConnLocalEvent server_ev :: server_tail)
          server_suffix
          client_prefix
          client_suffix
          server_full_sent
          server_full_received
          client_full_sent
          client_full_received
          server_final
          client_final)
=
  introduce forall
    (server_mid:connection_model)
    (client_mid:connection_model)
    (server_prefix_sent:B.bytes)
    (server_prefix_received:B.bytes)
    (server_suffix_sent:B.bytes)
    (server_suffix_received:B.bytes)
    (client_prefix_sent:B.bytes)
    (client_prefix_received:B.bytes)
    (client_suffix_sent:B.bytes)
    (client_suffix_received:B.bytes).
    Seq.equal server_full_sent client_full_received /\
    Seq.equal client_full_sent server_full_received /\
    Seq.equal server_full_sent
      (B.append server_prefix_sent server_suffix_sent) /\
    Seq.equal server_full_received
      (B.append server_prefix_received server_suffix_received) /\
    Seq.equal client_full_sent
      (B.append client_prefix_sent client_suffix_sent) /\
    Seq.equal client_full_received
      (B.append client_prefix_received client_suffix_received) /\
    conn_events_sent_seal_replay
      server_model
      (ConnLocalEvent server_ev :: server_tail)
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_sent_seal_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_received_decode_replay
      server_model
      (ConnLocalEvent server_ev :: server_tail)
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_received_decode_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_sent_seal_replay
      client_model
      client_prefix
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_sent_seal_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final /\
    conn_events_received_decode_replay
      client_model
      client_prefix
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_received_decode_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final ==>
    Seq.equal server_prefix_sent client_prefix_received /\
    Seq.equal client_prefix_sent server_prefix_received
  with
    introduce _ ==> _ with _.
    ( PWL.lemma_conn_events_sent_seal_replay_head
        server_model
        (ConnLocalEvent server_ev)
        server_tail
        server_prefix_sent
        server_prefix_received
        server_mid;
      eliminate exists sent_head_model sent_delta_sent sent_delta_received
        sent_tail_sent sent_tail_received.
        legal_event server_model (ConnLocalEvent server_ev) /\
        step_model server_model (ConnLocalEvent server_ev) == Some sent_head_model /\
        event_raw_delta_legal
          server_model
          (ConnLocalEvent server_ev)
          sent_delta_sent
          sent_delta_received /\
        sent_event_nonempty_seal_projection
          server_model
          (ConnLocalEvent server_ev)
          sent_delta_sent /\
        Seq.equal server_prefix_sent (B.append sent_delta_sent sent_tail_sent) /\
        Seq.equal server_prefix_received
          (B.append sent_delta_received sent_tail_received) /\
        conn_events_sent_seal_replay
          sent_head_model
          server_tail
          sent_tail_sent
          sent_tail_received
          server_mid
      returns
        Seq.equal server_prefix_sent client_prefix_received /\
        Seq.equal client_prefix_sent server_prefix_received
      with _.
      ( PWL.lemma_conn_events_received_decode_replay_head
          server_model
          (ConnLocalEvent server_ev)
          server_tail
          server_prefix_sent
          server_prefix_received
          server_mid;
        eliminate exists received_head_model received_delta_sent received_delta_received
          received_tail_sent received_tail_received.
          legal_event server_model (ConnLocalEvent server_ev) /\
          step_model server_model (ConnLocalEvent server_ev) ==
            Some received_head_model /\
          event_raw_delta_legal
            server_model
            (ConnLocalEvent server_ev)
            received_delta_sent
            received_delta_received /\
          received_event_nonempty_decode_projection
            server_model
            (ConnLocalEvent server_ev)
            received_delta_received /\
          Seq.equal server_prefix_sent
            (B.append received_delta_sent received_tail_sent) /\
          Seq.equal server_prefix_received
            (B.append received_delta_received received_tail_received) /\
          conn_events_received_decode_replay
            received_head_model
            server_tail
            received_tail_sent
            received_tail_received
            server_mid
        returns
          Seq.equal server_prefix_sent client_prefix_received /\
          Seq.equal client_prefix_sent server_prefix_received
        with _.
        ( assert (sent_head_model == server_post);
          assert (received_head_model == server_post);
          assert (Seq.equal sent_delta_sent B.empty);
          assert (Seq.equal sent_delta_received B.empty);
          assert (Seq.equal received_delta_sent B.empty);
          assert (Seq.equal received_delta_received B.empty);
          Seq.lemma_eq_elim sent_delta_sent B.empty;
          Seq.lemma_eq_elim sent_delta_received B.empty;
          Seq.lemma_eq_elim received_delta_sent B.empty;
          Seq.lemma_eq_elim received_delta_received B.empty;
          assert (Seq.equal (B.append sent_delta_sent sent_tail_sent) sent_tail_sent);
          assert (Seq.equal (B.append sent_delta_received sent_tail_received) sent_tail_received);
          assert (Seq.equal (B.append received_delta_sent received_tail_sent) received_tail_sent);
          assert (Seq.equal (B.append received_delta_received received_tail_received) received_tail_received);
          Seq.lemma_eq_elim server_prefix_sent
            (B.append sent_delta_sent sent_tail_sent);
          Seq.lemma_eq_elim server_prefix_received
            (B.append sent_delta_received sent_tail_received);
          assert (Seq.equal server_prefix_sent sent_tail_sent);
          assert (Seq.equal server_prefix_received sent_tail_received);
          Seq.lemma_eq_elim server_prefix_sent sent_tail_sent;
          Seq.lemma_eq_elim server_prefix_received sent_tail_received;
          assert (Seq.equal received_tail_sent sent_tail_sent);
          assert (Seq.equal received_tail_received sent_tail_received);
          Seq.lemma_eq_elim received_tail_sent sent_tail_sent;
          Seq.lemma_eq_elim received_tail_received sent_tail_received;
          assert (Seq.equal server_full_sent
            (B.append sent_tail_sent server_suffix_sent));
          assert (Seq.equal server_full_received
            (B.append sent_tail_received server_suffix_received));
          assert (Seq.equal sent_tail_sent client_prefix_received);
          assert (Seq.equal client_prefix_sent sent_tail_received);
          assert (Seq.equal server_prefix_sent client_prefix_received);
          assert (Seq.equal client_prefix_sent server_prefix_received) ) ) )

let lemma_paired_replay_split_prefixes_equal_with_full_streams_cons_client_local
  (server_model:connection_model)
  (client_model:connection_model)
  (client_ev:local_event)
  (server_prefix:list conn_event)
  (server_suffix:list conn_event)
  (client_tail:list conn_event)
  (client_suffix:list conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  (client_post:connection_model)
  : Lemma
      (requires
        step_model client_model (ConnLocalEvent client_ev) == Some client_post /\
        paired_replay_split_prefixes_equal_with_full_streams
          server_model
          client_post
          server_prefix
          server_suffix
          client_tail
          client_suffix
          server_full_sent
          server_full_received
          client_full_sent
          client_full_received
          server_final
          client_final)
      (ensures
        paired_replay_split_prefixes_equal_with_full_streams
          server_model
          client_model
          server_prefix
          server_suffix
          (ConnLocalEvent client_ev :: client_tail)
          client_suffix
          server_full_sent
          server_full_received
          client_full_sent
          client_full_received
          server_final
          client_final)
=
  introduce forall
    (server_mid:connection_model)
    (client_mid:connection_model)
    (server_prefix_sent:B.bytes)
    (server_prefix_received:B.bytes)
    (server_suffix_sent:B.bytes)
    (server_suffix_received:B.bytes)
    (client_prefix_sent:B.bytes)
    (client_prefix_received:B.bytes)
    (client_suffix_sent:B.bytes)
    (client_suffix_received:B.bytes).
    Seq.equal server_full_sent client_full_received /\
    Seq.equal client_full_sent server_full_received /\
    Seq.equal server_full_sent
      (B.append server_prefix_sent server_suffix_sent) /\
    Seq.equal server_full_received
      (B.append server_prefix_received server_suffix_received) /\
    Seq.equal client_full_sent
      (B.append client_prefix_sent client_suffix_sent) /\
    Seq.equal client_full_received
      (B.append client_prefix_received client_suffix_received) /\
    conn_events_sent_seal_replay
      server_model
      server_prefix
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_sent_seal_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_received_decode_replay
      server_model
      server_prefix
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_received_decode_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_sent_seal_replay
      client_model
      (ConnLocalEvent client_ev :: client_tail)
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_sent_seal_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final /\
    conn_events_received_decode_replay
      client_model
      (ConnLocalEvent client_ev :: client_tail)
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_received_decode_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final ==>
    Seq.equal server_prefix_sent client_prefix_received /\
    Seq.equal client_prefix_sent server_prefix_received
  with
    introduce _ ==> _ with _.
    ( PWL.lemma_conn_events_sent_seal_replay_head
        client_model
        (ConnLocalEvent client_ev)
        client_tail
        client_prefix_sent
        client_prefix_received
        client_mid;
      eliminate exists sent_head_model sent_delta_sent sent_delta_received
        sent_tail_sent sent_tail_received.
        legal_event client_model (ConnLocalEvent client_ev) /\
        step_model client_model (ConnLocalEvent client_ev) == Some sent_head_model /\
        event_raw_delta_legal
          client_model
          (ConnLocalEvent client_ev)
          sent_delta_sent
          sent_delta_received /\
        sent_event_nonempty_seal_projection
          client_model
          (ConnLocalEvent client_ev)
          sent_delta_sent /\
        Seq.equal client_prefix_sent (B.append sent_delta_sent sent_tail_sent) /\
        Seq.equal client_prefix_received
          (B.append sent_delta_received sent_tail_received) /\
        conn_events_sent_seal_replay
          sent_head_model
          client_tail
          sent_tail_sent
          sent_tail_received
          client_mid
      returns
        Seq.equal server_prefix_sent client_prefix_received /\
        Seq.equal client_prefix_sent server_prefix_received
      with _.
      ( PWL.lemma_conn_events_received_decode_replay_head
          client_model
          (ConnLocalEvent client_ev)
          client_tail
          client_prefix_sent
          client_prefix_received
          client_mid;
        eliminate exists received_head_model received_delta_sent received_delta_received
          received_tail_sent received_tail_received.
          legal_event client_model (ConnLocalEvent client_ev) /\
          step_model client_model (ConnLocalEvent client_ev) ==
            Some received_head_model /\
          event_raw_delta_legal
            client_model
            (ConnLocalEvent client_ev)
            received_delta_sent
            received_delta_received /\
          received_event_nonempty_decode_projection
            client_model
            (ConnLocalEvent client_ev)
            received_delta_received /\
          Seq.equal client_prefix_sent
            (B.append received_delta_sent received_tail_sent) /\
          Seq.equal client_prefix_received
            (B.append received_delta_received received_tail_received) /\
          conn_events_received_decode_replay
            received_head_model
            client_tail
            received_tail_sent
            received_tail_received
            client_mid
        returns
          Seq.equal server_prefix_sent client_prefix_received /\
          Seq.equal client_prefix_sent server_prefix_received
        with _.
        ( assert (sent_head_model == client_post);
          assert (received_head_model == client_post);
          assert (Seq.equal sent_delta_sent B.empty);
          assert (Seq.equal sent_delta_received B.empty);
          assert (Seq.equal received_delta_sent B.empty);
          assert (Seq.equal received_delta_received B.empty);
          Seq.lemma_eq_elim sent_delta_sent B.empty;
          Seq.lemma_eq_elim sent_delta_received B.empty;
          Seq.lemma_eq_elim received_delta_sent B.empty;
          Seq.lemma_eq_elim received_delta_received B.empty;
          assert (Seq.equal (B.append sent_delta_sent sent_tail_sent) sent_tail_sent);
          assert (Seq.equal (B.append sent_delta_received sent_tail_received) sent_tail_received);
          assert (Seq.equal (B.append received_delta_sent received_tail_sent) received_tail_sent);
          assert (Seq.equal (B.append received_delta_received received_tail_received) received_tail_received);
          Seq.lemma_eq_elim client_prefix_sent
            (B.append sent_delta_sent sent_tail_sent);
          Seq.lemma_eq_elim client_prefix_received
            (B.append sent_delta_received sent_tail_received);
          assert (Seq.equal client_prefix_sent sent_tail_sent);
          assert (Seq.equal client_prefix_received sent_tail_received);
          Seq.lemma_eq_elim client_prefix_sent sent_tail_sent;
          Seq.lemma_eq_elim client_prefix_received sent_tail_received;
          assert (Seq.equal received_tail_sent sent_tail_sent);
          assert (Seq.equal received_tail_received sent_tail_received);
          Seq.lemma_eq_elim received_tail_sent sent_tail_sent;
          Seq.lemma_eq_elim received_tail_received sent_tail_received;
          assert (Seq.equal client_full_sent
            (B.append sent_tail_sent client_suffix_sent));
          assert (Seq.equal client_full_received
            (B.append sent_tail_received client_suffix_received));
          assert (Seq.equal server_prefix_sent sent_tail_received);
          assert (Seq.equal sent_tail_sent server_prefix_received);
          assert (Seq.equal server_prefix_sent client_prefix_received);
          assert (Seq.equal client_prefix_sent server_prefix_received) ) ) )

let lemma_paired_replay_split_prefixes_equal_single_server_hello
  (server_model:connection_model)
  (client_model:connection_model)
  (sh:M.server_hello)
  (server_suffix:list conn_event)
  (client_suffix:list conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (paired_replay_split_prefixes_equal
        server_model
        client_model
        [ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ServerHello sh);
        }]
        server_suffix
        [ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ServerHello sh);
        }]
        client_suffix
        server_full_sent
        server_full_received
        client_full_sent
        client_full_received
        server_final
        client_final)
=
  introduce forall
    (server_mid:connection_model)
    (client_mid:connection_model)
    (server_prefix_sent:B.bytes)
    (server_prefix_received:B.bytes)
    (server_suffix_sent:B.bytes)
    (server_suffix_received:B.bytes)
    (client_prefix_sent:B.bytes)
    (client_prefix_received:B.bytes)
    (client_suffix_sent:B.bytes)
    (client_suffix_received:B.bytes).
    Seq.equal server_full_sent
      (B.append server_prefix_sent server_suffix_sent) /\
    Seq.equal server_full_received
      (B.append server_prefix_received server_suffix_received) /\
    Seq.equal client_full_sent
      (B.append client_prefix_sent client_suffix_sent) /\
    Seq.equal client_full_received
      (B.append client_prefix_received client_suffix_received) /\
    conn_events_sent_seal_replay
      server_model
      [ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }]
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_sent_seal_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_received_decode_replay
      server_model
      [ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }]
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_received_decode_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_sent_seal_replay
      client_model
      [ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }]
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_sent_seal_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final /\
    conn_events_received_decode_replay
      client_model
      [ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }]
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_received_decode_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final ==>
    Seq.equal server_prefix_sent client_prefix_received /\
    Seq.equal client_prefix_sent server_prefix_received
  with
    introduce _ ==> _ with _.
    ( assert (
        Seq.equal
          server_prefix_sent
          (serialized_cleartext_tls_message
            (M.TlsHandshake (M.ServerHello sh))));
      assert (
        Seq.equal
          client_prefix_received
          (serialized_cleartext_tls_message
            (M.TlsHandshake (M.ServerHello sh))));
      assert (Seq.equal client_prefix_sent B.empty);
      assert (Seq.equal server_prefix_received B.empty) )

let lemma_paired_replay_split_prefixes_equal_single_client_hello_with_full_streams
  (server_model:connection_model)
  (client_model:connection_model)
  (ch:M.client_hello)
  (server_suffix:list conn_event)
  (client_suffix:list conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (paired_replay_split_prefixes_equal_with_full_streams
        server_model
        client_model
        [ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }]
        server_suffix
        [ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }]
        client_suffix
        server_full_sent
        server_full_received
        client_full_sent
        client_full_received
        server_final
        client_final)
=
  introduce forall
    (server_mid:connection_model)
    (client_mid:connection_model)
    (server_prefix_sent:B.bytes)
    (server_prefix_received:B.bytes)
    (server_suffix_sent:B.bytes)
    (server_suffix_received:B.bytes)
    (client_prefix_sent:B.bytes)
    (client_prefix_received:B.bytes)
    (client_suffix_sent:B.bytes)
    (client_suffix_received:B.bytes).
    Seq.equal server_full_sent client_full_received /\
    Seq.equal client_full_sent server_full_received /\
    Seq.equal server_full_sent
      (B.append server_prefix_sent server_suffix_sent) /\
    Seq.equal server_full_received
      (B.append server_prefix_received server_suffix_received) /\
    Seq.equal client_full_sent
      (B.append client_prefix_sent client_suffix_sent) /\
    Seq.equal client_full_received
      (B.append client_prefix_received client_suffix_received) /\
    conn_events_sent_seal_replay
      server_model
      [ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }]
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_sent_seal_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_received_decode_replay
      server_model
      [ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }]
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_received_decode_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_sent_seal_replay
      client_model
      [ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }]
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_sent_seal_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final /\
    conn_events_received_decode_replay
      client_model
      [ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }]
      client_prefix_sent
      client_prefix_received
      client_mid /\
    conn_events_received_decode_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final ==>
    Seq.equal server_prefix_sent client_prefix_received /\
    Seq.equal client_prefix_sent server_prefix_received
  with
    introduce _ ==> _ with _.
    ( lemma_received_client_hello_raw_from_sent_replay_single
        server_model
        ch
        server_prefix_sent
        server_prefix_received
        server_mid;
      assert (Seq.equal server_prefix_sent B.empty);
      assert (Seq.equal client_prefix_received B.empty);
      assert (
        Seq.equal
          client_prefix_sent
          (serialized_cleartext_tls_message
            (M.TlsHandshake (M.ClientHello ch))));
      WFL.lemma_received_client_hello_raw_length ch server_prefix_received;
      assert (B.length client_prefix_sent ==
        B.length server_prefix_received);
      Seq.lemma_eq_elim client_full_sent server_full_received;
      Seq.lemma_eq_elim
        client_full_sent
        (B.append client_prefix_sent client_suffix_sent);
      Seq.lemma_eq_elim
        server_full_received
        (B.append server_prefix_received server_suffix_received);
      assert (Seq.equal
        (B.append client_prefix_sent client_suffix_sent)
        (B.append server_prefix_received server_suffix_received));
      PWL.lemma_append_heads_equal_same_len
        client_prefix_sent
        client_suffix_sent
        server_prefix_received
        server_suffix_received )

let lemma_paired_replay_split_prefixes_equal_single_client_hello
  (server_model:connection_model)
  (client_model:connection_model)
  (ch:M.client_hello)
  (server_suffix:list conn_event)
  (client_suffix:list conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        Seq.equal server_full_sent client_full_received /\
        Seq.equal client_full_sent server_full_received)
      (ensures
        paired_replay_split_prefixes_equal
          server_model
          client_model
          [ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }]
          server_suffix
          [ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }]
          client_suffix
          server_full_sent
          server_full_received
          client_full_sent
          client_full_received
          server_final
          client_final)
=
  lemma_paired_replay_split_prefixes_equal_single_client_hello_with_full_streams
    server_model
    client_model
    ch
    server_suffix
    client_suffix
    server_full_sent
    server_full_received
    client_full_sent
    client_full_received
    server_final
    client_final;
  lemma_paired_replay_split_prefixes_equal_from_full_streams
    server_model
    client_model
    [ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    }]
    server_suffix
    [ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    }]
    client_suffix
    server_full_sent
    server_full_received
    client_full_sent
    client_full_received
    server_final
    client_final

let lemma_paired_replay_suffix_views_from_full_replays_with_equal_prefixes
  (server_model:connection_model)
  (client_model:connection_model)
  (server_prefix:list conn_event)
  (server_suffix:list conn_event)
  (client_prefix:list conn_event)
  (client_suffix:list conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        Seq.equal server_full_sent client_full_received /\
        Seq.equal client_full_sent server_full_received /\
        same_endpoint_replay_split_prefixes_equal
          server_model
          server_prefix
          server_suffix
          server_full_sent
          server_full_received
          server_final /\
        same_endpoint_replay_split_prefixes_equal
          client_model
          client_prefix
          client_suffix
          client_full_sent
          client_full_received
          client_final /\
        paired_replay_split_prefixes_equal
          server_model
          client_model
          server_prefix
          server_suffix
          client_prefix
          client_suffix
          server_full_sent
          server_full_received
          client_full_sent
          client_full_received
          server_final
          client_final /\
        conn_events_sent_seal_replay
          server_model
          (FStar.List.Tot.append server_prefix server_suffix)
          server_full_sent
          server_full_received
          server_final /\
        conn_events_received_decode_replay
          server_model
          (FStar.List.Tot.append server_prefix server_suffix)
          server_full_sent
          server_full_received
          server_final /\
        conn_events_sent_seal_replay
          client_model
          (FStar.List.Tot.append client_prefix client_suffix)
          client_full_sent
          client_full_received
          client_final /\
        conn_events_received_decode_replay
          client_model
          (FStar.List.Tot.append client_prefix client_suffix)
          client_full_sent
          client_full_received
          client_final)
      (ensures
        exists server_mid client_mid
          server_suffix_sent server_suffix_received
          client_suffix_sent client_suffix_received.
          Seq.equal server_suffix_sent client_suffix_received /\
          Seq.equal client_suffix_sent server_suffix_received /\
          conn_events_sent_seal_replay
            server_mid
            server_suffix
            server_suffix_sent
            server_suffix_received
            server_final /\
          conn_events_received_decode_replay
            server_mid
            server_suffix
            server_suffix_sent
            server_suffix_received
            server_final /\
          conn_events_sent_seal_replay
            client_mid
            client_suffix
            client_suffix_sent
            client_suffix_received
            client_final /\
          conn_events_received_decode_replay
            client_mid
            client_suffix
            client_suffix_sent
            client_suffix_received
            client_final)
=
  PWL.lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
    server_model
    server_prefix
    server_suffix
    server_full_sent
    server_full_received
    server_final
    (fun
      sent_mid
      received_mid
      sent_prefix_sent
      sent_prefix_received
      sent_suffix_sent
      sent_suffix_received
      received_prefix_sent
      received_prefix_received
      received_suffix_sent
      received_suffix_received ->
      assert (Seq.equal sent_prefix_sent received_prefix_sent);
      assert (Seq.equal sent_prefix_received received_prefix_received));
  eliminate exists
    (server_mid:connection_model)
    (server_prefix_sent:B.bytes)
    (server_prefix_received:B.bytes)
    (server_suffix_sent:B.bytes)
    (server_suffix_received:B.bytes).
    Seq.equal server_full_sent
      (B.append server_prefix_sent server_suffix_sent) /\
    Seq.equal server_full_received
      (B.append server_prefix_received server_suffix_received) /\
    conn_events_sent_seal_replay
      server_model
      server_prefix
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_sent_seal_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_received_decode_replay
      server_model
      server_prefix
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_received_decode_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final
  returns
    exists server_mid' client_mid'
      server_suffix_sent' server_suffix_received'
      client_suffix_sent' client_suffix_received'.
      Seq.equal server_suffix_sent' client_suffix_received' /\
      Seq.equal client_suffix_sent' server_suffix_received' /\
      conn_events_sent_seal_replay
        server_mid'
        server_suffix
        server_suffix_sent'
        server_suffix_received'
        server_final /\
      conn_events_received_decode_replay
        server_mid'
        server_suffix
        server_suffix_sent'
        server_suffix_received'
        server_final /\
      conn_events_sent_seal_replay
        client_mid'
        client_suffix
        client_suffix_sent'
        client_suffix_received'
        client_final /\
      conn_events_received_decode_replay
        client_mid'
        client_suffix
        client_suffix_sent'
        client_suffix_received'
        client_final
  with _.
  ( PWL.lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
      client_model
      client_prefix
      client_suffix
      client_full_sent
      client_full_received
      client_final
      (fun
        sent_mid
        received_mid
        sent_prefix_sent
        sent_prefix_received
        sent_suffix_sent
        sent_suffix_received
        received_prefix_sent
        received_prefix_received
        received_suffix_sent
        received_suffix_received ->
        assert (Seq.equal sent_prefix_sent received_prefix_sent);
        assert (Seq.equal sent_prefix_received received_prefix_received));
    eliminate exists
      (client_mid:connection_model)
      (client_prefix_sent:B.bytes)
      (client_prefix_received:B.bytes)
      (client_suffix_sent:B.bytes)
      (client_suffix_received:B.bytes).
      Seq.equal client_full_sent
        (B.append client_prefix_sent client_suffix_sent) /\
      Seq.equal client_full_received
        (B.append client_prefix_received client_suffix_received) /\
      conn_events_sent_seal_replay
        client_model
        client_prefix
        client_prefix_sent
        client_prefix_received
        client_mid /\
      conn_events_sent_seal_replay
        client_mid
        client_suffix
        client_suffix_sent
        client_suffix_received
        client_final /\
      conn_events_received_decode_replay
        client_model
        client_prefix
        client_prefix_sent
        client_prefix_received
        client_mid /\
      conn_events_received_decode_replay
        client_mid
        client_suffix
        client_suffix_sent
        client_suffix_received
        client_final
    returns
      exists server_mid' client_mid'
        server_suffix_sent' server_suffix_received'
        client_suffix_sent' client_suffix_received'.
        Seq.equal server_suffix_sent' client_suffix_received' /\
        Seq.equal client_suffix_sent' server_suffix_received' /\
        conn_events_sent_seal_replay
          server_mid'
          server_suffix
          server_suffix_sent'
          server_suffix_received'
          server_final /\
        conn_events_received_decode_replay
          server_mid'
          server_suffix
          server_suffix_sent'
          server_suffix_received'
          server_final /\
        conn_events_sent_seal_replay
          client_mid'
          client_suffix
          client_suffix_sent'
          client_suffix_received'
          client_final /\
        conn_events_received_decode_replay
          client_mid'
          client_suffix
          client_suffix_sent'
          client_suffix_received'
          client_final
    with _.
    ( assert (
        Seq.equal server_prefix_sent client_prefix_received /\
        Seq.equal client_prefix_sent server_prefix_received);
      PWL.lemma_paired_replay_suffixes_equal_from_equal_prefixes
        server_full_sent
        server_full_received
        client_full_sent
        client_full_received
        server_prefix_sent
        server_prefix_received
        server_suffix_sent
        server_suffix_received
        client_prefix_sent
        client_prefix_received
        client_suffix_sent
        client_suffix_received;
      introduce exists
        (server_mid':connection_model)
        (client_mid':connection_model)
        (server_suffix_sent':B.bytes)
        (server_suffix_received':B.bytes)
        (client_suffix_sent':B.bytes)
        (client_suffix_received':B.bytes).
        Seq.equal server_suffix_sent' client_suffix_received' /\
        Seq.equal client_suffix_sent' server_suffix_received' /\
        conn_events_sent_seal_replay
          server_mid'
          server_suffix
          server_suffix_sent'
          server_suffix_received'
          server_final /\
        conn_events_received_decode_replay
          server_mid'
          server_suffix
          server_suffix_sent'
          server_suffix_received'
          server_final /\
        conn_events_sent_seal_replay
          client_mid'
          client_suffix
          client_suffix_sent'
          client_suffix_received'
          client_final /\
        conn_events_received_decode_replay
          client_mid'
          client_suffix
          client_suffix_sent'
          client_suffix_received'
          client_final
      with
        server_mid
        client_mid
        server_suffix_sent
        server_suffix_received
        client_suffix_sent
        client_suffix_received
      and () ) )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_paired_protected_handshake_contiguous_replay_views_from_full_replays_with_equal_prefixes
  (server_model:connection_model)
  (client_model:connection_model)
  (server_prefix:list conn_event)
  (client_prefix:list conn_event)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (server_auth_skip:local_event)
  (client_auth_skip:local_event)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (client_verify_skip:local_event)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (verified_server_finished:M.finished)
  (client_app_write_material:traffic_key_material)
  (client_app_read_material:traffic_key_material)
  (server_app_write_material:traffic_key_material)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  (client_finished_rest:list conn_event)
  (server_finished_rest:list conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires (
        let server_suffix =
          PWL.server_protected_handshake_contiguous_replay_events
            server_material
            sent_msg0
            sent_msg1
            server_auth_skip
            sent_msg2
            sent_msg3
            server_app_write_material
            received_msg4
            server_finished_rest in
        let client_suffix =
          PWL.client_protected_handshake_contiguous_replay_events
            client_material
            received_msg0
            received_msg1
            client_auth_skip
            received_msg2
            client_verify_skip
            received_msg3
            verified_server_finished
            client_app_write_material
            client_app_read_material
            sent_msg4
            client_finished_rest in
        Seq.equal server_full_sent client_full_received /\
        Seq.equal client_full_sent server_full_received /\
        same_endpoint_replay_split_prefixes_equal
          server_model
          server_prefix
          server_suffix
          server_full_sent
          server_full_received
          server_final /\
        same_endpoint_replay_split_prefixes_equal
          client_model
          client_prefix
          client_suffix
          client_full_sent
          client_full_received
          client_final /\
        paired_replay_split_prefixes_equal
          server_model
          client_model
          server_prefix
          server_suffix
          client_prefix
          client_suffix
          server_full_sent
          server_full_received
          client_full_sent
          client_full_received
          server_final
          client_final /\
        conn_events_sent_seal_replay
          server_model
          (FStar.List.Tot.append server_prefix server_suffix)
          server_full_sent
          server_full_received
          server_final /\
        conn_events_received_decode_replay
          server_model
          (FStar.List.Tot.append server_prefix server_suffix)
          server_full_sent
          server_full_received
          server_final /\
        conn_events_sent_seal_replay
          client_model
          (FStar.List.Tot.append client_prefix client_suffix)
          client_full_sent
          client_full_received
          client_final /\
        conn_events_received_decode_replay
          client_model
          (FStar.List.Tot.append client_prefix client_suffix)
          client_full_sent
          client_full_received
          client_final))
      (ensures
        exists server_mid client_mid
          server_raw_sent server_raw_received
          client_raw_sent client_raw_received.
          Seq.equal server_raw_sent client_raw_received /\
          Seq.equal client_raw_sent server_raw_received /\
          PWL.paired_protected_handshake_contiguous_replay_views
            server_mid
            client_mid
            server_material
            client_material
            sent_msg0
            received_msg0
            sent_msg1
            received_msg1
            server_auth_skip
            client_auth_skip
            sent_msg2
            received_msg2
            client_verify_skip
            sent_msg3
            received_msg3
            verified_server_finished
            client_app_write_material
            client_app_read_material
            server_app_write_material
            sent_msg4
            received_msg4
            client_finished_rest
            server_finished_rest
            server_raw_sent
            server_raw_received
            client_raw_sent
            client_raw_received
            server_final
            client_final)
=
  let server_suffix =
    PWL.server_protected_handshake_contiguous_replay_events
      server_material
      sent_msg0
      sent_msg1
      server_auth_skip
      sent_msg2
      sent_msg3
      server_app_write_material
      received_msg4
      server_finished_rest in
  let client_suffix =
    PWL.client_protected_handshake_contiguous_replay_events
      client_material
      received_msg0
      received_msg1
      client_auth_skip
      received_msg2
      client_verify_skip
      received_msg3
      verified_server_finished
      client_app_write_material
      client_app_read_material
      sent_msg4
      client_finished_rest in
  lemma_paired_replay_suffix_views_from_full_replays_with_equal_prefixes
    server_model
    client_model
    server_prefix
    server_suffix
    client_prefix
    client_suffix
    server_full_sent
    server_full_received
    client_full_sent
    client_full_received
    server_final
    client_final;
  eliminate exists
    (server_mid:connection_model)
    (client_mid:connection_model)
    (server_raw_sent:B.bytes)
    (server_raw_received:B.bytes)
    (client_raw_sent:B.bytes)
    (client_raw_received:B.bytes).
    Seq.equal server_raw_sent client_raw_received /\
    Seq.equal client_raw_sent server_raw_received /\
    conn_events_sent_seal_replay
      server_mid
      server_suffix
      server_raw_sent
      server_raw_received
      server_final /\
    conn_events_received_decode_replay
      server_mid
      server_suffix
      server_raw_sent
      server_raw_received
      server_final /\
    conn_events_sent_seal_replay
      client_mid
      client_suffix
      client_raw_sent
      client_raw_received
      client_final /\
    conn_events_received_decode_replay
      client_mid
      client_suffix
      client_raw_sent
      client_raw_received
      client_final
  returns
    exists server_mid' client_mid'
      server_raw_sent' server_raw_received'
      client_raw_sent' client_raw_received'.
      Seq.equal server_raw_sent' client_raw_received' /\
      Seq.equal client_raw_sent' server_raw_received' /\
      PWL.paired_protected_handshake_contiguous_replay_views
        server_mid'
        client_mid'
        server_material
        client_material
        sent_msg0
        received_msg0
        sent_msg1
        received_msg1
        server_auth_skip
        client_auth_skip
        sent_msg2
        received_msg2
        client_verify_skip
        sent_msg3
        received_msg3
        verified_server_finished
        client_app_write_material
        client_app_read_material
        server_app_write_material
        sent_msg4
        received_msg4
        client_finished_rest
        server_finished_rest
        server_raw_sent'
        server_raw_received'
        client_raw_sent'
        client_raw_received'
        server_final
        client_final
  with _.
  ( assert (
      PWL.paired_protected_handshake_contiguous_replay_views
        server_mid
        client_mid
        server_material
        client_material
        sent_msg0
        received_msg0
        sent_msg1
        received_msg1
        server_auth_skip
        client_auth_skip
        sent_msg2
        received_msg2
        client_verify_skip
        sent_msg3
        received_msg3
        verified_server_finished
        client_app_write_material
        client_app_read_material
        server_app_write_material
        sent_msg4
        received_msg4
        client_finished_rest
        server_finished_rest
        server_raw_sent
        server_raw_received
        client_raw_sent
        client_raw_received
        server_final
        client_final);
    introduce exists
      (server_mid':connection_model)
      (client_mid':connection_model)
      (server_raw_sent':B.bytes)
      (server_raw_received':B.bytes)
      (client_raw_sent':B.bytes)
      (client_raw_received':B.bytes).
      Seq.equal server_raw_sent' client_raw_received' /\
      Seq.equal client_raw_sent' server_raw_received' /\
      PWL.paired_protected_handshake_contiguous_replay_views
        server_mid'
        client_mid'
        server_material
        client_material
        sent_msg0
        received_msg0
        sent_msg1
        received_msg1
        server_auth_skip
        client_auth_skip
        sent_msg2
        received_msg2
        client_verify_skip
        sent_msg3
        received_msg3
        verified_server_finished
        client_app_write_material
        client_app_read_material
        server_app_write_material
        sent_msg4
        received_msg4
        client_finished_rest
        server_finished_rest
        server_raw_sent'
        server_raw_received'
        client_raw_sent'
        client_raw_received'
        server_final
        client_final
    with
      server_mid
      client_mid
      server_raw_sent
      server_raw_received
      client_raw_sent
      client_raw_received
    and () )
#pop-options
