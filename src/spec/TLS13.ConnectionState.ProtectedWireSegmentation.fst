module TLS13.ConnectionState.ProtectedWireSegmentation

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWR = TLS13.ConnectionState.ProtectedWireReplay
module PWS = TLS13.ConnectionState.ProtectedWireStream
module Seq = FStar.Seq
module WFL = TLS13.Spec.WireFormatLemmas

open TLS13.Spec.ConnectionState

#push-options "--split_queries always --z3rlimit 10"
let lemma_bytes_append_equal
  (left right left_tail right_tail:B.bytes)
  : Lemma
      (requires
        Seq.equal left right /\
        Seq.equal left_tail right_tail)
      (ensures
        Seq.equal
          (B.append left left_tail)
          (B.append right right_tail))
=
  Seq.lemma_eq_elim left right;
  Seq.lemma_eq_elim left_tail right_tail;
  assert (Seq.equal
    (B.append left left_tail)
    (B.append right right_tail))

let lemma_bytes_append_assoc
  (x y z:B.bytes)
  : Lemma
      (ensures
        Seq.equal
          (B.append (B.append x y) z)
          (B.append x (B.append y z)))
=
  Seq.append_assoc x y z

let lemma_sent_client_hello_raw_from_sent_replay_single
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
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }]
          raw_sent
          raw_received
          final_model)
      (ensures
        Seq.equal raw_sent
          (serialized_cleartext_tls_message
            (M.TlsHandshake (M.ClientHello ch))) /\
        Seq.equal raw_received B.empty)
=
  let ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ClientHello ch);
  } in
  PWR.lemma_conn_events_sent_seal_replay_head
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
    Seq.equal raw_sent
      (serialized_cleartext_tls_message
        (M.TlsHandshake (M.ClientHello ch))) /\
    Seq.equal raw_received B.empty
  with _.
  ( assert (cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello ch))
      delta_sent);
    assert (Seq.equal delta_sent
      (serialized_cleartext_tls_message
        (M.TlsHandshake (M.ClientHello ch))));
    assert (Seq.equal delta_received B.empty);
    assert (Seq.equal tail_sent B.empty);
    assert (Seq.equal tail_received B.empty);
    Seq.lemma_eq_elim tail_sent B.empty;
    Seq.lemma_eq_elim tail_received B.empty;
    assert (Seq.equal (B.append delta_sent tail_sent) delta_sent);
    assert (Seq.equal (B.append delta_received tail_received) B.empty);
    Seq.lemma_eq_elim raw_sent (B.append delta_sent tail_sent);
    Seq.lemma_eq_elim raw_received (B.append delta_received tail_received);
    assert (Seq.equal raw_sent delta_sent);
    assert (Seq.equal raw_received B.empty);
    Seq.lemma_eq_elim raw_sent delta_sent;
    assert (Seq.equal raw_sent
      (serialized_cleartext_tls_message
        (M.TlsHandshake (M.ClientHello ch)))) )

let lemma_sent_server_hello_raw_from_sent_replay_single
  (model:connection_model)
  (sh:M.server_hello)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_sent_seal_replay
          model
          [ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }]
          raw_sent
          raw_received
          final_model)
      (ensures
        Seq.equal raw_sent
          (serialized_cleartext_tls_message
            (M.TlsHandshake (M.ServerHello sh))) /\
        Seq.equal raw_received B.empty)
=
  let ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  } in
  PWR.lemma_conn_events_sent_seal_replay_head
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
    Seq.equal raw_sent
      (serialized_cleartext_tls_message
        (M.TlsHandshake (M.ServerHello sh))) /\
    Seq.equal raw_received B.empty
  with _.
  ( assert (cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello sh))
      delta_sent);
    assert (Seq.equal delta_sent
      (serialized_cleartext_tls_message
        (M.TlsHandshake (M.ServerHello sh))));
    assert (Seq.equal delta_received B.empty);
    assert (Seq.equal tail_sent B.empty);
    assert (Seq.equal tail_received B.empty);
    Seq.lemma_eq_elim tail_sent B.empty;
    Seq.lemma_eq_elim tail_received B.empty;
    assert (Seq.equal (B.append delta_sent tail_sent) delta_sent);
    assert (Seq.equal (B.append delta_received tail_received) B.empty);
    Seq.lemma_eq_elim raw_sent (B.append delta_sent tail_sent);
    Seq.lemma_eq_elim raw_received (B.append delta_received tail_received);
    assert (Seq.equal raw_sent delta_sent);
    assert (Seq.equal raw_received B.empty);
    Seq.lemma_eq_elim raw_sent delta_sent;
    assert (Seq.equal raw_sent
      (serialized_cleartext_tls_message
        (M.TlsHandshake (M.ServerHello sh)))) )

let lemma_received_server_hello_raw_from_received_replay_single
  (model:connection_model)
  (sh:M.server_hello)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_received_decode_replay
          model
          [ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }]
          raw_sent
          raw_received
          final_model)
      (ensures
        Seq.equal raw_sent B.empty /\
        Seq.equal raw_received
          (serialized_cleartext_tls_message
            (M.TlsHandshake (M.ServerHello sh))))
=
  let ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  } in
  PWR.lemma_conn_events_received_decode_replay_head
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
    Seq.equal raw_received
      (serialized_cleartext_tls_message
        (M.TlsHandshake (M.ServerHello sh)))
  with _.
  ( assert (Seq.equal delta_sent B.empty);
    assert (received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello sh))
      delta_received);
    assert (cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello sh))
      delta_received);
    assert (Seq.equal delta_received
      (serialized_cleartext_tls_message
        (M.TlsHandshake (M.ServerHello sh))));
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
    assert (Seq.equal raw_received
      (serialized_cleartext_tls_message
        (M.TlsHandshake (M.ServerHello sh)))) )

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
  PWR.lemma_conn_events_sent_seal_replay_head
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
  PWR.lemma_conn_events_received_decode_replay_head
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

let lemma_paired_replay_split_prefixes_equal_uniform_empty
  (server_model:connection_model)
  (client_model:connection_model)
  (server_suffix:list conn_event)
  (client_suffix:list conn_event)
  : Lemma
      (paired_replay_split_prefixes_equal_uniform
        server_model
        client_model
        []
        server_suffix
        []
        client_suffix)
=
  introduce forall
    (server_full_sent:B.bytes)
    (server_full_received:B.bytes)
    (client_full_sent:B.bytes)
    (client_full_received:B.bytes)
    (server_final:connection_model)
    (client_final:connection_model).
    Seq.equal server_full_sent client_full_received /\
    Seq.equal client_full_sent server_full_received ==>
    paired_replay_split_prefixes_equal_with_full_streams
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
      client_final
  with
    introduce _ ==> _ with _.
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

let lemma_same_endpoint_replay_split_prefixes_equal_uniform_empty
  (model:connection_model)
  (suffix:list conn_event)
  : Lemma
      (same_endpoint_replay_split_prefixes_equal_uniform
        model
        []
        suffix)
=
  introduce forall
    (raw_sent:B.bytes)
    (raw_received:B.bytes)
    (final_model:connection_model).
    same_endpoint_replay_split_prefixes_equal
      model
      []
      suffix
      raw_sent
      raw_received
      final_model
  with
    lemma_same_endpoint_replay_split_prefixes_equal_empty
      model
      suffix
      raw_sent
      raw_received
      final_model

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
    ( PWR.lemma_conn_events_sent_seal_replay_head
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
      ( PWR.lemma_conn_events_received_decode_replay_head
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

let lemma_same_endpoint_replay_split_prefixes_equal_uniform_cons_local
  (model:connection_model)
  (ev:local_event)
  (tail:list conn_event)
  (suffix:list conn_event)
  (post_model:connection_model)
  : Lemma
      (requires
        step_model model (ConnLocalEvent ev) == Some post_model /\
        same_endpoint_replay_split_prefixes_equal_uniform
          post_model
          tail
          suffix)
      (ensures
        same_endpoint_replay_split_prefixes_equal_uniform
          model
          (ConnLocalEvent ev :: tail)
          suffix)
=
  introduce forall
    (raw_sent:B.bytes)
    (raw_received:B.bytes)
    (final_model:connection_model).
    same_endpoint_replay_split_prefixes_equal
      model
      (ConnLocalEvent ev :: tail)
      suffix
      raw_sent
      raw_received
      final_model
  with
    lemma_same_endpoint_replay_split_prefixes_equal_cons_local
      model
      ev
      tail
      suffix
      raw_sent
      raw_received
      final_model
      post_model

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

let lemma_same_endpoint_replay_split_prefixes_equal_uniform_cons_sent_cleartext
  (model:connection_model)
  (msg:M.tls_message)
  (tail:list conn_event)
  (suffix:list conn_event)
  (post_model:connection_model)
  : Lemma
      (requires
        network_message_is_cleartext CL.Sent msg == true /\
        step_model
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          }) == Some post_model /\
        same_endpoint_replay_split_prefixes_equal_uniform
          post_model
          tail
          suffix)
      (ensures
        same_endpoint_replay_split_prefixes_equal_uniform
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          } :: tail)
          suffix)
=
  let ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = msg;
  } in
  introduce forall
    (raw_sent:B.bytes)
    (raw_received:B.bytes)
    (final_model:connection_model).
    same_endpoint_replay_split_prefixes_equal
      model
      (ev :: tail)
      suffix
      raw_sent
      raw_received
      final_model
  with
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
        (ev :: tail)
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
        (ev :: tail)
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
      ( PWR.lemma_conn_events_sent_seal_replay_head
          model
          ev
          tail
          sent_prefix_sent
          sent_prefix_received
          sent_mid;
        eliminate exists sent_head_model sent_delta_sent sent_delta_received
          sent_tail_sent sent_tail_received.
          legal_event model ev /\
          step_model model ev == Some sent_head_model /\
          event_raw_delta_legal model ev sent_delta_sent sent_delta_received /\
          sent_event_nonempty_seal_projection model ev sent_delta_sent /\
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
        ( PWR.lemma_conn_events_received_decode_replay_head
            model
            ev
            tail
            received_prefix_sent
            received_prefix_received
            received_mid;
          eliminate exists received_head_model received_delta_sent received_delta_received
            received_tail_sent received_tail_received.
            legal_event model ev /\
            step_model model ev == Some received_head_model /\
            event_raw_delta_legal model ev received_delta_sent received_delta_received /\
            received_event_nonempty_decode_projection model ev received_delta_received /\
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
            assert (cleartext_tls_message_raw msg sent_delta_sent);
            assert (cleartext_tls_message_raw msg received_delta_sent);
            assert (Seq.equal sent_delta_sent
              (serialized_cleartext_tls_message msg));
            assert (Seq.equal received_delta_sent
              (serialized_cleartext_tls_message msg));
            assert (Seq.equal sent_delta_sent received_delta_sent);
            assert (Seq.equal sent_delta_received B.empty);
            assert (Seq.equal received_delta_received B.empty);
            Seq.lemma_eq_elim
              raw_sent
              (B.append sent_prefix_sent sent_suffix_sent);
            Seq.lemma_eq_elim
              raw_sent
              (B.append received_prefix_sent received_suffix_sent);
            Seq.lemma_eq_elim sent_prefix_sent
              (B.append sent_delta_sent sent_tail_sent);
            Seq.lemma_eq_elim received_prefix_sent
              (B.append received_delta_sent received_tail_sent);
            lemma_bytes_append_assoc sent_delta_sent sent_tail_sent sent_suffix_sent;
            lemma_bytes_append_assoc received_delta_sent received_tail_sent received_suffix_sent;
            assert (Seq.equal raw_sent
              (B.append sent_delta_sent
                (B.append sent_tail_sent sent_suffix_sent)));
            assert (Seq.equal raw_sent
              (B.append received_delta_sent
                (B.append received_tail_sent received_suffix_sent)));
            assert (Seq.equal
              (B.append sent_delta_sent
                (B.append sent_tail_sent sent_suffix_sent))
              (B.append received_delta_sent
                (B.append received_tail_sent received_suffix_sent)));
            PWS.lemma_append_tails_equal_from_equal_heads
              sent_delta_sent
              (B.append sent_tail_sent sent_suffix_sent)
              received_delta_sent
              (B.append received_tail_sent received_suffix_sent);
            assert (Seq.equal
              (B.append sent_tail_sent sent_suffix_sent)
              (B.append received_tail_sent received_suffix_sent));
            Seq.lemma_eq_elim
              raw_received
              (B.append sent_prefix_received sent_suffix_received);
            Seq.lemma_eq_elim
              raw_received
              (B.append received_prefix_received received_suffix_received);
            Seq.lemma_eq_elim sent_prefix_received
              (B.append sent_delta_received sent_tail_received);
            Seq.lemma_eq_elim received_prefix_received
              (B.append received_delta_received received_tail_received);
            Seq.lemma_eq_elim sent_delta_received B.empty;
            Seq.lemma_eq_elim received_delta_received B.empty;
            CL.lemma_append_empty_left sent_tail_received;
            CL.lemma_append_empty_left received_tail_received;
            assert (Seq.equal
              (B.append sent_delta_received sent_tail_received)
              sent_tail_received);
            assert (Seq.equal
              (B.append received_delta_received received_tail_received)
              received_tail_received);
            assert (Seq.equal sent_prefix_received sent_tail_received);
            assert (Seq.equal received_prefix_received received_tail_received);
            Seq.lemma_eq_elim sent_prefix_received sent_tail_received;
            Seq.lemma_eq_elim received_prefix_received received_tail_received;
            assert (Seq.equal raw_received
              (B.append sent_tail_received sent_suffix_received));
            assert (Seq.equal raw_received
              (B.append received_tail_received received_suffix_received));
            assert (Seq.equal
              (B.append sent_tail_received sent_suffix_received)
              (B.append received_tail_received received_suffix_received));
            assert (same_endpoint_replay_split_prefixes_equal
              post_model
              tail
              suffix
              (B.append sent_tail_sent sent_suffix_sent)
              (B.append sent_tail_received sent_suffix_received)
              final_model);
            assert (Seq.equal sent_tail_sent received_tail_sent);
            assert (Seq.equal sent_tail_received received_tail_received);
            lemma_bytes_append_equal
              sent_delta_sent
              received_delta_sent
              sent_tail_sent
              received_tail_sent;
            assert (Seq.equal sent_prefix_sent received_prefix_sent);
            lemma_bytes_append_equal
              sent_delta_received
              received_delta_received
              sent_tail_received
              received_tail_received;
            assert (Seq.equal sent_prefix_received received_prefix_received) ) ) )

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

let lemma_same_endpoint_replay_split_prefixes_equal_uniform_cons_received_server_hello
  (model:connection_model)
  (sh:M.server_hello)
  (tail:list conn_event)
  (suffix:list conn_event)
  (post_model:connection_model)
  : Lemma
      (requires
        step_model
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) == Some post_model /\
        same_endpoint_replay_split_prefixes_equal_uniform
          post_model
          tail
          suffix)
      (ensures
        same_endpoint_replay_split_prefixes_equal_uniform
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          } :: tail)
          suffix)
=
  let msg = M.TlsHandshake (M.ServerHello sh) in
  let ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = msg;
  } in
  introduce forall
    (raw_sent:B.bytes)
    (raw_received:B.bytes)
    (final_model:connection_model).
    same_endpoint_replay_split_prefixes_equal
      model
      (ev :: tail)
      suffix
      raw_sent
      raw_received
      final_model
  with
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
        (ev :: tail)
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
        (ev :: tail)
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
      ( PWR.lemma_conn_events_sent_seal_replay_head
          model
          ev
          tail
          sent_prefix_sent
          sent_prefix_received
          sent_mid;
        eliminate exists sent_head_model sent_delta_sent sent_delta_received
          sent_tail_sent sent_tail_received.
          legal_event model ev /\
          step_model model ev == Some sent_head_model /\
          event_raw_delta_legal model ev sent_delta_sent sent_delta_received /\
          sent_event_nonempty_seal_projection model ev sent_delta_sent /\
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
        ( PWR.lemma_conn_events_received_decode_replay_head
            model
            ev
            tail
            received_prefix_sent
            received_prefix_received
            received_mid;
          eliminate exists received_head_model received_delta_sent received_delta_received
            received_tail_sent received_tail_received.
            legal_event model ev /\
            step_model model ev == Some received_head_model /\
            event_raw_delta_legal model ev received_delta_sent received_delta_received /\
            received_event_nonempty_decode_projection model ev received_delta_received /\
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
            assert (Seq.equal received_delta_sent B.empty);
            assert (cleartext_tls_message_raw msg sent_delta_received);
            assert (cleartext_tls_message_raw msg received_delta_received);
            assert (Seq.equal sent_delta_received
              (serialized_cleartext_tls_message msg));
            assert (Seq.equal received_delta_received
              (serialized_cleartext_tls_message msg));
            assert (Seq.equal sent_delta_received received_delta_received);
            Seq.lemma_eq_elim
              raw_sent
              (B.append sent_prefix_sent sent_suffix_sent);
            Seq.lemma_eq_elim
              raw_sent
              (B.append received_prefix_sent received_suffix_sent);
            Seq.lemma_eq_elim sent_prefix_sent
              (B.append sent_delta_sent sent_tail_sent);
            Seq.lemma_eq_elim received_prefix_sent
              (B.append received_delta_sent received_tail_sent);
            Seq.lemma_eq_elim sent_delta_sent B.empty;
            Seq.lemma_eq_elim received_delta_sent B.empty;
            CL.lemma_append_empty_left sent_tail_sent;
            CL.lemma_append_empty_left received_tail_sent;
            assert (Seq.equal
              (B.append sent_delta_sent sent_tail_sent)
              sent_tail_sent);
            assert (Seq.equal
              (B.append received_delta_sent received_tail_sent)
              received_tail_sent);
            assert (Seq.equal sent_prefix_sent sent_tail_sent);
            assert (Seq.equal received_prefix_sent received_tail_sent);
            Seq.lemma_eq_elim sent_prefix_sent sent_tail_sent;
            Seq.lemma_eq_elim received_prefix_sent received_tail_sent;
            assert (Seq.equal raw_sent
              (B.append sent_tail_sent sent_suffix_sent));
            assert (Seq.equal raw_sent
              (B.append received_tail_sent received_suffix_sent));
            assert (Seq.equal
              (B.append sent_tail_sent sent_suffix_sent)
              (B.append received_tail_sent received_suffix_sent));
            Seq.lemma_eq_elim
              raw_received
              (B.append sent_prefix_received sent_suffix_received);
            Seq.lemma_eq_elim
              raw_received
              (B.append received_prefix_received received_suffix_received);
            Seq.lemma_eq_elim sent_prefix_received
              (B.append sent_delta_received sent_tail_received);
            Seq.lemma_eq_elim received_prefix_received
              (B.append received_delta_received received_tail_received);
            lemma_bytes_append_assoc
              sent_delta_received
              sent_tail_received
              sent_suffix_received;
            lemma_bytes_append_assoc
              received_delta_received
              received_tail_received
              received_suffix_received;
            assert (Seq.equal raw_received
              (B.append sent_delta_received
                (B.append sent_tail_received sent_suffix_received)));
            assert (Seq.equal raw_received
              (B.append received_delta_received
                (B.append received_tail_received received_suffix_received)));
            assert (Seq.equal
              (B.append sent_delta_received
                (B.append sent_tail_received sent_suffix_received))
              (B.append received_delta_received
                (B.append received_tail_received received_suffix_received)));
            PWS.lemma_append_tails_equal_from_equal_heads
              sent_delta_received
              (B.append sent_tail_received sent_suffix_received)
              received_delta_received
              (B.append received_tail_received received_suffix_received);
            assert (Seq.equal
              (B.append sent_tail_received sent_suffix_received)
              (B.append received_tail_received received_suffix_received));
            assert (same_endpoint_replay_split_prefixes_equal
              post_model
              tail
              suffix
              (B.append sent_tail_sent sent_suffix_sent)
              (B.append sent_tail_received sent_suffix_received)
              final_model);
            assert (Seq.equal sent_tail_sent received_tail_sent);
            assert (Seq.equal sent_tail_received received_tail_received);
            lemma_bytes_append_equal
              sent_delta_sent
              received_delta_sent
              sent_tail_sent
              received_tail_sent;
            assert (Seq.equal sent_prefix_sent received_prefix_sent);
            lemma_bytes_append_equal
              sent_delta_received
              received_delta_received
              sent_tail_received
              received_tail_received;
            assert (Seq.equal sent_prefix_received received_prefix_received) ) ) )

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
      PWS.lemma_append_heads_equal_same_len
       sent_prefix_received
       sent_suffix_received
       received_prefix_received
       received_suffix_received )

let lemma_same_endpoint_replay_split_prefixes_equal_uniform_cons_received_client_hello
  (model:connection_model)
  (ch:M.client_hello)
  (tail:list conn_event)
  (suffix:list conn_event)
  (post_model:connection_model)
  : Lemma
      (requires
        step_model
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) == Some post_model /\
        same_endpoint_replay_split_prefixes_equal_uniform
          post_model
          tail
          suffix)
      (ensures
        same_endpoint_replay_split_prefixes_equal_uniform
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          } :: tail)
          suffix)
=
  let msg = M.TlsHandshake (M.ClientHello ch) in
  let ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = msg;
  } in
  introduce forall
    (raw_sent:B.bytes)
    (raw_received:B.bytes)
    (final_model:connection_model).
    same_endpoint_replay_split_prefixes_equal
      model
      (ev :: tail)
      suffix
      raw_sent
      raw_received
      final_model
  with
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
        (ev :: tail)
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
        (ev :: tail)
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
      ( PWR.lemma_conn_events_sent_seal_replay_head
          model
          ev
          tail
          sent_prefix_sent
          sent_prefix_received
          sent_mid;
        eliminate exists sent_head_model sent_delta_sent sent_delta_received
          sent_tail_sent sent_tail_received.
          legal_event model ev /\
          step_model model ev == Some sent_head_model /\
          event_raw_delta_legal model ev sent_delta_sent sent_delta_received /\
          sent_event_nonempty_seal_projection model ev sent_delta_sent /\
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
        ( PWR.lemma_conn_events_received_decode_replay_head
            model
            ev
            tail
            received_prefix_sent
            received_prefix_received
            received_mid;
          eliminate exists received_head_model received_delta_sent received_delta_received
            received_tail_sent received_tail_received.
            legal_event model ev /\
            step_model model ev == Some received_head_model /\
            event_raw_delta_legal model ev received_delta_sent received_delta_received /\
            received_event_nonempty_decode_projection model ev received_delta_received /\
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
            assert (Seq.equal received_delta_sent B.empty);
            assert (received_cleartext_tls_message_raw msg sent_delta_received);
            assert (received_cleartext_tls_message_raw msg received_delta_received);
            WFL.lemma_received_client_hello_raw_length ch sent_delta_received;
            WFL.lemma_received_client_hello_raw_length ch received_delta_received;
            assert (B.length sent_delta_received ==
              B.length received_delta_received);
            Seq.lemma_eq_elim
              raw_sent
              (B.append sent_prefix_sent sent_suffix_sent);
            Seq.lemma_eq_elim
              raw_sent
              (B.append received_prefix_sent received_suffix_sent);
            Seq.lemma_eq_elim sent_prefix_sent
              (B.append sent_delta_sent sent_tail_sent);
            Seq.lemma_eq_elim received_prefix_sent
              (B.append received_delta_sent received_tail_sent);
            Seq.lemma_eq_elim sent_delta_sent B.empty;
            Seq.lemma_eq_elim received_delta_sent B.empty;
            CL.lemma_append_empty_left sent_tail_sent;
            CL.lemma_append_empty_left received_tail_sent;
            assert (Seq.equal
              (B.append sent_delta_sent sent_tail_sent)
              sent_tail_sent);
            assert (Seq.equal
              (B.append received_delta_sent received_tail_sent)
              received_tail_sent);
            assert (Seq.equal sent_prefix_sent sent_tail_sent);
            assert (Seq.equal received_prefix_sent received_tail_sent);
            Seq.lemma_eq_elim sent_prefix_sent sent_tail_sent;
            Seq.lemma_eq_elim received_prefix_sent received_tail_sent;
            assert (Seq.equal raw_sent
              (B.append sent_tail_sent sent_suffix_sent));
            assert (Seq.equal raw_sent
              (B.append received_tail_sent received_suffix_sent));
            assert (Seq.equal
              (B.append sent_tail_sent sent_suffix_sent)
              (B.append received_tail_sent received_suffix_sent));
            Seq.lemma_eq_elim
              raw_received
              (B.append sent_prefix_received sent_suffix_received);
            Seq.lemma_eq_elim
              raw_received
              (B.append received_prefix_received received_suffix_received);
            Seq.lemma_eq_elim sent_prefix_received
              (B.append sent_delta_received sent_tail_received);
            Seq.lemma_eq_elim received_prefix_received
              (B.append received_delta_received received_tail_received);
            lemma_bytes_append_assoc
              sent_delta_received
              sent_tail_received
              sent_suffix_received;
            lemma_bytes_append_assoc
              received_delta_received
              received_tail_received
              received_suffix_received;
            assert (Seq.equal raw_received
              (B.append sent_delta_received
                (B.append sent_tail_received sent_suffix_received)));
            assert (Seq.equal raw_received
              (B.append received_delta_received
                (B.append received_tail_received received_suffix_received)));
            assert (Seq.equal
              (B.append sent_delta_received
                (B.append sent_tail_received sent_suffix_received))
              (B.append received_delta_received
                (B.append received_tail_received received_suffix_received)));
            PWS.lemma_append_heads_equal_same_len
              sent_delta_received
              (B.append sent_tail_received sent_suffix_received)
              received_delta_received
              (B.append received_tail_received received_suffix_received);
            assert (Seq.equal sent_delta_received received_delta_received);
            PWS.lemma_append_tails_equal_from_equal_heads
              sent_delta_received
              (B.append sent_tail_received sent_suffix_received)
              received_delta_received
              (B.append received_tail_received received_suffix_received);
            assert (Seq.equal
              (B.append sent_tail_received sent_suffix_received)
              (B.append received_tail_received received_suffix_received));
            assert (same_endpoint_replay_split_prefixes_equal
              post_model
              tail
              suffix
              (B.append sent_tail_sent sent_suffix_sent)
              (B.append sent_tail_received sent_suffix_received)
              final_model);
            assert (Seq.equal sent_tail_sent received_tail_sent);
            assert (Seq.equal sent_tail_received received_tail_received);
            lemma_bytes_append_equal
              sent_delta_sent
              received_delta_sent
              sent_tail_sent
              received_tail_sent;
            assert (Seq.equal sent_prefix_sent received_prefix_sent);
            lemma_bytes_append_equal
              sent_delta_received
              received_delta_received
              sent_tail_received
              received_tail_received;
            assert (Seq.equal sent_prefix_received received_prefix_received) ) ) )

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
    ( PWR.lemma_conn_events_sent_seal_replay_head
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
      ( PWR.lemma_conn_events_received_decode_replay_head
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

let lemma_paired_replay_split_prefixes_equal_uniform_cons_client_hello
  (server_model:connection_model)
  (client_model:connection_model)
  (ch:M.client_hello)
  (server_tail:list conn_event)
  (server_suffix:list conn_event)
  (client_tail:list conn_event)
  (client_suffix:list conn_event)
  (server_post:connection_model)
  (client_post:connection_model)
  : Lemma
      (requires
        step_model
          server_model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) == Some server_post /\
        step_model
          client_model
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) == Some client_post /\
        paired_replay_split_prefixes_equal_uniform
          server_post
          client_post
          server_tail
          server_suffix
          client_tail
          client_suffix)
      (ensures
        paired_replay_split_prefixes_equal_uniform
          server_model
          client_model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          } :: server_tail)
          server_suffix
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          } :: client_tail)
          client_suffix)
=
  let server_head = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ClientHello ch);
  } in
  let client_head = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ClientHello ch);
  } in
  introduce forall
    (server_full_sent:B.bytes)
    (server_full_received:B.bytes)
    (client_full_sent:B.bytes)
    (client_full_received:B.bytes)
    (server_final:connection_model)
    (client_final:connection_model).
    Seq.equal server_full_sent client_full_received /\
    Seq.equal client_full_sent server_full_received ==>
    paired_replay_split_prefixes_equal_with_full_streams
      server_model
      client_model
      (server_head :: server_tail)
      server_suffix
      (client_head :: client_tail)
      client_suffix
      server_full_sent
      server_full_received
      client_full_sent
      client_full_received
      server_final
      client_final
  with
    introduce _ ==> _ with _.
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
        (server_head :: server_tail)
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
        (server_head :: server_tail)
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
        (client_head :: client_tail)
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
        (client_head :: client_tail)
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
      ( PWR.lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
          server_model
          [server_head]
          server_tail
          server_prefix_sent
          server_prefix_received
          server_mid
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
            lemma_same_endpoint_replay_split_prefixes_equal_single_received_client_hello
              server_model
              ch
              server_tail
              server_prefix_sent
              server_prefix_received
              server_mid;
            assert (Seq.equal sent_prefix_sent received_prefix_sent);
            assert (Seq.equal sent_prefix_received received_prefix_received));
        eliminate exists
          (server_head_mid:connection_model)
          (server_head_sent:B.bytes)
          (server_head_received:B.bytes)
          (server_tail_sent:B.bytes)
          (server_tail_received:B.bytes).
          Seq.equal server_prefix_sent
            (B.append server_head_sent server_tail_sent) /\
          Seq.equal server_prefix_received
            (B.append server_head_received server_tail_received) /\
          conn_events_sent_seal_replay
            server_model
            [server_head]
            server_head_sent
            server_head_received
            server_head_mid /\
          conn_events_sent_seal_replay
            server_head_mid
            server_tail
            server_tail_sent
            server_tail_received
            server_mid /\
          conn_events_received_decode_replay
            server_model
            [server_head]
            server_head_sent
            server_head_received
            server_head_mid /\
          conn_events_received_decode_replay
            server_head_mid
            server_tail
            server_tail_sent
            server_tail_received
            server_mid
        returns
          Seq.equal server_prefix_sent client_prefix_received /\
          Seq.equal client_prefix_sent server_prefix_received
        with _.
        ( PWR.lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
            client_model
            [client_head]
            client_tail
            client_prefix_sent
            client_prefix_received
            client_mid
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
              lemma_same_endpoint_replay_split_prefixes_equal_single_sent_cleartext
                client_model
                (M.TlsHandshake (M.ClientHello ch))
                client_tail
                client_prefix_sent
                client_prefix_received
                client_mid;
              assert (Seq.equal sent_prefix_sent received_prefix_sent);
              assert (Seq.equal sent_prefix_received received_prefix_received));
          eliminate exists
            (client_head_mid:connection_model)
            (client_head_sent:B.bytes)
            (client_head_received:B.bytes)
            (client_tail_sent:B.bytes)
            (client_tail_received:B.bytes).
            Seq.equal client_prefix_sent
              (B.append client_head_sent client_tail_sent) /\
            Seq.equal client_prefix_received
              (B.append client_head_received client_tail_received) /\
            conn_events_sent_seal_replay
              client_model
              [client_head]
              client_head_sent
              client_head_received
              client_head_mid /\
            conn_events_sent_seal_replay
              client_head_mid
              client_tail
              client_tail_sent
              client_tail_received
              client_mid /\
            conn_events_received_decode_replay
              client_model
              [client_head]
              client_head_sent
              client_head_received
              client_head_mid /\
            conn_events_received_decode_replay
              client_head_mid
              client_tail
              client_tail_sent
              client_tail_received
              client_mid
          returns
            Seq.equal server_prefix_sent client_prefix_received /\
            Seq.equal client_prefix_sent server_prefix_received
          with _.
          ( assert (server_head_mid == server_post);
            assert (client_head_mid == client_post);
            lemma_received_client_hello_raw_from_sent_replay_single
              server_model
              ch
              server_head_sent
              server_head_received
              server_head_mid;
            lemma_sent_client_hello_raw_from_sent_replay_single
              client_model
              ch
              client_head_sent
              client_head_received
              client_head_mid;
            assert (Seq.equal server_head_sent B.empty);
            assert (Seq.equal client_head_received B.empty);
            WFL.lemma_received_client_hello_raw_length ch server_head_received;
            assert (B.length client_head_sent == B.length server_head_received);
            Seq.lemma_eq_elim
              server_full_sent
              (B.append server_prefix_sent server_suffix_sent);
            Seq.lemma_eq_elim
              client_full_received
              (B.append client_prefix_received client_suffix_received);
            Seq.lemma_eq_elim server_prefix_sent
              (B.append server_head_sent server_tail_sent);
            Seq.lemma_eq_elim client_prefix_received
              (B.append client_head_received client_tail_received);
            Seq.lemma_eq_elim server_head_sent B.empty;
            Seq.lemma_eq_elim client_head_received B.empty;
            CL.lemma_append_empty_left server_tail_sent;
            CL.lemma_append_empty_left client_tail_received;
            assert (Seq.equal
              (B.append server_head_sent server_tail_sent)
              server_tail_sent);
            assert (Seq.equal
              (B.append client_head_received client_tail_received)
              client_tail_received);
            assert (Seq.equal server_prefix_sent server_tail_sent);
            assert (Seq.equal client_prefix_received client_tail_received);
            Seq.lemma_eq_elim server_prefix_sent server_tail_sent;
            Seq.lemma_eq_elim client_prefix_received client_tail_received;
            assert (Seq.equal server_full_sent
              (B.append server_tail_sent server_suffix_sent));
            assert (Seq.equal client_full_received
              (B.append client_tail_received client_suffix_received));
            assert (Seq.equal
              (B.append server_tail_sent server_suffix_sent)
              (B.append client_tail_received client_suffix_received));
            Seq.lemma_eq_elim
              client_full_sent
              (B.append client_prefix_sent client_suffix_sent);
            Seq.lemma_eq_elim
              server_full_received
              (B.append server_prefix_received server_suffix_received);
            Seq.lemma_eq_elim client_prefix_sent
              (B.append client_head_sent client_tail_sent);
            Seq.lemma_eq_elim server_prefix_received
              (B.append server_head_received server_tail_received);
            lemma_bytes_append_assoc client_head_sent client_tail_sent client_suffix_sent;
            lemma_bytes_append_assoc server_head_received server_tail_received server_suffix_received;
            assert (Seq.equal client_full_sent
              (B.append client_head_sent
                (B.append client_tail_sent client_suffix_sent)));
            assert (Seq.equal server_full_received
              (B.append server_head_received
                (B.append server_tail_received server_suffix_received)));
            assert (Seq.equal
              (B.append client_head_sent
                (B.append client_tail_sent client_suffix_sent))
              (B.append server_head_received
                (B.append server_tail_received server_suffix_received)));
            PWS.lemma_append_heads_equal_same_len
              client_head_sent
              (B.append client_tail_sent client_suffix_sent)
              server_head_received
              (B.append server_tail_received server_suffix_received);
            assert (Seq.equal client_head_sent server_head_received);
            PWS.lemma_append_tails_equal_from_equal_heads
              client_head_sent
              (B.append client_tail_sent client_suffix_sent)
              server_head_received
              (B.append server_tail_received server_suffix_received);
            assert (Seq.equal
              (B.append client_tail_sent client_suffix_sent)
              (B.append server_tail_received server_suffix_received));
            assert (paired_replay_split_prefixes_equal_with_full_streams
              server_post
              client_post
              server_tail
              server_suffix
              client_tail
              client_suffix
              (B.append server_tail_sent server_suffix_sent)
              (B.append server_tail_received server_suffix_received)
              (B.append client_tail_sent client_suffix_sent)
              (B.append client_tail_received client_suffix_received)
              server_final
              client_final);
            assert (Seq.equal server_tail_sent client_tail_received);
            assert (Seq.equal client_tail_sent server_tail_received);
            lemma_bytes_append_equal
              server_head_sent
              client_head_received
              server_tail_sent
              client_tail_received;
            assert (Seq.equal server_prefix_sent client_prefix_received);
            lemma_bytes_append_equal
              client_head_sent
              server_head_received
              client_tail_sent
              server_tail_received;
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
    ( PWR.lemma_conn_events_sent_seal_replay_head
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
      ( PWR.lemma_conn_events_received_decode_replay_head
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

let lemma_paired_replay_split_prefixes_equal_uniform_cons_server_local
  (server_model:connection_model)
  (client_model:connection_model)
  (server_ev:local_event)
  (server_tail:list conn_event)
  (server_suffix:list conn_event)
  (client_prefix:list conn_event)
  (client_suffix:list conn_event)
  (server_post:connection_model)
  : Lemma
      (requires
        step_model server_model (ConnLocalEvent server_ev) == Some server_post /\
        paired_replay_split_prefixes_equal_uniform
          server_post
          client_model
          server_tail
          server_suffix
          client_prefix
          client_suffix)
      (ensures
        paired_replay_split_prefixes_equal_uniform
          server_model
          client_model
          (ConnLocalEvent server_ev :: server_tail)
          server_suffix
          client_prefix
          client_suffix)
=
  introduce forall
    (server_full_sent:B.bytes)
    (server_full_received:B.bytes)
    (client_full_sent:B.bytes)
    (client_full_received:B.bytes)
    (server_final:connection_model)
    (client_final:connection_model).
    Seq.equal server_full_sent client_full_received /\
    Seq.equal client_full_sent server_full_received ==>
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
      client_final
  with
    introduce _ ==> _ with _.
    ( assert (paired_replay_split_prefixes_equal_with_full_streams
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
        client_final);
      lemma_paired_replay_split_prefixes_equal_with_full_streams_cons_server_local
        server_model
        client_model
        server_ev
        server_tail
        server_suffix
        client_prefix
        client_suffix
        server_full_sent
        server_full_received
        client_full_sent
        client_full_received
        server_final
        client_final
        server_post )

let lemma_paired_replay_split_prefixes_equal_uniform_cons_client_local
  (server_model:connection_model)
  (client_model:connection_model)
  (client_ev:local_event)
  (server_prefix:list conn_event)
  (server_suffix:list conn_event)
  (client_tail:list conn_event)
  (client_suffix:list conn_event)
  (client_post:connection_model)
  : Lemma
      (requires
        step_model client_model (ConnLocalEvent client_ev) == Some client_post /\
        paired_replay_split_prefixes_equal_uniform
          server_model
          client_post
          server_prefix
          server_suffix
          client_tail
          client_suffix)
      (ensures
        paired_replay_split_prefixes_equal_uniform
          server_model
          client_model
          server_prefix
          server_suffix
          (ConnLocalEvent client_ev :: client_tail)
          client_suffix)
=
  introduce forall
    (server_full_sent:B.bytes)
    (server_full_received:B.bytes)
    (client_full_sent:B.bytes)
    (client_full_received:B.bytes)
    (server_final:connection_model)
    (client_final:connection_model).
    Seq.equal server_full_sent client_full_received /\
    Seq.equal client_full_sent server_full_received ==>
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
      client_final
  with
    introduce _ ==> _ with _.
    ( assert (paired_replay_split_prefixes_equal_with_full_streams
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
        client_final);
      lemma_paired_replay_split_prefixes_equal_with_full_streams_cons_client_local
        server_model
        client_model
        client_ev
        server_prefix
        server_suffix
        client_tail
        client_suffix
        server_full_sent
        server_full_received
        client_full_sent
        client_full_received
        server_final
        client_final
        client_post )

let lemma_paired_replay_split_prefixes_equal_uniform_cons_server_hello
  (server_model:connection_model)
  (client_model:connection_model)
  (sh:M.server_hello)
  (server_tail:list conn_event)
  (server_suffix:list conn_event)
  (client_tail:list conn_event)
  (client_suffix:list conn_event)
  (server_post:connection_model)
  (client_post:connection_model)
  : Lemma
      (requires
        step_model
          server_model
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) == Some server_post /\
        step_model
          client_model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) == Some client_post /\
        paired_replay_split_prefixes_equal_uniform
          server_post
          client_post
          server_tail
          server_suffix
          client_tail
          client_suffix)
      (ensures
        paired_replay_split_prefixes_equal_uniform
          server_model
          client_model
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          } :: server_tail)
          server_suffix
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          } :: client_tail)
          client_suffix)
=
  let server_head = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  } in
  let client_head = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  } in
  introduce forall
    (server_full_sent:B.bytes)
    (server_full_received:B.bytes)
    (client_full_sent:B.bytes)
    (client_full_received:B.bytes)
    (server_final:connection_model)
    (client_final:connection_model).
    Seq.equal server_full_sent client_full_received /\
    Seq.equal client_full_sent server_full_received ==>
    paired_replay_split_prefixes_equal_with_full_streams
      server_model
      client_model
      (server_head :: server_tail)
      server_suffix
      (client_head :: client_tail)
      client_suffix
      server_full_sent
      server_full_received
      client_full_sent
      client_full_received
      server_final
      client_final
  with
    introduce _ ==> _ with _.
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
        (server_head :: server_tail)
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
        (server_head :: server_tail)
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
        (client_head :: client_tail)
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
        (client_head :: client_tail)
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
      ( PWR.lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
          server_model
          [server_head]
          server_tail
          server_prefix_sent
          server_prefix_received
          server_mid
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
            lemma_same_endpoint_replay_split_prefixes_equal_single_sent_cleartext
              server_model
              (M.TlsHandshake (M.ServerHello sh))
              server_tail
              server_prefix_sent
              server_prefix_received
              server_mid;
            assert (Seq.equal sent_prefix_sent received_prefix_sent);
            assert (Seq.equal sent_prefix_received received_prefix_received));
        eliminate exists
          (server_head_mid:connection_model)
          (server_head_sent:B.bytes)
          (server_head_received:B.bytes)
          (server_tail_sent:B.bytes)
          (server_tail_received:B.bytes).
          Seq.equal server_prefix_sent
            (B.append server_head_sent server_tail_sent) /\
          Seq.equal server_prefix_received
            (B.append server_head_received server_tail_received) /\
          conn_events_sent_seal_replay
            server_model
            [server_head]
            server_head_sent
            server_head_received
            server_head_mid /\
          conn_events_sent_seal_replay
            server_head_mid
            server_tail
            server_tail_sent
            server_tail_received
            server_mid /\
          conn_events_received_decode_replay
            server_model
            [server_head]
            server_head_sent
            server_head_received
            server_head_mid /\
          conn_events_received_decode_replay
            server_head_mid
            server_tail
            server_tail_sent
            server_tail_received
            server_mid
        returns
          Seq.equal server_prefix_sent client_prefix_received /\
          Seq.equal client_prefix_sent server_prefix_received
        with _.
        ( PWR.lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
            client_model
            [client_head]
            client_tail
            client_prefix_sent
            client_prefix_received
            client_mid
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
              lemma_same_endpoint_replay_split_prefixes_equal_single_received_server_hello
                client_model
                sh
                client_tail
                client_prefix_sent
                client_prefix_received
                client_mid;
              assert (Seq.equal sent_prefix_sent received_prefix_sent);
              assert (Seq.equal sent_prefix_received received_prefix_received));
          eliminate exists
            (client_head_mid:connection_model)
            (client_head_sent:B.bytes)
            (client_head_received:B.bytes)
            (client_tail_sent:B.bytes)
            (client_tail_received:B.bytes).
            Seq.equal client_prefix_sent
              (B.append client_head_sent client_tail_sent) /\
            Seq.equal client_prefix_received
              (B.append client_head_received client_tail_received) /\
            conn_events_sent_seal_replay
              client_model
              [client_head]
              client_head_sent
              client_head_received
              client_head_mid /\
            conn_events_sent_seal_replay
              client_head_mid
              client_tail
              client_tail_sent
              client_tail_received
              client_mid /\
            conn_events_received_decode_replay
              client_model
              [client_head]
              client_head_sent
              client_head_received
              client_head_mid /\
            conn_events_received_decode_replay
              client_head_mid
              client_tail
              client_tail_sent
              client_tail_received
              client_mid
          returns
            Seq.equal server_prefix_sent client_prefix_received /\
            Seq.equal client_prefix_sent server_prefix_received
          with _.
          ( assert (server_head_mid == server_post);
            assert (client_head_mid == client_post);
            lemma_sent_server_hello_raw_from_sent_replay_single
              server_model
              sh
              server_head_sent
              server_head_received
              server_head_mid;
            lemma_received_server_hello_raw_from_received_replay_single
              client_model
              sh
              client_head_sent
              client_head_received
              client_head_mid;
            assert (Seq.equal server_head_received B.empty);
            assert (Seq.equal client_head_sent B.empty);
            assert (B.length server_head_sent == B.length client_head_received);
            Seq.lemma_eq_elim
              server_full_received
              (B.append server_prefix_received server_suffix_received);
            Seq.lemma_eq_elim
              client_full_sent
              (B.append client_prefix_sent client_suffix_sent);
            Seq.lemma_eq_elim server_prefix_received
              (B.append server_head_received server_tail_received);
            Seq.lemma_eq_elim client_prefix_sent
              (B.append client_head_sent client_tail_sent);
            Seq.lemma_eq_elim server_head_received B.empty;
            Seq.lemma_eq_elim client_head_sent B.empty;
            CL.lemma_append_empty_left server_tail_received;
            CL.lemma_append_empty_left client_tail_sent;
            assert (Seq.equal
              (B.append server_head_received server_tail_received)
              server_tail_received);
            assert (Seq.equal
              (B.append client_head_sent client_tail_sent)
              client_tail_sent);
            assert (Seq.equal server_prefix_received server_tail_received);
            assert (Seq.equal client_prefix_sent client_tail_sent);
            Seq.lemma_eq_elim server_prefix_received server_tail_received;
            Seq.lemma_eq_elim client_prefix_sent client_tail_sent;
            assert (Seq.equal server_full_received
              (B.append server_tail_received server_suffix_received));
            assert (Seq.equal client_full_sent
              (B.append client_tail_sent client_suffix_sent));
            assert (Seq.equal
              (B.append client_tail_sent client_suffix_sent)
              (B.append server_tail_received server_suffix_received));
            Seq.lemma_eq_elim
              server_full_sent
              (B.append server_prefix_sent server_suffix_sent);
            Seq.lemma_eq_elim
              client_full_received
              (B.append client_prefix_received client_suffix_received);
            Seq.lemma_eq_elim server_prefix_sent
              (B.append server_head_sent server_tail_sent);
            Seq.lemma_eq_elim client_prefix_received
              (B.append client_head_received client_tail_received);
            lemma_bytes_append_assoc server_head_sent server_tail_sent server_suffix_sent;
            lemma_bytes_append_assoc client_head_received client_tail_received client_suffix_received;
            assert (Seq.equal server_full_sent
              (B.append server_head_sent
                (B.append server_tail_sent server_suffix_sent)));
            assert (Seq.equal client_full_received
              (B.append client_head_received
                (B.append client_tail_received client_suffix_received)));
            assert (Seq.equal
              (B.append server_head_sent
                (B.append server_tail_sent server_suffix_sent))
              (B.append client_head_received
                (B.append client_tail_received client_suffix_received)));
            PWS.lemma_append_heads_equal_same_len
              server_head_sent
              (B.append server_tail_sent server_suffix_sent)
              client_head_received
              (B.append client_tail_received client_suffix_received);
            assert (Seq.equal server_head_sent client_head_received);
            PWS.lemma_append_tails_equal_from_equal_heads
              server_head_sent
              (B.append server_tail_sent server_suffix_sent)
              client_head_received
              (B.append client_tail_received client_suffix_received);
            assert (Seq.equal
              (B.append server_tail_sent server_suffix_sent)
              (B.append client_tail_received client_suffix_received));
            assert (paired_replay_split_prefixes_equal_with_full_streams
              server_post
              client_post
              server_tail
              server_suffix
              client_tail
              client_suffix
              (B.append server_tail_sent server_suffix_sent)
              (B.append server_tail_received server_suffix_received)
              (B.append client_tail_sent client_suffix_sent)
              (B.append client_tail_received client_suffix_received)
              server_final
              client_final);
            assert (Seq.equal server_tail_sent client_tail_received);
            assert (Seq.equal client_tail_sent server_tail_received);
            lemma_bytes_append_equal
              server_head_sent
              client_head_received
              server_tail_sent
              client_tail_received;
            assert (Seq.equal server_prefix_sent client_prefix_received);
            lemma_bytes_append_equal
              client_head_sent
              server_head_received
              client_tail_sent
              server_tail_received;
            assert (Seq.equal client_prefix_sent server_prefix_received) ) ) )

let lemma_paired_replay_split_prefixes_equal_uniform_cleartext_handshake_prefix
  (server_model0:connection_model)
  (client_model0:connection_model)
  (start:handshake_start)
  (ch:M.client_hello)
  (selection:server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (client_shared:C.x25519_shared_secret)
  (sh:M.server_hello)
  (server_suffix:list conn_event)
  (client_suffix:list conn_event)
  (server_model1:connection_model)
  (server_model2:connection_model)
  (server_model3:connection_model)
  (server_model4:connection_model)
  (server_model5:connection_model)
  (client_model1:connection_model)
  (client_model2:connection_model)
  (client_model3:connection_model)
  (client_model4:connection_model)
  : Lemma
      (requires
        step_model
          server_model0
          (ConnLocalEvent LocalStartServer) == Some server_model1 /\
        step_model
          server_model1
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) == Some server_model2 /\
        step_model
          server_model2
          (ConnLocalEvent (LocalSelectServerParameters selection)) ==
          Some server_model3 /\
        step_model
          server_model3
          (ConnLocalEvent (LocalDeriveSharedSecret server_shared)) ==
          Some server_model4 /\
        step_model
          server_model4
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) == Some server_model5 /\
        step_model
          client_model0
          (ConnLocalEvent (LocalStartHandshake start)) ==
          Some client_model1 /\
        step_model
          client_model1
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) == Some client_model2 /\
        step_model
          client_model2
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) == Some client_model3 /\
        step_model
          client_model3
          (ConnLocalEvent (LocalDeriveSharedSecret client_shared)) ==
          Some client_model4)
      (ensures
        paired_replay_split_prefixes_equal_uniform
          server_model0
          client_model0
          (server_cleartext_handshake_prefix_events
            ch
            selection
            server_shared
            sh)
          server_suffix
          (client_cleartext_handshake_prefix_events
            start
            ch
            sh
            client_shared)
          client_suffix)
=
  let server_received_ch = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ClientHello ch);
  } in
  let server_select = ConnLocalEvent (LocalSelectServerParameters selection) in
  let server_derive = ConnLocalEvent (LocalDeriveSharedSecret server_shared) in
  let server_sent_sh = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  } in
  let client_sent_ch = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ClientHello ch);
  } in
  let client_received_sh = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  } in
  let client_derive = ConnLocalEvent (LocalDeriveSharedSecret client_shared) in
  lemma_paired_replay_split_prefixes_equal_uniform_empty
    server_model5
    client_model4
    server_suffix
    client_suffix;
  lemma_paired_replay_split_prefixes_equal_uniform_cons_client_local
    server_model5
    client_model3
    (LocalDeriveSharedSecret client_shared)
    []
    server_suffix
    []
    client_suffix
    client_model4;
  lemma_paired_replay_split_prefixes_equal_uniform_cons_server_hello
    server_model4
    client_model2
    sh
    []
    server_suffix
    [client_derive]
    client_suffix
    server_model5
    client_model3;
  lemma_paired_replay_split_prefixes_equal_uniform_cons_server_local
    server_model3
    client_model2
    (LocalDeriveSharedSecret server_shared)
    [server_sent_sh]
    server_suffix
    [client_received_sh; client_derive]
    client_suffix
    server_model4;
  lemma_paired_replay_split_prefixes_equal_uniform_cons_server_local
    server_model2
    client_model2
    (LocalSelectServerParameters selection)
    [server_derive; server_sent_sh]
    server_suffix
    [client_received_sh; client_derive]
    client_suffix
    server_model3;
  lemma_paired_replay_split_prefixes_equal_uniform_cons_client_hello
    server_model1
    client_model1
    ch
    [server_select; server_derive; server_sent_sh]
    server_suffix
    [client_received_sh; client_derive]
    client_suffix
    server_model2
    client_model2;
  lemma_paired_replay_split_prefixes_equal_uniform_cons_server_local
    server_model0
    client_model1
    LocalStartServer
    [server_received_ch; server_select; server_derive; server_sent_sh]
    server_suffix
    [client_sent_ch; client_received_sh; client_derive]
    client_suffix
    server_model1;
  lemma_paired_replay_split_prefixes_equal_uniform_cons_client_local
    server_model0
    client_model0
    (LocalStartHandshake start)
    [ConnLocalEvent LocalStartServer; server_received_ch; server_select; server_derive; server_sent_sh]
    server_suffix
    [client_sent_ch; client_received_sh; client_derive]
    client_suffix
    client_model1;
  assert (server_cleartext_handshake_prefix_events
    ch
    selection
    server_shared
    sh ==
    [ConnLocalEvent LocalStartServer; server_received_ch; server_select; server_derive; server_sent_sh]);
  assert (client_cleartext_handshake_prefix_events
    start
    ch
    sh
    client_shared ==
    [ConnLocalEvent (LocalStartHandshake start); client_sent_ch; client_received_sh; client_derive])

let lemma_same_endpoint_replay_split_prefixes_equal_uniform_server_cleartext_handshake_prefix
  (server_model0:connection_model)
  (ch:M.client_hello)
  (selection:server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (sh:M.server_hello)
  (server_suffix:list conn_event)
  (server_model1:connection_model)
  (server_model2:connection_model)
  (server_model3:connection_model)
  (server_model4:connection_model)
  (server_model5:connection_model)
  : Lemma
      (requires
        step_model
          server_model0
          (ConnLocalEvent LocalStartServer) == Some server_model1 /\
        step_model
          server_model1
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) == Some server_model2 /\
        step_model
          server_model2
          (ConnLocalEvent (LocalSelectServerParameters selection)) ==
          Some server_model3 /\
        step_model
          server_model3
          (ConnLocalEvent (LocalDeriveSharedSecret server_shared)) ==
          Some server_model4 /\
        step_model
          server_model4
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) == Some server_model5)
      (ensures
        same_endpoint_replay_split_prefixes_equal_uniform
          server_model0
          (server_cleartext_handshake_prefix_events
            ch
            selection
            server_shared
            sh)
          server_suffix)
=
  let server_received_ch = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ClientHello ch);
  } in
  let server_select = ConnLocalEvent (LocalSelectServerParameters selection) in
  let server_derive = ConnLocalEvent (LocalDeriveSharedSecret server_shared) in
  let server_sent_sh = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  } in
  lemma_same_endpoint_replay_split_prefixes_equal_uniform_empty
    server_model5
    server_suffix;
  lemma_same_endpoint_replay_split_prefixes_equal_uniform_cons_sent_cleartext
    server_model4
    (M.TlsHandshake (M.ServerHello sh))
    []
    server_suffix
    server_model5;
  lemma_same_endpoint_replay_split_prefixes_equal_uniform_cons_local
    server_model3
    (LocalDeriveSharedSecret server_shared)
    [server_sent_sh]
    server_suffix
    server_model4;
  lemma_same_endpoint_replay_split_prefixes_equal_uniform_cons_local
    server_model2
    (LocalSelectServerParameters selection)
    [server_derive; server_sent_sh]
    server_suffix
    server_model3;
  lemma_same_endpoint_replay_split_prefixes_equal_uniform_cons_received_client_hello
    server_model1
    ch
    [server_select; server_derive; server_sent_sh]
    server_suffix
    server_model2;
  lemma_same_endpoint_replay_split_prefixes_equal_uniform_cons_local
    server_model0
    LocalStartServer
    [server_received_ch; server_select; server_derive; server_sent_sh]
    server_suffix
    server_model1;
  assert (server_cleartext_handshake_prefix_events
    ch
    selection
    server_shared
    sh ==
    [ConnLocalEvent LocalStartServer; server_received_ch; server_select; server_derive; server_sent_sh])

let lemma_same_endpoint_replay_split_prefixes_equal_uniform_client_cleartext_handshake_prefix
  (client_model0:connection_model)
  (start:handshake_start)
  (ch:M.client_hello)
  (sh:M.server_hello)
  (client_shared:C.x25519_shared_secret)
  (client_suffix:list conn_event)
  (client_model1:connection_model)
  (client_model2:connection_model)
  (client_model3:connection_model)
  (client_model4:connection_model)
  : Lemma
      (requires
        step_model
          client_model0
          (ConnLocalEvent (LocalStartHandshake start)) ==
          Some client_model1 /\
        step_model
          client_model1
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) == Some client_model2 /\
        step_model
          client_model2
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) == Some client_model3 /\
        step_model
          client_model3
          (ConnLocalEvent (LocalDeriveSharedSecret client_shared)) ==
          Some client_model4)
      (ensures
        same_endpoint_replay_split_prefixes_equal_uniform
          client_model0
          (client_cleartext_handshake_prefix_events
            start
            ch
            sh
            client_shared)
          client_suffix)
=
  let client_sent_ch = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ClientHello ch);
  } in
  let client_received_sh = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  } in
  let client_derive = ConnLocalEvent (LocalDeriveSharedSecret client_shared) in
  lemma_same_endpoint_replay_split_prefixes_equal_uniform_empty
    client_model4
    client_suffix;
  lemma_same_endpoint_replay_split_prefixes_equal_uniform_cons_local
    client_model3
    (LocalDeriveSharedSecret client_shared)
    []
    client_suffix
    client_model4;
  lemma_same_endpoint_replay_split_prefixes_equal_uniform_cons_received_server_hello
    client_model2
    sh
    [client_derive]
    client_suffix
    client_model3;
  lemma_same_endpoint_replay_split_prefixes_equal_uniform_cons_sent_cleartext
    client_model1
    (M.TlsHandshake (M.ClientHello ch))
    [client_received_sh; client_derive]
    client_suffix
    client_model2;
  lemma_same_endpoint_replay_split_prefixes_equal_uniform_cons_local
    client_model0
    (LocalStartHandshake start)
    [client_sent_ch; client_received_sh; client_derive]
    client_suffix
    client_model1;
  assert (client_cleartext_handshake_prefix_events
    start
    ch
    sh
    client_shared ==
    [ConnLocalEvent (LocalStartHandshake start); client_sent_ch; client_received_sh; client_derive])

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
      PWS.lemma_append_heads_equal_same_len
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
  PWR.lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
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
  ( PWR.lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
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
      PWR.lemma_paired_replay_suffixes_equal_from_equal_prefixes
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

let lemma_paired_protected_handshake_contiguous_replay_views_from_cleartext_prefix_full_replays
  (server_model0:connection_model)
  (client_model0:connection_model)
  (start:handshake_start)
  (ch:M.client_hello)
  (selection:server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (client_shared:C.x25519_shared_secret)
  (sh:M.server_hello)
  (server_model1:connection_model)
  (server_model2:connection_model)
  (server_model3:connection_model)
  (server_model4:connection_model)
  (server_model5:connection_model)
  (client_model1:connection_model)
  (client_model2:connection_model)
  (client_model3:connection_model)
  (client_model4:connection_model)
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
        let server_prefix =
          server_cleartext_handshake_prefix_events
            ch
            selection
            server_shared
            sh in
        let client_prefix =
          client_cleartext_handshake_prefix_events
            start
            ch
            sh
            client_shared in
        Seq.equal server_full_sent client_full_received /\
        Seq.equal client_full_sent server_full_received /\
        step_model
          server_model0
          (ConnLocalEvent LocalStartServer) == Some server_model1 /\
        step_model
          server_model1
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) == Some server_model2 /\
        step_model
          server_model2
          (ConnLocalEvent (LocalSelectServerParameters selection)) ==
          Some server_model3 /\
        step_model
          server_model3
          (ConnLocalEvent (LocalDeriveSharedSecret server_shared)) ==
          Some server_model4 /\
        step_model
          server_model4
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) == Some server_model5 /\
        step_model
          client_model0
          (ConnLocalEvent (LocalStartHandshake start)) ==
          Some client_model1 /\
        step_model
          client_model1
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) == Some client_model2 /\
        step_model
          client_model2
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) == Some client_model3 /\
        step_model
          client_model3
          (ConnLocalEvent (LocalDeriveSharedSecret client_shared)) ==
          Some client_model4 /\
        conn_events_sent_seal_replay
          server_model0
          (FStar.List.Tot.append server_prefix server_suffix)
          server_full_sent
          server_full_received
          server_final /\
        conn_events_received_decode_replay
          server_model0
          (FStar.List.Tot.append server_prefix server_suffix)
          server_full_sent
          server_full_received
          server_final /\
        conn_events_sent_seal_replay
          client_model0
          (FStar.List.Tot.append client_prefix client_suffix)
          client_full_sent
          client_full_received
          client_final /\
        conn_events_received_decode_replay
          client_model0
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
  let server_prefix =
    server_cleartext_handshake_prefix_events
      ch
      selection
      server_shared
      sh in
  let client_prefix =
    client_cleartext_handshake_prefix_events
      start
      ch
      sh
      client_shared in
  lemma_same_endpoint_replay_split_prefixes_equal_uniform_server_cleartext_handshake_prefix
    server_model0
    ch
    selection
    server_shared
    sh
    server_suffix
    server_model1
    server_model2
    server_model3
    server_model4
    server_model5;
  lemma_same_endpoint_replay_split_prefixes_equal_uniform_client_cleartext_handshake_prefix
    client_model0
    start
    ch
    sh
    client_shared
    client_suffix
    client_model1
    client_model2
    client_model3
    client_model4;
  lemma_paired_replay_split_prefixes_equal_uniform_cleartext_handshake_prefix
    server_model0
    client_model0
    start
    ch
    selection
    server_shared
    client_shared
    sh
    server_suffix
    client_suffix
    server_model1
    server_model2
    server_model3
    server_model4
    server_model5
    client_model1
    client_model2
    client_model3
    client_model4;
  assert (same_endpoint_replay_split_prefixes_equal
    server_model0
    server_prefix
    server_suffix
    server_full_sent
    server_full_received
    server_final);
  assert (same_endpoint_replay_split_prefixes_equal
    client_model0
    client_prefix
    client_suffix
    client_full_sent
    client_full_received
    client_final);
  assert (paired_replay_split_prefixes_equal_with_full_streams
    server_model0
    client_model0
    server_prefix
    server_suffix
    client_prefix
    client_suffix
    server_full_sent
    server_full_received
    client_full_sent
    client_full_received
    server_final
    client_final);
  lemma_paired_replay_split_prefixes_equal_from_full_streams
    server_model0
    client_model0
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
  assert (paired_replay_split_prefixes_equal
    server_model0
    client_model0
    server_prefix
    server_suffix
    client_prefix
    client_suffix
    server_full_sent
    server_full_received
    client_full_sent
    client_full_received
    server_final
    client_final);
  lemma_paired_protected_handshake_contiguous_replay_views_from_full_replays_with_equal_prefixes
    server_model0
    client_model0
    server_prefix
    client_prefix
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
    server_full_sent
    server_full_received
    client_full_sent
    client_full_received
    server_final
    client_final
#pop-options
