module TLS13.ConnectionState.ProtectedWireSegmentation

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PWL = TLS13.ConnectionState.ProtectedWireLemmas
module Seq = FStar.Seq

open TLS13.Spec.ConnectionState

#push-options "--split_queries always --z3rlimit 10"
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
