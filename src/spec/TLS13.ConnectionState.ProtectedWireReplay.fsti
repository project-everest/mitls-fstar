module TLS13.ConnectionState.ProtectedWireReplay

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

open TLS13.ConnectionState.ProtectedWireBase

val lemma_conn_events_raw_replay_head
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

val lemma_conn_events_sent_seal_replay_head
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay
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
          CS.sent_event_nonempty_seal_projection model ev delta_sent /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          CS.conn_events_sent_seal_replay
            model1
            rest
            tail_sent
            tail_received
            final_model)

val lemma_conn_events_received_decode_replay_head
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_received_decode_replay
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
          CS.received_event_nonempty_decode_projection model ev delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          CS.conn_events_received_decode_replay
            model1
            rest
            tail_sent
            tail_received
            final_model)

val lemma_conn_events_sent_received_replays_same_events_final_model_equal
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (sent_raw_sent:B.bytes)
  (sent_raw_received:B.bytes)
  (sent_final:CS.connection_model)
  (received_raw_sent:B.bytes)
  (received_raw_received:B.bytes)
  (received_final:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay
          model
          events
          sent_raw_sent
          sent_raw_received
          sent_final /\
        CS.conn_events_received_decode_replay
          model
          events
          received_raw_sent
          received_raw_received
          received_final)
      (ensures sent_final == received_final)

val lemma_conn_events_raw_sent_seal_replays_same_events_final_model_equal
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_replay_sent:B.bytes)
  (raw_replay_received:B.bytes)
  (raw_final:CS.connection_model)
  (sent_raw_sent:B.bytes)
  (sent_raw_received:B.bytes)
  (sent_final:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model
          events
          raw_replay_sent
          raw_replay_received
          raw_final /\
        CS.conn_events_sent_seal_replay
          model
          events
          sent_raw_sent
          sent_raw_received
          sent_final)
      (ensures raw_final == sent_final)

val lemma_conn_events_raw_received_decode_replays_same_events_final_model_equal
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_replay_sent:B.bytes)
  (raw_replay_received:B.bytes)
  (raw_final:CS.connection_model)
  (received_raw_sent:B.bytes)
  (received_raw_received:B.bytes)
  (received_final:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model
          events
          raw_replay_sent
          raw_replay_received
          raw_final /\
        CS.conn_events_received_decode_replay
          model
          events
          received_raw_sent
          received_raw_received
          received_final)
      (ensures raw_final == received_final)

val lemma_conn_events_raw_replay_append_split
  (model:CS.connection_model)
  (prefix:list CS.conn_event)
  (suffix:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model
          (FStar.List.Tot.append prefix suffix)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists mid prefix_sent prefix_received suffix_sent suffix_received.
          Seq.equal raw_sent (B.append prefix_sent suffix_sent) /\
          Seq.equal raw_received (B.append prefix_received suffix_received) /\
          CS.conn_events_raw_replay
            model
            prefix
            prefix_sent
            prefix_received
            mid /\
          CS.conn_events_raw_replay
            mid
            suffix
            suffix_sent
            suffix_received
            final_model)

val lemma_conn_events_sent_seal_replay_append_split
  (model:CS.connection_model)
  (prefix:list CS.conn_event)
  (suffix:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay
          model
          (FStar.List.Tot.append prefix suffix)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists mid prefix_sent prefix_received suffix_sent suffix_received.
          Seq.equal raw_sent (B.append prefix_sent suffix_sent) /\
          Seq.equal raw_received (B.append prefix_received suffix_received) /\
          CS.conn_events_sent_seal_replay
            model
            prefix
            prefix_sent
            prefix_received
            mid /\
          CS.conn_events_sent_seal_replay
            mid
            suffix
            suffix_sent
            suffix_received
            final_model)

val lemma_conn_events_received_decode_replay_append_split
  (model:CS.connection_model)
  (prefix:list CS.conn_event)
  (suffix:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_received_decode_replay
          model
          (FStar.List.Tot.append prefix suffix)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists mid prefix_sent prefix_received suffix_sent suffix_received.
          Seq.equal raw_sent (B.append prefix_sent suffix_sent) /\
          Seq.equal raw_received (B.append prefix_received suffix_received) /\
          CS.conn_events_received_decode_replay
            model
            prefix
            prefix_sent
            prefix_received
            mid /\
          CS.conn_events_received_decode_replay
            mid
            suffix
            suffix_sent
            suffix_received
            final_model)

val lemma_sent_received_replay_append_split_equal_tails
  (sender_model:CS.connection_model)
  (receiver_model:CS.connection_model)
  (sender_prefix:list CS.conn_event)
  (sender_suffix:list CS.conn_event)
  (receiver_prefix:list CS.conn_event)
  (receiver_suffix:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay
          sender_model
          (FStar.List.Tot.append sender_prefix sender_suffix)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver_model
          (FStar.List.Tot.append receiver_prefix receiver_suffix)
          receiver_raw_sent
          receiver_raw_received
          receiver_final /\
        Seq.equal sender_raw_sent receiver_raw_received)
      (ensures
        exists sender_mid receiver_mid
          sender_prefix_sent sender_prefix_received
          sender_suffix_sent sender_suffix_received
          receiver_prefix_sent receiver_prefix_received
          receiver_suffix_sent receiver_suffix_received.
          Seq.equal
            sender_raw_sent
            (B.append sender_prefix_sent sender_suffix_sent) /\
          Seq.equal
            sender_raw_received
            (B.append sender_prefix_received sender_suffix_received) /\
          Seq.equal
            receiver_raw_sent
            (B.append receiver_prefix_sent receiver_suffix_sent) /\
          Seq.equal
            receiver_raw_received
            (B.append receiver_prefix_received receiver_suffix_received) /\
          CS.conn_events_sent_seal_replay
            sender_model
            sender_prefix
            sender_prefix_sent
            sender_prefix_received
            sender_mid /\
          CS.conn_events_sent_seal_replay
            sender_mid
            sender_suffix
            sender_suffix_sent
            sender_suffix_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_model
            receiver_prefix
            receiver_prefix_sent
            receiver_prefix_received
            receiver_mid /\
          CS.conn_events_received_decode_replay
            receiver_mid
            receiver_suffix
            receiver_suffix_sent
            receiver_suffix_received
            receiver_final /\
          (Seq.length sender_prefix_sent ==
             Seq.length receiver_prefix_received ==>
           Seq.equal sender_suffix_sent receiver_suffix_received))

noextract
let sent_received_replay_split_prefix_lengths_aligned
  (sender_model:CS.connection_model)
  (receiver_model:CS.connection_model)
  (sender_prefix:list CS.conn_event)
  (sender_suffix:list CS.conn_event)
  (receiver_prefix:list CS.conn_event)
  (receiver_suffix:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : prop =
  forall (sender_mid:CS.connection_model)
    (receiver_mid:CS.connection_model)
    (sender_prefix_sent:B.bytes)
    (sender_prefix_received:B.bytes)
    (sender_suffix_sent:B.bytes)
    (sender_suffix_received:B.bytes)
    (receiver_prefix_sent:B.bytes)
    (receiver_prefix_received:B.bytes)
    (receiver_suffix_sent:B.bytes)
    (receiver_suffix_received:B.bytes).
    Seq.equal
      sender_raw_sent
      (B.append sender_prefix_sent sender_suffix_sent) /\
    Seq.equal
      sender_raw_received
      (B.append sender_prefix_received sender_suffix_received) /\
    Seq.equal
      receiver_raw_sent
      (B.append receiver_prefix_sent receiver_suffix_sent) /\
    Seq.equal
      receiver_raw_received
      (B.append receiver_prefix_received receiver_suffix_received) /\
    CS.conn_events_sent_seal_replay
      sender_model
      sender_prefix
      sender_prefix_sent
      sender_prefix_received
      sender_mid /\
    CS.conn_events_sent_seal_replay
      sender_mid
      sender_suffix
      sender_suffix_sent
      sender_suffix_received
      sender_final /\
    CS.conn_events_received_decode_replay
      receiver_model
      receiver_prefix
      receiver_prefix_sent
      receiver_prefix_received
      receiver_mid /\
    CS.conn_events_received_decode_replay
      receiver_mid
      receiver_suffix
      receiver_suffix_sent
      receiver_suffix_received
      receiver_final ==>
    Seq.length sender_prefix_sent == Seq.length receiver_prefix_received

val lemma_sent_received_replay_append_split_equal_tails_from_aligned_prefixes
  (sender_model:CS.connection_model)
  (receiver_model:CS.connection_model)
  (sender_prefix:list CS.conn_event)
  (sender_suffix:list CS.conn_event)
  (receiver_prefix:list CS.conn_event)
  (receiver_suffix:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  (prefix_lengths_aligned:
    (sender_mid:CS.connection_model) ->
    (receiver_mid:CS.connection_model) ->
    (sender_prefix_sent:B.bytes) ->
    (sender_prefix_received:B.bytes) ->
    (sender_suffix_sent:B.bytes) ->
    (sender_suffix_received:B.bytes) ->
    (receiver_prefix_sent:B.bytes) ->
    (receiver_prefix_received:B.bytes) ->
    (receiver_suffix_sent:B.bytes) ->
    (receiver_suffix_received:B.bytes) ->
    Lemma
      (requires
        Seq.equal
          sender_raw_sent
          (B.append sender_prefix_sent sender_suffix_sent) /\
        Seq.equal
          sender_raw_received
          (B.append sender_prefix_received sender_suffix_received) /\
        Seq.equal
          receiver_raw_sent
          (B.append receiver_prefix_sent receiver_suffix_sent) /\
        Seq.equal
          receiver_raw_received
          (B.append receiver_prefix_received receiver_suffix_received) /\
        CS.conn_events_sent_seal_replay
          sender_model
          sender_prefix
          sender_prefix_sent
          sender_prefix_received
          sender_mid /\
        CS.conn_events_sent_seal_replay
          sender_mid
          sender_suffix
          sender_suffix_sent
          sender_suffix_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver_model
          receiver_prefix
          receiver_prefix_sent
          receiver_prefix_received
          receiver_mid /\
        CS.conn_events_received_decode_replay
          receiver_mid
          receiver_suffix
          receiver_suffix_sent
          receiver_suffix_received
          receiver_final)
      (ensures
        Seq.length sender_prefix_sent == Seq.length receiver_prefix_received))
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay
          sender_model
          (FStar.List.Tot.append sender_prefix sender_suffix)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver_model
          (FStar.List.Tot.append receiver_prefix receiver_suffix)
          receiver_raw_sent
          receiver_raw_received
          receiver_final /\
        Seq.equal sender_raw_sent receiver_raw_received)
      (ensures
        exists sender_mid receiver_mid
          sender_prefix_sent sender_prefix_received
          sender_suffix_sent sender_suffix_received
          receiver_prefix_sent receiver_prefix_received
          receiver_suffix_sent receiver_suffix_received.
          Seq.equal
            sender_raw_sent
            (B.append sender_prefix_sent sender_suffix_sent) /\
          Seq.equal
            sender_raw_received
            (B.append sender_prefix_received sender_suffix_received) /\
          Seq.equal
            receiver_raw_sent
            (B.append receiver_prefix_sent receiver_suffix_sent) /\
          Seq.equal
            receiver_raw_received
            (B.append receiver_prefix_received receiver_suffix_received) /\
          CS.conn_events_sent_seal_replay
            sender_model
            sender_prefix
            sender_prefix_sent
            sender_prefix_received
            sender_mid /\
          CS.conn_events_sent_seal_replay
            sender_mid
            sender_suffix
            sender_suffix_sent
            sender_suffix_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_model
            receiver_prefix
            receiver_prefix_sent
            receiver_prefix_received
            receiver_mid /\
          CS.conn_events_received_decode_replay
            receiver_mid
            receiver_suffix
            receiver_suffix_sent
            receiver_suffix_received
            receiver_final /\
          Seq.equal sender_suffix_sent receiver_suffix_received)

val lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
  (model:CS.connection_model)
  (prefix:list CS.conn_event)
  (suffix:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  (prefixes_equal:
    (sent_mid:CS.connection_model) ->
    (received_mid:CS.connection_model) ->
    (sent_prefix_sent:B.bytes) ->
    (sent_prefix_received:B.bytes) ->
    (sent_suffix_sent:B.bytes) ->
    (sent_suffix_received:B.bytes) ->
    (received_prefix_sent:B.bytes) ->
    (received_prefix_received:B.bytes) ->
    (received_suffix_sent:B.bytes) ->
    (received_suffix_received:B.bytes) ->
    Lemma
      (requires
        Seq.equal raw_sent (B.append sent_prefix_sent sent_suffix_sent) /\
        Seq.equal raw_received
            (B.append sent_prefix_received sent_suffix_received) /\
        Seq.equal raw_sent
            (B.append received_prefix_sent received_suffix_sent) /\
        Seq.equal raw_received
            (B.append received_prefix_received received_suffix_received) /\
        CS.conn_events_sent_seal_replay
            model
            prefix
            sent_prefix_sent
            sent_prefix_received
            sent_mid /\
        CS.conn_events_sent_seal_replay
            sent_mid
            suffix
            sent_suffix_sent
            sent_suffix_received
            final_model /\
        CS.conn_events_received_decode_replay
            model
            prefix
            received_prefix_sent
            received_prefix_received
            received_mid /\
        CS.conn_events_received_decode_replay
            received_mid
            suffix
            received_suffix_sent
            received_suffix_received
            final_model)
      (ensures
        Seq.equal sent_prefix_sent received_prefix_sent /\
        Seq.equal sent_prefix_received received_prefix_received))
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay
            model
            (FStar.List.Tot.append prefix suffix)
            raw_sent
            raw_received
            final_model /\
        CS.conn_events_received_decode_replay
            model
            (FStar.List.Tot.append prefix suffix)
            raw_sent
            raw_received
            final_model)
      (ensures
        exists mid prefix_sent prefix_received suffix_sent suffix_received.
            Seq.equal raw_sent (B.append prefix_sent suffix_sent) /\
            Seq.equal raw_received (B.append prefix_received suffix_received) /\
            CS.conn_events_sent_seal_replay
              model
              prefix
              prefix_sent
              prefix_received
              mid /\
            CS.conn_events_sent_seal_replay
              mid
              suffix
              suffix_sent
              suffix_received
              final_model /\
            CS.conn_events_received_decode_replay
              model
              prefix
              prefix_sent
              prefix_received
              mid /\
            CS.conn_events_received_decode_replay
              mid
              suffix
              suffix_sent
              suffix_received
              final_model)

val lemma_paired_replay_suffixes_equal_from_equal_prefixes:
  server_full_sent:B.bytes ->
  server_full_received:B.bytes ->
  client_full_sent:B.bytes ->
  client_full_received:B.bytes ->
  server_prefix_sent:B.bytes ->
  server_prefix_received:B.bytes ->
  server_suffix_sent:B.bytes ->
  server_suffix_received:B.bytes ->
  client_prefix_sent:B.bytes ->
  client_prefix_received:B.bytes ->
  client_suffix_sent:B.bytes ->
  client_suffix_received:B.bytes ->
  Lemma
    (requires
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
      Seq.equal server_prefix_sent client_prefix_received /\
      Seq.equal client_prefix_sent server_prefix_received)
    (ensures
      Seq.equal server_suffix_sent client_suffix_received /\
      Seq.equal client_suffix_sent server_suffix_received)
