module TLS13.ConnectionState.ProtectedWireSegmentation

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module Seq = FStar.Seq

noextract
let same_endpoint_replay_split_prefixes_equal
  (model:CS.connection_model)
  (prefix:list CS.conn_event)
  (suffix:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : prop =
  forall
    (sent_mid:CS.connection_model)
    (received_mid:CS.connection_model)
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
      final_model ==>
    Seq.equal sent_prefix_sent received_prefix_sent /\
    Seq.equal sent_prefix_received received_prefix_received

noextract
let paired_replay_split_prefixes_equal
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (server_prefix:list CS.conn_event)
  (server_suffix:list CS.conn_event)
  (client_prefix:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : prop =
  forall
    (server_mid:CS.connection_model)
    (client_mid:CS.connection_model)
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
    CS.conn_events_sent_seal_replay
      server_model
      server_prefix
      server_prefix_sent
      server_prefix_received
      server_mid /\
    CS.conn_events_sent_seal_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    CS.conn_events_received_decode_replay
      server_model
      server_prefix
      server_prefix_sent
      server_prefix_received
      server_mid /\
    CS.conn_events_received_decode_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    CS.conn_events_sent_seal_replay
      client_model
      client_prefix
      client_prefix_sent
      client_prefix_received
      client_mid /\
    CS.conn_events_sent_seal_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final /\
    CS.conn_events_received_decode_replay
      client_model
      client_prefix
      client_prefix_sent
      client_prefix_received
      client_mid /\
    CS.conn_events_received_decode_replay
      client_mid
      client_suffix
      client_suffix_sent
      client_suffix_received
      client_final ==>
    Seq.equal server_prefix_sent client_prefix_received /\
    Seq.equal client_prefix_sent server_prefix_received

val lemma_paired_replay_suffix_views_from_full_replays_with_equal_prefixes
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (server_prefix:list CS.conn_event)
  (server_suffix:list CS.conn_event)
  (client_prefix:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
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
        CS.conn_events_sent_seal_replay
          server_model
          (FStar.List.Tot.append server_prefix server_suffix)
          server_full_sent
          server_full_received
          server_final /\
        CS.conn_events_received_decode_replay
          server_model
          (FStar.List.Tot.append server_prefix server_suffix)
          server_full_sent
          server_full_received
          server_final /\
        CS.conn_events_sent_seal_replay
          client_model
          (FStar.List.Tot.append client_prefix client_suffix)
          client_full_sent
          client_full_received
          client_final /\
        CS.conn_events_received_decode_replay
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
          CS.conn_events_sent_seal_replay
            server_mid
            server_suffix
            server_suffix_sent
            server_suffix_received
            server_final /\
          CS.conn_events_received_decode_replay
            server_mid
            server_suffix
            server_suffix_sent
            server_suffix_received
            server_final /\
          CS.conn_events_sent_seal_replay
            client_mid
            client_suffix
            client_suffix_sent
            client_suffix_received
            client_final /\
          CS.conn_events_received_decode_replay
            client_mid
            client_suffix
            client_suffix_sent
            client_suffix_received
            client_final)
