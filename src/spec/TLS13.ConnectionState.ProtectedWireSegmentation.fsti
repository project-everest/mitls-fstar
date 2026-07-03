module TLS13.ConnectionState.ProtectedWireSegmentation

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PWL = TLS13.ConnectionState.ProtectedWireLemmas
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

noextract
let paired_replay_split_prefixes_equal_with_full_streams
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

noextract
let paired_replay_split_prefixes_equal_uniform
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (server_prefix:list CS.conn_event)
  (server_suffix:list CS.conn_event)
  (client_prefix:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  : prop =
  forall
    (server_full_sent:B.bytes)
    (server_full_received:B.bytes)
    (client_full_sent:B.bytes)
    (client_full_received:B.bytes)
    (server_final:CS.connection_model)
    (client_final:CS.connection_model).
    Seq.equal server_full_sent client_full_received /\
    Seq.equal client_full_sent server_full_received ==>
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
      client_final

noextract
let server_cleartext_handshake_prefix_events
  (ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (sh:M.server_hello)
  : list CS.conn_event =
  [
    CS.ConnLocalEvent CS.LocalStartServer;
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    };
    CS.ConnLocalEvent (CS.LocalSelectServerParameters selection);
    CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared);
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    };
  ]

noextract
let client_cleartext_handshake_prefix_events
  (start:CS.handshake_start)
  (ch:M.client_hello)
  (sh:M.server_hello)
  (client_shared:C.x25519_shared_secret)
  : list CS.conn_event =
  [
    CS.ConnLocalEvent (CS.LocalStartHandshake start);
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    };
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    };
    CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared);
  ]

val lemma_paired_replay_split_prefixes_equal_from_full_streams
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

val lemma_paired_replay_split_prefixes_equal_with_full_streams_from_plain
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

val lemma_paired_replay_split_prefixes_equal_uniform_empty
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (server_suffix:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  : Lemma
      (paired_replay_split_prefixes_equal_uniform
        server_model
        client_model
        []
        server_suffix
        []
        client_suffix)

val lemma_same_endpoint_replay_split_prefixes_equal_empty
  (model:CS.connection_model)
  (suffix:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (same_endpoint_replay_split_prefixes_equal
        model
        []
        suffix
        raw_sent
        raw_received
        final_model)

val lemma_same_endpoint_replay_split_prefixes_equal_single_local
  (model:CS.connection_model)
  (ev:CS.local_event)
  (suffix:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (same_endpoint_replay_split_prefixes_equal
        model
        [CS.ConnLocalEvent ev]
        suffix
        raw_sent
        raw_received
        final_model)

val lemma_same_endpoint_replay_split_prefixes_equal_cons_local
  (model:CS.connection_model)
  (ev:CS.local_event)
  (tail:list CS.conn_event)
  (suffix:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  (post_model:CS.connection_model)
  : Lemma
      (requires
        CS.step_model model (CS.ConnLocalEvent ev) == Some post_model /\
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
          (CS.ConnLocalEvent ev :: tail)
          suffix
          raw_sent
          raw_received
          final_model)

val lemma_same_endpoint_replay_split_prefixes_equal_single_sent_cleartext
  (model:CS.connection_model)
  (msg:M.tls_message)
  (suffix:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.network_message_is_cleartext CL.Sent msg == true)
      (ensures
        same_endpoint_replay_split_prefixes_equal
          model
          [CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          }]
          suffix
          raw_sent
          raw_received
          final_model)

val lemma_same_endpoint_replay_split_prefixes_equal_single_received_server_hello
  (model:CS.connection_model)
  (sh:M.server_hello)
  (suffix:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (same_endpoint_replay_split_prefixes_equal
        model
        [CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ServerHello sh);
        }]
        suffix
        raw_sent
        raw_received
        final_model)

val lemma_same_endpoint_replay_split_prefixes_equal_single_received_client_hello
  (model:CS.connection_model)
  (ch:M.client_hello)
  (suffix:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (same_endpoint_replay_split_prefixes_equal
        model
        [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }]
        suffix
        raw_sent
        raw_received
        final_model)

val lemma_paired_replay_split_prefixes_equal_empty
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (server_suffix:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
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

val lemma_paired_replay_split_prefixes_equal_single_local
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (server_ev:CS.local_event)
  (client_ev:CS.local_event)
  (server_suffix:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (paired_replay_split_prefixes_equal
        server_model
        client_model
        [CS.ConnLocalEvent server_ev]
        server_suffix
        [CS.ConnLocalEvent client_ev]
        client_suffix
        server_full_sent
        server_full_received
        client_full_sent
        client_full_received
        server_final
        client_final)

val lemma_paired_replay_split_prefixes_equal_with_full_streams_cons_server_local
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (server_ev:CS.local_event)
  (server_tail:list CS.conn_event)
  (server_suffix:list CS.conn_event)
  (client_prefix:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  (server_post:CS.connection_model)
  : Lemma
      (requires
        CS.step_model server_model (CS.ConnLocalEvent server_ev) ==
          Some server_post /\
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
          (CS.ConnLocalEvent server_ev :: server_tail)
          server_suffix
          client_prefix
          client_suffix
          server_full_sent
          server_full_received
          client_full_sent
          client_full_received
          server_final
          client_final)

val lemma_paired_replay_split_prefixes_equal_uniform_cons_client_hello
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (ch:M.client_hello)
  (server_tail:list CS.conn_event)
  (server_suffix:list CS.conn_event)
  (client_tail:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  (server_post:CS.connection_model)
  (client_post:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          server_model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) == Some server_post /\
        CS.step_model
          client_model
          (CS.ConnNetworkEvent {
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
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          } :: server_tail)
          server_suffix
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          } :: client_tail)
          client_suffix)

val lemma_paired_replay_split_prefixes_equal_with_full_streams_cons_client_local
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (client_ev:CS.local_event)
  (server_prefix:list CS.conn_event)
  (server_suffix:list CS.conn_event)
  (client_tail:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  (client_post:CS.connection_model)
  : Lemma
      (requires
        CS.step_model client_model (CS.ConnLocalEvent client_ev) ==
          Some client_post /\
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
          (CS.ConnLocalEvent client_ev :: client_tail)
          client_suffix
          server_full_sent
          server_full_received
          client_full_sent
          client_full_received
          server_final
          client_final)

val lemma_paired_replay_split_prefixes_equal_uniform_cons_server_local
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (server_ev:CS.local_event)
  (server_tail:list CS.conn_event)
  (server_suffix:list CS.conn_event)
  (client_prefix:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  (server_post:CS.connection_model)
  : Lemma
      (requires
        CS.step_model server_model (CS.ConnLocalEvent server_ev) ==
          Some server_post /\
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
          (CS.ConnLocalEvent server_ev :: server_tail)
          server_suffix
          client_prefix
          client_suffix)

val lemma_paired_replay_split_prefixes_equal_uniform_cons_client_local
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (client_ev:CS.local_event)
  (server_prefix:list CS.conn_event)
  (server_suffix:list CS.conn_event)
  (client_tail:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  (client_post:CS.connection_model)
  : Lemma
      (requires
        CS.step_model client_model (CS.ConnLocalEvent client_ev) ==
          Some client_post /\
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
          (CS.ConnLocalEvent client_ev :: client_tail)
          client_suffix)

val lemma_paired_replay_split_prefixes_equal_uniform_cons_server_hello
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (sh:M.server_hello)
  (server_tail:list CS.conn_event)
  (server_suffix:list CS.conn_event)
  (client_tail:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  (server_post:CS.connection_model)
  (client_post:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          server_model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) == Some server_post /\
        CS.step_model
          client_model
          (CS.ConnNetworkEvent {
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
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          } :: server_tail)
          server_suffix
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          } :: client_tail)
          client_suffix)

val lemma_paired_replay_split_prefixes_equal_uniform_cleartext_handshake_prefix
  (server_model0:CS.connection_model)
  (client_model0:CS.connection_model)
  (start:CS.handshake_start)
  (ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (client_shared:C.x25519_shared_secret)
  (sh:M.server_hello)
  (server_suffix:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  (server_model1:CS.connection_model)
  (server_model2:CS.connection_model)
  (server_model3:CS.connection_model)
  (server_model4:CS.connection_model)
  (server_model5:CS.connection_model)
  (client_model1:CS.connection_model)
  (client_model2:CS.connection_model)
  (client_model3:CS.connection_model)
  (client_model4:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          server_model0
          (CS.ConnLocalEvent CS.LocalStartServer) == Some server_model1 /\
        CS.step_model
          server_model1
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) == Some server_model2 /\
        CS.step_model
          server_model2
          (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
          Some server_model3 /\
        CS.step_model
          server_model3
          (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared)) ==
          Some server_model4 /\
        CS.step_model
          server_model4
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) == Some server_model5 /\
        CS.step_model
          client_model0
          (CS.ConnLocalEvent (CS.LocalStartHandshake start)) ==
          Some client_model1 /\
        CS.step_model
          client_model1
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) == Some client_model2 /\
        CS.step_model
          client_model2
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) == Some client_model3 /\
        CS.step_model
          client_model3
          (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared)) ==
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

val lemma_paired_replay_split_prefixes_equal_single_server_hello
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (sh:M.server_hello)
  (server_suffix:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (paired_replay_split_prefixes_equal
        server_model
        client_model
        [CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ServerHello sh);
        }]
        server_suffix
        [CS.ConnNetworkEvent {
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

val lemma_paired_replay_split_prefixes_equal_single_client_hello_with_full_streams
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (ch:M.client_hello)
  (server_suffix:list CS.conn_event)
  (client_suffix:list CS.conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (paired_replay_split_prefixes_equal_with_full_streams
        server_model
        client_model
        [CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }]
        server_suffix
        [CS.ConnNetworkEvent {
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

val lemma_paired_replay_split_prefixes_equal_single_client_hello
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (ch:M.client_hello)
  (server_suffix:list CS.conn_event)
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
        Seq.equal client_full_sent server_full_received)
      (ensures
        paired_replay_split_prefixes_equal
        server_model
        client_model
        [CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }]
        server_suffix
        [CS.ConnNetworkEvent {
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

val lemma_paired_protected_handshake_contiguous_replay_views_from_full_replays_with_equal_prefixes
  (server_model:CS.connection_model)
  (client_model:CS.connection_model)
  (server_prefix:list CS.conn_event)
  (client_prefix:list CS.conn_event)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (server_auth_skip:CS.local_event)
  (client_auth_skip:CS.local_event)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (client_verify_skip:CS.local_event)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (verified_server_finished:M.finished)
  (client_app_write_material:CS.traffic_key_material)
  (client_app_read_material:CS.traffic_key_material)
  (server_app_write_material:CS.traffic_key_material)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  (client_finished_rest:list CS.conn_event)
  (server_finished_rest:list CS.conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
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
