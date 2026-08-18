module TLS13.ConnectionState.ProtectedWireConcreteSegmentation

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module GFin = TLS13.Wire.Generated.Finished
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWR = TLS13.ConnectionState.ProtectedWireReplay
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module Seq = FStar.Seq

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Canonical
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.KeyMaterial
open TLS13.Spec.StateMachine.Log
open TLS13.Spec.StateMachine.Replay

#push-options "--z3rlimit 10"
let lemma_paired_protected_handshake_contiguous_replay_views_from_cleartext_prefix_full_replays_known_start
  (server_model0:connection_model)
  (client_model0:connection_model)
  (start:handshake_start)
  (ch:GCH.clientHello)
  (selection:server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (client_shared:C.x25519_shared_secret)
  (sh:GSH.serverHello)
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
  (verified_server_finished:GFin.finished)
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
          PWSeg.server_cleartext_handshake_prefix_events
            ch
            selection
            server_shared
            sh in
        let client_prefix =
          PWSeg.client_cleartext_handshake_prefix_events
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
        exists server_raw_sent server_raw_received
          client_raw_sent client_raw_received.
          Seq.equal server_raw_sent client_raw_received /\
          Seq.equal client_raw_sent server_raw_received /\
          PWL.paired_protected_handshake_contiguous_replay_views
            server_model5
            client_model4
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
    PWSeg.server_cleartext_handshake_prefix_events
      ch
      selection
      server_shared
      sh in
  let client_prefix =
    PWSeg.client_cleartext_handshake_prefix_events
      start
      ch
      sh
      client_shared in
  PWSeg.lemma_same_endpoint_replay_split_prefixes_equal_uniform_server_cleartext_handshake_prefix
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
  PWSeg.lemma_same_endpoint_replay_split_prefixes_equal_uniform_client_cleartext_handshake_prefix
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
  PWSeg.lemma_paired_replay_split_prefixes_equal_uniform_cleartext_handshake_prefix
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
  assert (PWSeg.same_endpoint_replay_split_prefixes_equal
    server_model0
    server_prefix
    server_suffix
    server_full_sent
    server_full_received
    server_final);
  assert (PWSeg.same_endpoint_replay_split_prefixes_equal
    client_model0
    client_prefix
    client_suffix
    client_full_sent
    client_full_received
    client_final);
  assert (server_prefix ==
    PWSeg.server_cleartext_handshake_prefix_events
      ch
      selection
      server_shared
      sh);
  assert (client_prefix ==
    PWSeg.client_cleartext_handshake_prefix_events
      start
      ch
      sh
      client_shared);
  assert (PWSeg.paired_replay_split_prefixes_equal_uniform
    server_model0
    client_model0
    server_prefix
    server_suffix
    client_prefix
    client_suffix);
  assert (PWSeg.paired_replay_split_prefixes_equal_with_full_streams
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
  PWSeg.lemma_paired_replay_split_prefixes_equal_from_full_streams
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
  assert (PWSeg.paired_replay_split_prefixes_equal
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
  PWR.lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
    server_model0
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
      server_model0
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
      server_model0
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
  with
  ( PWSeg.lemma_conn_events_sent_seal_replay_server_cleartext_handshake_prefix_final_model
      server_model0
      ch
      selection
      server_shared
      sh
      server_model1
      server_model2
      server_model3
      server_model4
      server_model5
      server_prefix_sent
      server_prefix_received
      server_mid;
    assert (server_mid == server_model5);
    PWR.lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
      client_model0
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
        client_model0
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
        client_model0
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
    with
    ( PWSeg.lemma_conn_events_sent_seal_replay_client_cleartext_handshake_prefix_final_model
        client_model0
        start
        ch
        sh
        client_shared
        client_model1
        client_model2
        client_model3
        client_model4
        client_prefix_sent
        client_prefix_received
        client_mid;
      assert (client_mid == client_model4);
      assert (Seq.equal server_prefix_sent client_prefix_received /\
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
      assert (Seq.equal server_suffix_sent client_suffix_received);
      assert (Seq.equal client_suffix_sent server_suffix_received);
      assert (PWL.paired_protected_handshake_contiguous_replay_views
        server_model5
        client_model4
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
        server_suffix_sent
        server_suffix_received
        client_suffix_sent
        client_suffix_received
        server_final
        client_final);
      introduce exists
        (server_raw_sent:B.bytes)
        (server_raw_received:B.bytes)
        (client_raw_sent:B.bytes)
        (client_raw_received:B.bytes).
        Seq.equal server_raw_sent client_raw_received /\
        Seq.equal client_raw_sent server_raw_received /\
        PWL.paired_protected_handshake_contiguous_replay_views
          server_model5
          client_model4
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
          client_final
      with
        server_suffix_sent
        server_suffix_received
        client_suffix_sent
        client_suffix_received
      and () ) )
#pop-options

#push-options "--z3rlimit 10"
let lemma_paired_protected_handshake_contiguous_replay_views_from_cleartext_prefix_state_logs_known_start
  (server:connection_state)
  (client:connection_state)
  (start:handshake_start)
  (ch:GCH.clientHello)
  (selection:server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (client_shared:C.x25519_shared_secret)
  (sh:GSH.serverHello)
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
  (verified_server_finished:GFin.finished)
  (client_app_write_material:traffic_key_material)
  (client_app_read_material:traffic_key_material)
  (server_app_write_material:traffic_key_material)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  (client_finished_rest:list conn_event)
  (server_finished_rest:list conn_event)
  : Lemma
      (requires (
        let server_model0 = initial_model server.cs_model.model_config in
        let client_model0 = initial_model client.cs_model.model_config in
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
          PWSeg.server_cleartext_handshake_prefix_events
            ch
            selection
            server_shared
            sh in
        let client_prefix =
          PWSeg.client_cleartext_handshake_prefix_events
            start
            ch
            sh
            client_shared in
        Seq.equal
          server.cs_wire_log.CL.raw_sent
          client.cs_wire_log.CL.raw_received /\
        Seq.equal
          client.cs_wire_log.CL.raw_sent
          server.cs_wire_log.CL.raw_received /\
        server.cs_event_log ==
          FStar.List.Tot.append server_prefix server_suffix /\
        client.cs_event_log ==
          FStar.List.Tot.append client_prefix client_suffix /\
        connection_state_sent_seal_replay_consistent server /\
        connection_state_received_decode_replay_consistent server /\
        connection_state_sent_seal_replay_consistent client /\
        connection_state_received_decode_replay_consistent client /\
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
          Some client_model4))
      (ensures
        exists server_raw_sent server_raw_received
          client_raw_sent client_raw_received.
          Seq.equal server_raw_sent client_raw_received /\
          Seq.equal client_raw_sent server_raw_received /\
          PWL.paired_protected_handshake_contiguous_replay_views
            server_model5
            client_model4
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
            server.cs_model
            client.cs_model)
=
  let server_model0 = initial_model server.cs_model.model_config in
  let client_model0 = initial_model client.cs_model.model_config in
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
    PWSeg.server_cleartext_handshake_prefix_events
      ch
      selection
      server_shared
      sh in
  let client_prefix =
    PWSeg.client_cleartext_handshake_prefix_events
      start
      ch
      sh
      client_shared in
  assert (conn_events_sent_seal_replay
    server_model0
    (FStar.List.Tot.append server_prefix server_suffix)
    server.cs_wire_log.CL.raw_sent
    server.cs_wire_log.CL.raw_received
    server.cs_model);
  assert (conn_events_received_decode_replay
    server_model0
    (FStar.List.Tot.append server_prefix server_suffix)
    server.cs_wire_log.CL.raw_sent
    server.cs_wire_log.CL.raw_received
    server.cs_model);
  assert (conn_events_sent_seal_replay
    client_model0
    (FStar.List.Tot.append client_prefix client_suffix)
    client.cs_wire_log.CL.raw_sent
    client.cs_wire_log.CL.raw_received
    client.cs_model);
  assert (conn_events_received_decode_replay
    client_model0
    (FStar.List.Tot.append client_prefix client_suffix)
    client.cs_wire_log.CL.raw_sent
    client.cs_wire_log.CL.raw_received
    client.cs_model);
  lemma_paired_protected_handshake_contiguous_replay_views_from_cleartext_prefix_full_replays_known_start
    server_model0
    client_model0
    start
    ch
    selection
    server_shared
    client_shared
    sh
    server_model1
    server_model2
    server_model3
    server_model4
    server_model5
    client_model1
    client_model2
    client_model3
    client_model4
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
    server.cs_wire_log.CL.raw_sent
    server.cs_wire_log.CL.raw_received
    client.cs_wire_log.CL.raw_sent
    client.cs_wire_log.CL.raw_received
    server.cs_model
    client.cs_model
#pop-options
