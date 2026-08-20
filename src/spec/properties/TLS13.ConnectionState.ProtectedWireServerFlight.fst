module TLS13.ConnectionState.ProtectedWireServerFlight

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CSL = TLS13.ConnectionState.Lemmas
module K = TLS13.Keys
module M = TLS13.Messages
module R = TLS13.Record.Spec
module RD = TLS13.Wire.Spec.RevealDecode
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties
module T = TLS13.Types
module Tr = TLS13.Transcript
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas
module WRT = TLS13.Wire.Spec.Reveal.FinishedRoundTrip
module WU = TLS13.Wire.Spec.Reveal.Util

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Canonical
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.KeyMaterial
open TLS13.Spec.StateMachine.Log
open TLS13.Spec.StateMachine.Replay
open TLS13.ConnectionState.ProtectedWireBase
open TLS13.ConnectionState.ProtectedWireStream
open TLS13.ConnectionState.ProtectedWireReplay
open TLS13.ConnectionState.ProtectedWireRecordAlignment
open TLS13.ConnectionState.ProtectedWireHead

#push-options "--z3rlimit 20"
let lemma_single_message_sender_after_server_write_client_read_install_normalizes_received_head
  (server:connection_model)
  (client:connection_model)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (client_head:conn_event)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        (match
          server.model_handshake.hs_keys.ks_handshake_secret,
          client.model_handshake.hs_keys.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.model_handshake.hs_transcript
          client.model_handshake.hs_transcript /\
        negotiated_aead_alg server.model_handshake ==
          negotiated_aead_alg client.model_handshake /\
        protected_handshake_buffer_empty client /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        (match client_head with
         | ConnNetworkEvent directed ->
           directed.CL.message_direction == CL.Received /\
           directed.CL.message_value == M.TlsHandshake received_msg
         | ConnProtectedHandshake step ->
           (* A BUFFERING step delivers no message and its
              [protected_handshake_message] field is inert, so a caller
              reasoning about the client step that DELIVERS [received_msg]
              must say the step is not a buffering one.  Buffering steps are
              skipped, not paired, by the flight inversion. *)
           step.protected_handshake_buffering == false /\
           step.protected_handshake_message == received_msg
         (* Cleartext reassembly is a SERVER-side event; [client_head] is a
            client event, so this shape never arises here. *)
         | ConnCleartextHandshake _ ->
           False
         | ConnLocalEvent _ ->
           False) /\
        conn_events_sent_seal_replay
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = server_material;
              };
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        conn_events_received_decode_replay
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            }) :: client_head :: client_rest)
          client_raw_sent
          client_raw_received
          client_final)
      (ensures
        TLS13.ConnectionState.ProtectedWireHead.received_handshake_head_normal_form
          received_msg client_head /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final)
=
  let server_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeysForRole {
        install_role = ServerEndpoint;
        install_payload = {
          install_epoch = TrafficHandshake;
          install_direction = TrafficWrite;
          install_material = server_material;
        };
      }) in
  let client_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeys {
        install_epoch = TrafficHandshake;
        install_direction = TrafficRead;
        install_material = client_material;
      }) in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    server
    server_install_ev
    (sent_ev :: server_rest)
    server_raw_sent
    server_raw_received
    client_raw_received
    server_final;
  eliminate exists
    (server_after:connection_model)
    (server_sent_after_install:B.bytes)
    (server_received_after_install:B.bytes).
    legal_event server server_install_ev /\
    step_model server server_install_ev == Some server_after /\
    Seq.equal server_sent_after_install client_raw_received /\
    conn_events_sent_seal_replay
      server_after
      (sent_ev :: server_rest)
      server_sent_after_install
      server_received_after_install
      server_final
  with
  ( lemma_received_replay_skip_empty_head_preserves_peer_stream
      server_sent_after_install
      client
      client_install_ev
      (client_head :: client_rest)
      client_raw_sent
      client_raw_received
      client_final;
    eliminate exists
      (client_after:connection_model)
      (client_sent_after_install:B.bytes)
      (client_received_after_install:B.bytes).
      legal_event client client_install_ev /\
      step_model client client_install_ev == Some client_after /\
      Seq.equal server_sent_after_install client_received_after_install /\
      conn_events_received_decode_replay
        client_after
        (client_head :: client_rest)
        client_sent_after_install
        client_received_after_install
        client_final
    with
    ( assert (legal_local_event server
        (LocalInstallTrafficKeysForRole {
          install_role = ServerEndpoint;
          install_payload = {
            install_epoch = TrafficHandshake;
            install_direction = TrafficWrite;
            install_material = server_material;
          };
        }));
      assert (legal_local_event client
        (LocalInstallTrafficKeys {
          install_epoch = TrafficHandshake;
          install_direction = TrafficRead;
          install_material = client_material;
        }));
      assert (traffic_install_matches_key_schedule_for_role
        ServerEndpoint
        server.model_handshake
        {
          install_epoch = TrafficHandshake;
          install_direction = TrafficWrite;
          install_material = server_material;
        });
      assert (traffic_install_matches_key_schedule
        client.model_handshake
        {
          install_epoch = TrafficHandshake;
          install_direction = TrafficRead;
          install_material = client_material;
        });
      lemma_server_handshake_write_client_handshake_read_install_aligned_from_key_schedule
        server
        client
        server_material
        client_material
        server_after
        client_after;
      assert (protected_handshake_buffer_empty client_after);
      lemma_single_message_sender_normalizes_received_handshake_head
        server_after
        client_after
        sent_msg
        received_msg
        client_head
        server_rest
        client_rest
        server_sent_after_install
        server_received_after_install
        client_sent_after_install
        client_received_after_install
        server_final
        client_final;
      (* [client_head] is now known to be in normal form: either the network
         event itself, or a saturating head step for the same message.  In the
         first case the hypothesis replay IS the conclusion; in the second we
         normalise the head step behind the install event. *)
      match client_head with
      | ConnNetworkEvent _ -> ()
      | ConnProtectedHandshake step ->
        assert (protected_handshake_buffer_empty client);
        lemma_single_message_head_step_replay_normalizes_after
          client
          (LocalInstallTrafficKeys {
            install_epoch = TrafficHandshake;
            install_direction = TrafficRead;
            install_material = client_material;
          })
          step
          client_rest
          client_raw_sent
          client_raw_received
          client_final ) )
#pop-options

#push-options "--z3rlimit 60"
let lemma_protected_handshake_event_projection_pair_after_server_write_client_read_install_heads_with_tails
  (server:connection_model)
  (client:connection_model)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        (match
          server.model_handshake.hs_keys.ks_handshake_secret,
          client.model_handshake.hs_keys.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.model_handshake.hs_transcript
          client.model_handshake.hs_transcript /\
        negotiated_aead_alg server.model_handshake ==
          negotiated_aead_alg client.model_handshake /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = server_material;
              };
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        conn_events_received_decode_replay
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final)
      (ensures
        exists server_after client_after server_after_head client_after_head pair
          server_tail_sent server_tail_received
          client_tail_sent client_tail_received.
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
              })) == Some client_after /\
          step_model
            server_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some server_after_head /\
          step_model
            client_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some client_after_head /\
          pair.pm_sender == server_after /\
          pair.pm_receiver == client_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal server_tail_sent client_tail_received /\
          conn_events_sent_seal_replay
            server_after_head
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          conn_events_received_decode_replay
            client_after_head
            client_rest
            client_tail_sent
            client_tail_received
            client_final)
=
  let server_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeysForRole {
        install_role = ServerEndpoint;
        install_payload = {
          install_epoch = TrafficHandshake;
          install_direction = TrafficWrite;
          install_material = server_material;
        };
      }) in
  let client_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeys {
        install_epoch = TrafficHandshake;
        install_direction = TrafficRead;
        install_material = client_material;
      }) in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    server
    server_install_ev
    (sent_ev :: server_rest)
    server_raw_sent
    server_raw_received
    client_raw_received
    server_final;
  eliminate exists
    (server_after:connection_model)
    (server_sent_after_install:B.bytes)
    (server_received_after_install:B.bytes).
    legal_event server server_install_ev /\
    step_model server server_install_ev == Some server_after /\
    Seq.equal server_sent_after_install client_raw_received /\
    conn_events_sent_seal_replay
      server_after
      (sent_ev :: server_rest)
      server_sent_after_install
      server_received_after_install
      server_final
  with
  ( lemma_received_replay_skip_empty_head_preserves_peer_stream
      server_sent_after_install
      client
      client_install_ev
      (received_ev :: client_rest)
      client_raw_sent
      client_raw_received
      client_final;
    eliminate exists
      (client_after:connection_model)
      (client_sent_after_install:B.bytes)
      (client_received_after_install:B.bytes).
      legal_event client client_install_ev /\
      step_model client client_install_ev == Some client_after /\
      Seq.equal server_sent_after_install client_received_after_install /\
      conn_events_received_decode_replay
        client_after
        (received_ev :: client_rest)
        client_sent_after_install
        client_received_after_install
        client_final
    with
    ( assert (legal_event server server_install_ev);
      assert (legal_event client client_install_ev);
      assert (legal_local_event server
        (LocalInstallTrafficKeysForRole {
          install_role = ServerEndpoint;
          install_payload = {
            install_epoch = TrafficHandshake;
            install_direction = TrafficWrite;
            install_material = server_material;
          };
        }));
      assert (legal_local_event client
        (LocalInstallTrafficKeys {
          install_epoch = TrafficHandshake;
          install_direction = TrafficRead;
          install_material = client_material;
        }));
      assert (traffic_install_matches_key_schedule_for_role
        ServerEndpoint
        server.model_handshake
        {
          install_epoch = TrafficHandshake;
          install_direction = TrafficWrite;
          install_material = server_material;
        });
      assert (traffic_install_matches_key_schedule
        client.model_handshake
        {
          install_epoch = TrafficHandshake;
          install_direction = TrafficRead;
          install_material = client_material;
        });
      lemma_server_handshake_write_client_handshake_read_install_aligned_from_key_schedule
        server
        client
        server_material
        client_material
        server_after
        client_after;
      lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
        server_after
        client_after
        sent_msg
        received_msg
        server_rest
        client_rest
        server_sent_after_install
        server_received_after_install
        client_sent_after_install
        client_received_after_install
        server_final
        client_final;
      eliminate exists
        (server_after_head0:connection_model)
        (client_after_head0:connection_model)
        (pair0:protected_message_replay)
        (server_tail_sent:B.bytes)
        (server_tail_received:B.bytes)
        (client_tail_sent:B.bytes)
        (client_tail_received:B.bytes).
        step_model server_after sent_ev == Some server_after_head0 /\
        step_model client_after received_ev == Some client_after_head0 /\
        pair0.pm_sender == server_after /\
        pair0.pm_receiver == client_after /\
        protected_handshake_event_projection_pair
          pair0
          sent_msg
          received_msg /\
        Seq.equal server_sent_after_install (B.append pair0.pm_raw_sent server_tail_sent) /\
        Seq.equal client_received_after_install (B.append pair0.pm_raw_received client_tail_received) /\
        Seq.equal server_tail_sent client_tail_received /\
        conn_events_sent_seal_replay
          server_after_head0
          server_rest
          server_tail_sent
          server_tail_received
          server_final /\
        conn_events_received_decode_replay
          client_after_head0
          client_rest
          client_tail_sent
          client_tail_received
          client_final
      with
      ( introduce exists
          (server_after':connection_model)
          (client_after':connection_model)
          (server_after_head:connection_model)
          (client_after_head:connection_model)
          (pair:protected_message_replay)
          (server_tail_sent':B.bytes)
          (server_tail_received':B.bytes)
          (client_tail_sent':B.bytes)
          (client_tail_received':B.bytes).
          step_model server server_install_ev == Some server_after' /\
          step_model client client_install_ev == Some client_after' /\
          step_model server_after' sent_ev == Some server_after_head /\
          step_model client_after' received_ev == Some client_after_head /\
          pair.pm_sender == server_after' /\
          pair.pm_receiver == client_after' /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal server_tail_sent' client_tail_received' /\
          conn_events_sent_seal_replay
            server_after_head
            server_rest
            server_tail_sent'
            server_tail_received'
            server_final /\
          conn_events_received_decode_replay
            client_after_head
            client_rest
            client_tail_sent'
            client_tail_received'
            client_final
        with
          server_after
          client_after
          server_after_head0
          client_after_head0
          pair0
          server_tail_sent
          server_tail_received
          client_tail_sent
          client_tail_received
        and () ) ) )

let lemma_protected_handshake_event_projection_pair_after_server_write_client_read_install_receiver_preserve_read_local_head_with_tails
  (server:connection_model)
  (client:connection_model)
  (receiver_skip:local_event)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        record_key_iv_material_agrees
          (record_material_of_traffic_material server_material)
          (record_material_of_traffic_material client_material) /\
        local_event_preserves_record_read receiver_skip /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = server_material;
              };
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        conn_events_received_decode_replay
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            }) :: ConnLocalEvent receiver_skip :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final)
      (ensures
        exists server_after client_after client_after_skip
          server_after_head client_after_head pair
          server_tail_sent server_tail_received
          client_tail_sent client_tail_received.
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
              })) == Some client_after /\
          step_model client_after (ConnLocalEvent receiver_skip) ==
            Some client_after_skip /\
          step_model
            server_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some server_after_head /\
          step_model
            client_after_skip
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some client_after_head /\
          pair.pm_sender == server_after /\
          pair.pm_receiver == client_after_skip /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal server_tail_sent client_tail_received /\
          conn_events_sent_seal_replay
            server_after_head
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          conn_events_received_decode_replay
            client_after_head
            client_rest
            client_tail_sent
            client_tail_received
            client_final)
=
  let server_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeysForRole {
        install_role = ServerEndpoint;
        install_payload = {
          install_epoch = TrafficHandshake;
          install_direction = TrafficWrite;
          install_material = server_material;
        };
      }) in
  let client_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeys {
        install_epoch = TrafficHandshake;
        install_direction = TrafficRead;
        install_material = client_material;
      }) in
  let receiver_skip_ev = ConnLocalEvent receiver_skip in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    server
    server_install_ev
    (sent_ev :: server_rest)
    server_raw_sent
    server_raw_received
    client_raw_received
    server_final;
  eliminate exists
    (server_after:connection_model)
    (server_sent_after_install:B.bytes)
    (server_received_after_install:B.bytes).
    legal_event server server_install_ev /\
    step_model server server_install_ev == Some server_after /\
    Seq.equal server_sent_after_install client_raw_received /\
    conn_events_sent_seal_replay
      server_after
      (sent_ev :: server_rest)
      server_sent_after_install
      server_received_after_install
      server_final
  with
  ( lemma_received_replay_skip_empty_head_preserves_peer_stream
      server_sent_after_install
      client
      client_install_ev
      (receiver_skip_ev :: received_ev :: client_rest)
      client_raw_sent
      client_raw_received
      client_final;
    eliminate exists
      (client_after:connection_model)
      (client_sent_after_install:B.bytes)
      (client_received_after_install:B.bytes).
      legal_event client client_install_ev /\
      step_model client client_install_ev == Some client_after /\
      Seq.equal server_sent_after_install client_received_after_install /\
      conn_events_received_decode_replay
        client_after
        (receiver_skip_ev :: received_ev :: client_rest)
        client_sent_after_install
        client_received_after_install
        client_final
    with
    ( lemma_received_replay_skip_empty_head_preserves_peer_stream
        server_sent_after_install
        client_after
        receiver_skip_ev
        (received_ev :: client_rest)
        client_sent_after_install
        client_received_after_install
        client_final;
      eliminate exists
        (client_after_skip:connection_model)
        (client_sent_after_skip:B.bytes)
        (client_received_after_skip:B.bytes).
        legal_event client_after receiver_skip_ev /\
        step_model client_after receiver_skip_ev == Some client_after_skip /\
        Seq.equal server_sent_after_install client_received_after_skip /\
        conn_events_received_decode_replay
          client_after_skip
          (received_ev :: client_rest)
          client_sent_after_skip
          client_received_after_skip
          client_final
      with
      ( lemma_server_handshake_write_client_handshake_read_install_materials_aligned
          server
          client
          server_material
          client_material
          server_after
          client_after;
        lemma_step_receiver_local_event_preserves_write_read_record_material_alignment
          server_after
          client_after
          receiver_skip
          client_after_skip;
        lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
          server_after
          client_after_skip
          sent_msg
          received_msg
          server_rest
          client_rest
          server_sent_after_install
          server_received_after_install
          client_sent_after_skip
          client_received_after_skip
          server_final
          client_final;
        eliminate exists
          (server_after_head0:connection_model)
          (client_after_head0:connection_model)
          (pair0:protected_message_replay)
          (server_tail_sent:B.bytes)
          (server_tail_received:B.bytes)
          (client_tail_sent:B.bytes)
          (client_tail_received:B.bytes).
          step_model server_after sent_ev == Some server_after_head0 /\
          step_model client_after_skip received_ev == Some client_after_head0 /\
          pair0.pm_sender == server_after /\
          pair0.pm_receiver == client_after_skip /\
          protected_handshake_event_projection_pair
            pair0
            sent_msg
            received_msg /\
          Seq.equal server_sent_after_install (B.append pair0.pm_raw_sent server_tail_sent) /\
          Seq.equal client_received_after_skip (B.append pair0.pm_raw_received client_tail_received) /\
          Seq.equal server_tail_sent client_tail_received /\
          conn_events_sent_seal_replay
            server_after_head0
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          conn_events_received_decode_replay
            client_after_head0
            client_rest
            client_tail_sent
            client_tail_received
            client_final
        with
        ( introduce exists
            (server_after':connection_model)
            (client_after':connection_model)
            (client_after_skip':connection_model)
            (server_after_head:connection_model)
            (client_after_head:connection_model)
            (pair:protected_message_replay)
            (server_tail_sent':B.bytes)
            (server_tail_received':B.bytes)
            (client_tail_sent':B.bytes)
            (client_tail_received':B.bytes).
            step_model server server_install_ev == Some server_after' /\
            step_model client client_install_ev == Some client_after' /\
            step_model client_after' receiver_skip_ev == Some client_after_skip' /\
            step_model server_after' sent_ev == Some server_after_head /\
            step_model client_after_skip' received_ev == Some client_after_head /\
            pair.pm_sender == server_after' /\
            pair.pm_receiver == client_after_skip' /\
            protected_handshake_event_projection_pair pair sent_msg received_msg /\
            Seq.equal server_tail_sent' client_tail_received' /\
            conn_events_sent_seal_replay
              server_after_head
              server_rest
              server_tail_sent'
              server_tail_received'
              server_final /\
            conn_events_received_decode_replay
              client_after_head
              client_rest
              client_tail_sent'
              client_tail_received'
              client_final
          with
            server_after
            client_after
            client_after_skip
            server_after_head0
            client_after_head0
            pair0
            server_tail_sent
            server_tail_received
            client_tail_sent
            client_tail_received
          and () ) ) ) )

#restart-solver
let lemma_protected_handshake_event_projection_pair_after_server_write_receiver_preserve_read_local_head_client_read_install_with_tails
  (server:connection_model)
  (client:connection_model)
  (receiver_skip:local_event)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        record_key_iv_material_agrees
          (record_material_of_traffic_material server_material)
          (record_material_of_traffic_material client_material) /\
        local_event_preserves_record_read receiver_skip /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = server_material;
              };
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        conn_events_received_decode_replay
          client
          (ConnLocalEvent receiver_skip :: ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final)
      (ensures
        exists server_after client_after_skip client_after
          server_after_head client_after_head pair
          server_tail_sent server_tail_received
          client_tail_sent client_tail_received.
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
          step_model client (ConnLocalEvent receiver_skip) ==
            Some client_after_skip /\
          step_model
            client_after_skip
            (ConnLocalEvent
              (LocalInstallTrafficKeys {
                install_epoch = TrafficHandshake;
                install_direction = TrafficRead;
                install_material = client_material;
              })) == Some client_after /\
          step_model
            server_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some server_after_head /\
          step_model
            client_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some client_after_head /\
          pair.pm_sender == server_after /\
          pair.pm_receiver == client_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal server_tail_sent client_tail_received /\
          conn_events_sent_seal_replay
            server_after_head
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          conn_events_received_decode_replay
            client_after_head
            client_rest
            client_tail_sent
            client_tail_received
            client_final)
=
  let server_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeysForRole {
        install_role = ServerEndpoint;
        install_payload = {
          install_epoch = TrafficHandshake;
          install_direction = TrafficWrite;
          install_material = server_material;
        };
      }) in
  let receiver_skip_ev = ConnLocalEvent receiver_skip in
  let client_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeys {
        install_epoch = TrafficHandshake;
        install_direction = TrafficRead;
        install_material = client_material;
      }) in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    server
    server_install_ev
    (sent_ev :: server_rest)
    server_raw_sent
    server_raw_received
    client_raw_received
    server_final;
  eliminate exists
    (server_after:connection_model)
    (server_sent_after_install:B.bytes)
    (server_received_after_install:B.bytes).
    legal_event server server_install_ev /\
    step_model server server_install_ev == Some server_after /\
    Seq.equal server_sent_after_install client_raw_received /\
    conn_events_sent_seal_replay
      server_after
      (sent_ev :: server_rest)
      server_sent_after_install
      server_received_after_install
      server_final
  with
  ( lemma_received_replay_skip_empty_head_preserves_peer_stream
      server_sent_after_install
      client
      receiver_skip_ev
      (client_install_ev :: received_ev :: client_rest)
      client_raw_sent
      client_raw_received
      client_final;
    eliminate exists
      (client_after_skip:connection_model)
      (client_sent_after_skip:B.bytes)
      (client_received_after_skip:B.bytes).
      legal_event client receiver_skip_ev /\
      step_model client receiver_skip_ev == Some client_after_skip /\
      Seq.equal server_sent_after_install client_received_after_skip /\
      conn_events_received_decode_replay
        client_after_skip
        (client_install_ev :: received_ev :: client_rest)
        client_sent_after_skip
        client_received_after_skip
        client_final
    with
    ( lemma_received_replay_skip_empty_head_preserves_peer_stream
        server_sent_after_install
        client_after_skip
        client_install_ev
        (received_ev :: client_rest)
        client_sent_after_skip
        client_received_after_skip
        client_final;
      eliminate exists
        (client_after:connection_model)
        (client_sent_after_install:B.bytes)
        (client_received_after_install:B.bytes).
        legal_event client_after_skip client_install_ev /\
        step_model client_after_skip client_install_ev == Some client_after /\
        Seq.equal server_sent_after_install client_received_after_install /\
        conn_events_received_decode_replay
          client_after
          (received_ev :: client_rest)
          client_sent_after_install
          client_received_after_install
          client_final
      with
      ( lemma_server_handshake_write_client_handshake_read_install_materials_aligned
          server
          client_after_skip
          server_material
          client_material
          server_after
          client_after;
        lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
          server_after
          client_after
          sent_msg
          received_msg
          server_rest
          client_rest
          server_sent_after_install
          server_received_after_install
          client_sent_after_install
          client_received_after_install
          server_final
          client_final;
        eliminate exists
          (server_after_head0:connection_model)
          (client_after_head0:connection_model)
          (pair0:protected_message_replay)
          (server_tail_sent:B.bytes)
          (server_tail_received:B.bytes)
          (client_tail_sent:B.bytes)
          (client_tail_received:B.bytes).
          step_model server_after sent_ev == Some server_after_head0 /\
          step_model client_after received_ev == Some client_after_head0 /\
          pair0.pm_sender == server_after /\
          pair0.pm_receiver == client_after /\
          protected_handshake_event_projection_pair
            pair0
            sent_msg
            received_msg /\
          Seq.equal server_sent_after_install (B.append pair0.pm_raw_sent server_tail_sent) /\
          Seq.equal client_received_after_install (B.append pair0.pm_raw_received client_tail_received) /\
          Seq.equal server_tail_sent client_tail_received /\
          conn_events_sent_seal_replay
            server_after_head0
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          conn_events_received_decode_replay
            client_after_head0
            client_rest
            client_tail_sent
            client_tail_received
            client_final
        with
        ( introduce exists
            (server_after':connection_model)
            (client_after_skip':connection_model)
            (client_after':connection_model)
            (server_after_head:connection_model)
            (client_after_head:connection_model)
            (pair:protected_message_replay)
            (server_tail_sent':B.bytes)
            (server_tail_received':B.bytes)
            (client_tail_sent':B.bytes)
            (client_tail_received':B.bytes).
            step_model server server_install_ev == Some server_after' /\
            step_model client receiver_skip_ev == Some client_after_skip' /\
            step_model client_after_skip' client_install_ev == Some client_after' /\
            step_model server_after' sent_ev == Some server_after_head /\
            step_model client_after' received_ev == Some client_after_head /\
            pair.pm_sender == server_after' /\
            pair.pm_receiver == client_after' /\
            protected_handshake_event_projection_pair pair sent_msg received_msg /\
            Seq.equal server_tail_sent' client_tail_received' /\
            conn_events_sent_seal_replay
              server_after_head
              server_rest
              server_tail_sent'
              server_tail_received'
              server_final /\
            conn_events_received_decode_replay
              client_after_head
              client_rest
              client_tail_sent'
              client_tail_received'
              client_final
          with
            server_after
            client_after_skip
            client_after
            server_after_head0
            client_after_head0
            pair0
            server_tail_sent
            server_tail_received
            client_tail_sent
            client_tail_received
          and () ) ) ) )

let lemma_protected_handshake_event_projection_pair_after_sender_preserve_write_local_head_server_write_client_read_install_with_tails
  (server:connection_model)
  (client:connection_model)
  (sender_skip:local_event)
  (server_after_skip:connection_model)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        (match
          server_after_skip.model_handshake.hs_keys.ks_handshake_secret,
          client.model_handshake.hs_keys.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server_after_skip.model_handshake.hs_transcript
          client.model_handshake.hs_transcript /\
        negotiated_aead_alg server_after_skip.model_handshake ==
          negotiated_aead_alg client.model_handshake /\
        local_event_preserves_record_write sender_skip /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        step_model server (ConnLocalEvent sender_skip) ==
          Some server_after_skip /\
        conn_events_sent_seal_replay
          server
          (ConnLocalEvent sender_skip :: ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = server_material;
              };
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        conn_events_received_decode_replay
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final)
      (ensures
        exists server_after client_after server_after_head client_after_head pair
          server_tail_sent server_tail_received
          client_tail_sent client_tail_received.
          step_model
            server_after_skip
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
              })) == Some client_after /\
          step_model
            server_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some server_after_head /\
          step_model
            client_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some client_after_head /\
          pair.pm_sender == server_after /\
          pair.pm_receiver == client_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal server_tail_sent client_tail_received /\
          conn_events_sent_seal_replay
            server_after_head
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          conn_events_received_decode_replay
            client_after_head
            client_rest
            client_tail_sent
            client_tail_received
            client_final)
=
  let sender_skip_ev = ConnLocalEvent sender_skip in
  let server_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeysForRole {
        install_role = ServerEndpoint;
        install_payload = {
          install_epoch = TrafficHandshake;
          install_direction = TrafficWrite;
          install_material = server_material;
        };
      }) in
  let client_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeys {
        install_epoch = TrafficHandshake;
        install_direction = TrafficRead;
        install_material = client_material;
      }) in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    server
    sender_skip_ev
    (server_install_ev :: sent_ev :: server_rest)
    server_raw_sent
    server_raw_received
    client_raw_received
    server_final;
  eliminate exists
    (server_after_skip0:connection_model)
    (server_sent_after_skip:B.bytes)
    (server_received_after_skip:B.bytes).
    legal_event server sender_skip_ev /\
    step_model server sender_skip_ev == Some server_after_skip0 /\
    Seq.equal server_sent_after_skip client_raw_received /\
    conn_events_sent_seal_replay
      server_after_skip0
      (server_install_ev :: sent_ev :: server_rest)
      server_sent_after_skip
      server_received_after_skip
      server_final
  with
  (
    assert (server_after_skip0 == server_after_skip);
    lemma_protected_handshake_event_projection_pair_after_server_write_client_read_install_heads_with_tails
      server_after_skip
      client
      server_material
      client_material
      sent_msg
      received_msg
      server_rest
      client_rest
      server_sent_after_skip
      server_received_after_skip
      client_raw_sent
      client_raw_received
      server_final
      client_final;
    eliminate exists server_after client_after server_after_head client_after_head pair
      server_tail_sent server_tail_received client_tail_sent client_tail_received.
      step_model server_after_skip server_install_ev == Some server_after /\
      step_model client client_install_ev == Some client_after /\
      step_model server_after sent_ev == Some server_after_head /\
      step_model client_after received_ev == Some client_after_head /\
      pair.pm_sender == server_after /\
      pair.pm_receiver == client_after /\
      protected_handshake_event_projection_pair pair sent_msg received_msg /\
      Seq.equal server_tail_sent client_tail_received /\
      conn_events_sent_seal_replay
        server_after_head
        server_rest
        server_tail_sent
        server_tail_received
        server_final /\
      conn_events_received_decode_replay
        client_after_head
        client_rest
        client_tail_sent
        client_tail_received
        client_final
    with
    (
      introduce exists
        (server_after':connection_model)
        (client_after':connection_model)
        (server_after_head':connection_model)
        (client_after_head':connection_model)
        (pair':protected_message_replay)
        (server_tail_sent':B.bytes)
        (server_tail_received':B.bytes)
        (client_tail_sent':B.bytes)
        (client_tail_received':B.bytes).
        step_model server_after_skip server_install_ev == Some server_after' /\
        step_model client client_install_ev == Some client_after' /\
        step_model server_after' sent_ev == Some server_after_head' /\
        step_model client_after' received_ev == Some client_after_head' /\
        pair'.pm_sender == server_after' /\
        pair'.pm_receiver == client_after' /\
        protected_handshake_event_projection_pair pair' sent_msg received_msg /\
        Seq.equal server_tail_sent' client_tail_received' /\
        conn_events_sent_seal_replay
          server_after_head'
          server_rest
          server_tail_sent'
          server_tail_received'
          server_final /\
        conn_events_received_decode_replay
          client_after_head'
          client_rest
          client_tail_sent'
          client_tail_received'
          client_final
      with
        server_after
        client_after
        server_after_head
        client_after_head
        pair
        server_tail_sent
        server_tail_received
        client_tail_sent
        client_tail_received
      and ()
    )
  )

let lemma_protected_handshake_event_projection_pair_after_sender_preserve_write_local_head_server_write_receiver_preserve_read_local_head_client_read_install_with_tails
  (server:connection_model)
  (client:connection_model)
  (sender_skip:local_event)
  (server_after_skip:connection_model)
  (receiver_skip:local_event)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        record_key_iv_material_agrees
          (record_material_of_traffic_material server_material)
          (record_material_of_traffic_material client_material) /\
        local_event_preserves_record_write sender_skip /\
        local_event_preserves_record_read receiver_skip /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        step_model server (ConnLocalEvent sender_skip) ==
          Some server_after_skip /\
        conn_events_sent_seal_replay
          server
          (ConnLocalEvent sender_skip :: ConnLocalEvent
             (LocalInstallTrafficKeysForRole {
               install_role = ServerEndpoint;
               install_payload = {
                 install_epoch = TrafficHandshake;
                 install_direction = TrafficWrite;
                 install_material = server_material;
               };
             }) :: ConnNetworkEvent {
               CL.message_direction = CL.Sent;
               CL.message_value = M.TlsHandshake sent_msg;
             } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        conn_events_received_decode_replay
          client
          (ConnLocalEvent receiver_skip :: ConnLocalEvent
             (LocalInstallTrafficKeys {
               install_epoch = TrafficHandshake;
               install_direction = TrafficRead;
               install_material = client_material;
             }) :: ConnNetworkEvent {
               CL.message_direction = CL.Received;
               CL.message_value = M.TlsHandshake received_msg;
             } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final)
      (ensures
        exists server_after client_after_skip client_after
          server_after_head client_after_head pair
          server_tail_sent server_tail_received
          client_tail_sent client_tail_received.
          step_model server (ConnLocalEvent sender_skip) ==
            Some server_after_skip /\
          step_model
             server_after_skip
             (ConnLocalEvent
               (LocalInstallTrafficKeysForRole {
                 install_role = ServerEndpoint;
                 install_payload = {
                   install_epoch = TrafficHandshake;
                   install_direction = TrafficWrite;
                   install_material = server_material;
                 };
               })) == Some server_after /\
          step_model client (ConnLocalEvent receiver_skip) ==
            Some client_after_skip /\
          step_model
             client_after_skip
             (ConnLocalEvent
               (LocalInstallTrafficKeys {
                 install_epoch = TrafficHandshake;
                 install_direction = TrafficRead;
                 install_material = client_material;
               })) == Some client_after /\
          step_model
             server_after
             (ConnNetworkEvent {
               CL.message_direction = CL.Sent;
               CL.message_value = M.TlsHandshake sent_msg;
             }) == Some server_after_head /\
          step_model
             client_after
             (ConnNetworkEvent {
               CL.message_direction = CL.Received;
               CL.message_value = M.TlsHandshake received_msg;
             }) == Some client_after_head /\
          pair.pm_sender == server_after /\
          pair.pm_receiver == client_after /\
          protected_handshake_event_projection_pair
             pair
             sent_msg
             received_msg /\
          Seq.equal server_tail_sent client_tail_received /\
          conn_events_sent_seal_replay
             server_after_head
             server_rest
             server_tail_sent
             server_tail_received
             server_final /\
          conn_events_received_decode_replay
             client_after_head
             client_rest
             client_tail_sent
             client_tail_received
             client_final)
=
  let sender_skip_ev = ConnLocalEvent sender_skip in
  let server_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeysForRole {
        install_role = ServerEndpoint;
        install_payload = {
          install_epoch = TrafficHandshake;
          install_direction = TrafficWrite;
          install_material = server_material;
        };
      }) in
  let receiver_skip_ev = ConnLocalEvent receiver_skip in
  let client_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeys {
        install_epoch = TrafficHandshake;
        install_direction = TrafficRead;
        install_material = client_material;
      }) in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    server
    sender_skip_ev
    (server_install_ev :: sent_ev :: server_rest)
    server_raw_sent
    server_raw_received
    client_raw_received
    server_final;
  eliminate exists
    (server_after_skip0:connection_model)
    (server_sent_after_skip:B.bytes)
    (server_received_after_skip:B.bytes).
    legal_event server sender_skip_ev /\
    step_model server sender_skip_ev == Some server_after_skip0 /\
    Seq.equal server_sent_after_skip client_raw_received /\
    conn_events_sent_seal_replay
      server_after_skip0
      (server_install_ev :: sent_ev :: server_rest)
      server_sent_after_skip
      server_received_after_skip
      server_final
  with
  (
    assert (server_after_skip0 == server_after_skip);
    lemma_protected_handshake_event_projection_pair_after_server_write_receiver_preserve_read_local_head_client_read_install_with_tails
      server_after_skip
      client
      receiver_skip
      server_material
      client_material
      sent_msg
      received_msg
      server_rest
      client_rest
      server_sent_after_skip
      server_received_after_skip
      client_raw_sent
      client_raw_received
      server_final
      client_final;
    eliminate exists
      (server_after:connection_model)
      (client_after_skip:connection_model)
      (client_after:connection_model)
      (server_after_head:connection_model)
      (client_after_head:connection_model)
      (pair:protected_message_replay)
      (server_tail_sent:B.bytes)
      (server_tail_received:B.bytes)
      (client_tail_sent:B.bytes)
      (client_tail_received:B.bytes).
      step_model server_after_skip server_install_ev == Some server_after /\
      step_model client receiver_skip_ev == Some client_after_skip /\
      step_model client_after_skip client_install_ev == Some client_after /\
      step_model server_after sent_ev == Some server_after_head /\
      step_model client_after received_ev == Some client_after_head /\
      pair.pm_sender == server_after /\
      pair.pm_receiver == client_after /\
      protected_handshake_event_projection_pair pair sent_msg received_msg /\
      Seq.equal server_tail_sent client_tail_received /\
      conn_events_sent_seal_replay
        server_after_head
        server_rest
        server_tail_sent
        server_tail_received
        server_final /\
      conn_events_received_decode_replay
        client_after_head
        client_rest
        client_tail_sent
        client_tail_received
        client_final
    with
    (
      introduce exists
        (server_after':connection_model)
        (client_after_skip':connection_model)
        (client_after':connection_model)
        (server_after_head':connection_model)
        (client_after_head':connection_model)
        (pair':protected_message_replay)
        (server_tail_sent':B.bytes)
        (server_tail_received':B.bytes)
        (client_tail_sent':B.bytes)
        (client_tail_received':B.bytes).
        step_model server sender_skip_ev == Some server_after_skip /\
        step_model server_after_skip server_install_ev == Some server_after' /\
        step_model client receiver_skip_ev == Some client_after_skip' /\
        step_model client_after_skip' client_install_ev == Some client_after' /\
        step_model server_after' sent_ev == Some server_after_head' /\
        step_model client_after' received_ev == Some client_after_head' /\
        pair'.pm_sender == server_after' /\
        pair'.pm_receiver == client_after' /\
        protected_handshake_event_projection_pair pair' sent_msg received_msg /\
        Seq.equal server_tail_sent' client_tail_received' /\
        conn_events_sent_seal_replay
          server_after_head'
          server_rest
          server_tail_sent'
          server_tail_received'
          server_final /\
        conn_events_received_decode_replay
          client_after_head'
          client_rest
          client_tail_sent'
          client_tail_received'
          client_final
      with
        server_after
        client_after_skip
        client_after
        server_after_head
        client_after_head
        pair
        server_tail_sent
        server_tail_received
        client_tail_sent
        client_tail_received
      and ()
    )
  )

#restart-solver
let lemma_protected_handshake_event_projection_pair_after_server_write_client_read_install_heads_with_next_alignment_and_tails
  (server:connection_model)
  (client:connection_model)
  (server_after:connection_model)
  (client_after:connection_model)
  (server_after_head:connection_model)
  (client_after_head:connection_model)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        (match
          server.model_handshake.hs_keys.ks_handshake_secret,
          client.model_handshake.hs_keys.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.model_handshake.hs_transcript
          client.model_handshake.hs_transcript /\
        negotiated_aead_alg server.model_handshake ==
          negotiated_aead_alg client.model_handshake /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
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
            })) == Some client_after /\
        step_model
          server_after
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some server_after_head /\
        step_model
          client_after
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some client_after_head /\
        server_after_head.model_record.record_write ==
          R.next_seq server_after.model_record.record_write /\
        client_after_head.model_record.record_read ==
          R.next_seq client_after.model_record.record_read /\
        conn_events_sent_seal_replay
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = server_material;
              };
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        conn_events_received_decode_replay
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final)
      (ensures
        exists pair server_tail_sent server_tail_received
          client_tail_sent client_tail_received.
          pair.pm_sender == server_after /\
          pair.pm_receiver == client_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          write_read_record_material_aligned server_after_head client_after_head /\
          Seq.equal server_tail_sent client_tail_received /\
          conn_events_sent_seal_replay
            server_after_head
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          conn_events_received_decode_replay
            client_after_head
            client_rest
            client_tail_sent
            client_tail_received
            client_final)
=
  let server_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeysForRole {
        install_role = ServerEndpoint;
        install_payload = {
          install_epoch = TrafficHandshake;
          install_direction = TrafficWrite;
          install_material = server_material;
        };
      }) in
  let client_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeys {
        install_epoch = TrafficHandshake;
        install_direction = TrafficRead;
        install_material = client_material;
      }) in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    server
    server_install_ev
    (sent_ev :: server_rest)
    server_raw_sent
    server_raw_received
    client_raw_received
    server_final;
  eliminate exists
    (server_after0:connection_model)
    (server_sent_after_install:B.bytes)
    (server_received_after_install:B.bytes).
    legal_event server server_install_ev /\
    step_model server server_install_ev == Some server_after0 /\
    Seq.equal server_sent_after_install client_raw_received /\
    conn_events_sent_seal_replay
      server_after0
      (sent_ev :: server_rest)
      server_sent_after_install
      server_received_after_install
      server_final
  with
  ( assert (server_after0 == server_after);
    assert (traffic_install_matches_key_schedule_for_role
      ServerEndpoint
      server.model_handshake
      {
        install_epoch = TrafficHandshake;
        install_direction = TrafficWrite;
        install_material = server_material;
      });
    lemma_received_replay_skip_empty_head_preserves_peer_stream
      server_sent_after_install
      client
      client_install_ev
      (received_ev :: client_rest)
      client_raw_sent
      client_raw_received
      client_final;
    eliminate exists
      (client_after0:connection_model)
      (client_sent_after_install:B.bytes)
      (client_received_after_install:B.bytes).
      legal_event client client_install_ev /\
      step_model client client_install_ev == Some client_after0 /\
      Seq.equal server_sent_after_install client_received_after_install /\
      conn_events_received_decode_replay
        client_after0
        (received_ev :: client_rest)
        client_sent_after_install
        client_received_after_install
        client_final
    with
    ( assert (client_after0 == client_after);
      assert (traffic_install_matches_key_schedule
        client.model_handshake
        {
          install_epoch = TrafficHandshake;
          install_direction = TrafficRead;
          install_material = client_material;
        });
      lemma_server_handshake_write_client_handshake_read_install_aligned_from_key_schedule
        server
        client
        server_material
        client_material
        server_after
        client_after;
      lemma_protected_handshake_event_projection_pair_after_both_skip_empty_heads_with_next_alignment_and_tails
        server
        server_after
        client
        client_after
        server_after_head
        client_after_head
        server_install_ev
        client_install_ev
        sent_msg
        received_msg
        server_rest
        client_rest
        server_raw_sent
        server_raw_received
        client_raw_sent
        client_raw_received
        server_final
        client_final ) )

let lemma_protected_handshake_event_projection_pairs_after_server_write_client_read_install_and_next_head_with_tails
  (server:connection_model)
  (client:connection_model)
  (server_after_install:connection_model)
  (client_after_install:connection_model)
  (server_after0:connection_model)
  (client_after0:connection_model)
  (server_after1:connection_model)
  (client_after1:connection_model)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
        (requires
          (match
            server.model_handshake.hs_keys.ks_handshake_secret,
            client.model_handshake.hs_keys.ks_handshake_secret
          with
          | Some server_secret, Some client_secret ->
            Seq.equal server_secret client_secret
          | _, _ ->
            False) /\
          Seq.equal
            server.model_handshake.hs_transcript
            client.model_handshake.hs_transcript /\
          negotiated_aead_alg server.model_handshake ==
            negotiated_aead_alg client.model_handshake /\
          Seq.equal server_raw_sent client_raw_received /\
          protected_handshake_wire_round_trip_message sent_msg0 /\
          protected_handshake_wire_round_trip_message received_msg0 /\
          protected_handshake_wire_round_trip_message sent_msg1 /\
          protected_handshake_wire_round_trip_message received_msg1 /\
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
              })) == Some server_after_install /\
          step_model
            client
            (ConnLocalEvent
              (LocalInstallTrafficKeys {
                install_epoch = TrafficHandshake;
                install_direction = TrafficRead;
                install_material = client_material;
              })) == Some client_after_install /\
          step_model
            server_after_install
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg0;
            }) == Some server_after0 /\
          step_model
            client_after_install
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg0;
            }) == Some client_after0 /\
          server_after0.model_record.record_write ==
            R.next_seq server_after_install.model_record.record_write /\
          client_after0.model_record.record_read ==
            R.next_seq client_after_install.model_record.record_read /\
          step_model
            server_after0
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg1;
            }) == Some server_after1 /\
          step_model
            client_after0
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg1;
            }) == Some client_after1 /\
          server_after1.model_record.record_write ==
            R.next_seq server_after0.model_record.record_write /\
          client_after1.model_record.record_read ==
            R.next_seq client_after0.model_record.record_read /\
          conn_events_sent_seal_replay
            server
            (ConnLocalEvent
              (LocalInstallTrafficKeysForRole {
                install_role = ServerEndpoint;
                install_payload = {
                  install_epoch = TrafficHandshake;
                  install_direction = TrafficWrite;
                  install_material = server_material;
                };
              }) :: ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake sent_msg0;
              } :: ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake sent_msg1;
              } :: server_rest)
            server_raw_sent
            server_raw_received
            server_final /\
          conn_events_received_decode_replay
            client
            (ConnLocalEvent
              (LocalInstallTrafficKeys {
                install_epoch = TrafficHandshake;
                install_direction = TrafficRead;
                install_material = client_material;
              }) :: ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake received_msg0;
              } :: ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake received_msg1;
              } :: client_rest)
            client_raw_sent
            client_raw_received
            client_final)
        (ensures
          exists pair0 pair1 server_tail_sent server_tail_received
            client_tail_sent client_tail_received.
            pair0.pm_sender == server_after_install /\
            pair0.pm_receiver == client_after_install /\
            protected_handshake_event_projection_pair
              pair0
              sent_msg0
              received_msg0 /\
            pair1.pm_sender == server_after0 /\
            pair1.pm_receiver == client_after0 /\
            protected_handshake_event_projection_pair
              pair1
              sent_msg1
              received_msg1 /\
            write_read_record_material_aligned server_after1 client_after1 /\
            Seq.equal server_tail_sent client_tail_received /\
            conn_events_sent_seal_replay
              server_after1
              server_rest
              server_tail_sent
              server_tail_received
              server_final /\
            conn_events_received_decode_replay
              client_after1
              client_rest
              client_tail_sent
              client_tail_received
              client_final)
=
  let sent_ev1 = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg1;
  } in
  let received_ev1 = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg1;
  } in
  lemma_protected_handshake_event_projection_pair_after_server_write_client_read_install_heads_with_next_alignment_and_tails
    server
    client
    server_after_install
    client_after_install
    server_after0
    client_after0
    server_material
    client_material
    sent_msg0
    received_msg0
    (sent_ev1 :: server_rest)
    (received_ev1 :: client_rest)
    server_raw_sent
    server_raw_received
    client_raw_sent
    client_raw_received
    server_final
    client_final;
  eliminate exists
    (pair0:protected_message_replay)
    (server_tail_sent0:B.bytes)
    (server_tail_received0:B.bytes)
    (client_tail_sent0:B.bytes)
    (client_tail_received0:B.bytes).
    pair0.pm_sender == server_after_install /\
    pair0.pm_receiver == client_after_install /\
    protected_handshake_event_projection_pair
        pair0
        sent_msg0
        received_msg0 /\
    write_read_record_material_aligned server_after0 client_after0 /\
    Seq.equal server_tail_sent0 client_tail_received0 /\
    conn_events_sent_seal_replay
        server_after0
        (sent_ev1 :: server_rest)
        server_tail_sent0
        server_tail_received0
        server_final /\
    conn_events_received_decode_replay
        client_after0
        (received_ev1 :: client_rest)
        client_tail_sent0
        client_tail_received0
        client_final
  with
  ( lemma_protected_handshake_event_projection_pair_from_head_replays_with_next_alignment_and_tails
        server_after0
        client_after0
        server_after1
        client_after1
        sent_msg1
        received_msg1
        server_rest
        client_rest
        server_tail_sent0
        server_tail_received0
        client_tail_sent0
        client_tail_received0
        server_final
        client_final;
    eliminate exists
        (pair1:protected_message_replay)
        (server_tail_sent1:B.bytes)
        (server_tail_received1:B.bytes)
        (client_tail_sent1:B.bytes)
        (client_tail_received1:B.bytes).
        pair1.pm_sender == server_after0 /\
        pair1.pm_receiver == client_after0 /\
        protected_handshake_event_projection_pair
          pair1
          sent_msg1
          received_msg1 /\
        write_read_record_material_aligned server_after1 client_after1 /\
        Seq.equal server_tail_sent0 (B.append pair1.pm_raw_sent server_tail_sent1) /\
        Seq.equal client_tail_received0 (B.append pair1.pm_raw_received client_tail_received1) /\
        Seq.equal server_tail_sent1 client_tail_received1 /\
        conn_events_sent_seal_replay
          server_after1
          server_rest
          server_tail_sent1
          server_tail_received1
          server_final /\
        conn_events_received_decode_replay
          client_after1
          client_rest
          client_tail_sent1
          client_tail_received1
          client_final
    with
    ( introduce exists
          (pair0':protected_message_replay)
          (pair1':protected_message_replay)
          (server_tail_sent:B.bytes)
          (server_tail_received:B.bytes)
          (client_tail_sent:B.bytes)
          (client_tail_received:B.bytes).
          pair0'.pm_sender == server_after_install /\
          pair0'.pm_receiver == client_after_install /\
          protected_handshake_event_projection_pair
            pair0'
            sent_msg0
            received_msg0 /\
          pair1'.pm_sender == server_after0 /\
          pair1'.pm_receiver == client_after0 /\
          protected_handshake_event_projection_pair
            pair1'
            sent_msg1
            received_msg1 /\
          write_read_record_material_aligned server_after1 client_after1 /\
          Seq.equal server_tail_sent client_tail_received /\
          conn_events_sent_seal_replay
            server_after1
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          conn_events_received_decode_replay
            client_after1
            client_rest
            client_tail_sent
            client_tail_received
            client_final
        with
          pair0
          pair1
          server_tail_sent1
          server_tail_received1
          client_tail_sent1
          client_tail_received1
        and () ) )

let lemma_protected_handshake_event_projection_pairs_after_server_write_client_read_install_two_heads_then_both_non_install_local_heads_with_next_alignment_and_tails
  (server:connection_model)
  (client:connection_model)
  (server_after_install:connection_model)
  (client_after_install:connection_model)
  (server_after0:connection_model)
  (client_after0:connection_model)
  (server_after1:connection_model)
  (client_after1:connection_model)
  (server_after_skip:connection_model)
  (client_after_skip:connection_model)
  (server_after2:connection_model)
  (client_after2:connection_model)
  (server_skip:local_event)
  (client_skip:local_event)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
        (requires
          (match
            server.model_handshake.hs_keys.ks_handshake_secret,
            client.model_handshake.hs_keys.ks_handshake_secret
          with
          | Some server_secret, Some client_secret ->
            Seq.equal server_secret client_secret
          | _, _ ->
            False) /\
          Seq.equal
            server.model_handshake.hs_transcript
            client.model_handshake.hs_transcript /\
          negotiated_aead_alg server.model_handshake ==
            negotiated_aead_alg client.model_handshake /\
          local_event_does_not_install_record_keys server_skip /\
          local_event_does_not_install_record_keys client_skip /\
          Seq.equal server_raw_sent client_raw_received /\
          protected_handshake_wire_round_trip_message sent_msg0 /\
          protected_handshake_wire_round_trip_message received_msg0 /\
          protected_handshake_wire_round_trip_message sent_msg1 /\
          protected_handshake_wire_round_trip_message received_msg1 /\
          protected_handshake_wire_round_trip_message sent_msg2 /\
          protected_handshake_wire_round_trip_message received_msg2 /\
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
              })) == Some server_after_install /\
          step_model
            client
            (ConnLocalEvent
              (LocalInstallTrafficKeys {
                install_epoch = TrafficHandshake;
                install_direction = TrafficRead;
                install_material = client_material;
              })) == Some client_after_install /\
          step_model
            server_after_install
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg0;
            }) == Some server_after0 /\
          step_model
            client_after_install
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg0;
            }) == Some client_after0 /\
          server_after0.model_record.record_write ==
            R.next_seq server_after_install.model_record.record_write /\
          client_after0.model_record.record_read ==
            R.next_seq client_after_install.model_record.record_read /\
          step_model
            server_after0
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg1;
            }) == Some server_after1 /\
          step_model
            client_after0
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg1;
            }) == Some client_after1 /\
          server_after1.model_record.record_write ==
            R.next_seq server_after0.model_record.record_write /\
          client_after1.model_record.record_read ==
            R.next_seq client_after0.model_record.record_read /\
          step_model server_after1 (ConnLocalEvent server_skip) ==
            Some server_after_skip /\
          step_model client_after1 (ConnLocalEvent client_skip) ==
            Some client_after_skip /\
          step_model
            server_after_skip
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg2;
            }) == Some server_after2 /\
          step_model
            client_after_skip
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg2;
            }) == Some client_after2 /\
          server_after2.model_record.record_write ==
            R.next_seq server_after_skip.model_record.record_write /\
          client_after2.model_record.record_read ==
            R.next_seq client_after_skip.model_record.record_read /\
          conn_events_sent_seal_replay
            server
            (ConnLocalEvent
              (LocalInstallTrafficKeysForRole {
                install_role = ServerEndpoint;
                install_payload = {
                  install_epoch = TrafficHandshake;
                  install_direction = TrafficWrite;
                  install_material = server_material;
                };
              }) :: ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake sent_msg0;
              } :: ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake sent_msg1;
              } :: ConnLocalEvent server_skip :: ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake sent_msg2;
              } :: server_rest)
            server_raw_sent
            server_raw_received
            server_final /\
          conn_events_received_decode_replay
            client
            (ConnLocalEvent
              (LocalInstallTrafficKeys {
                install_epoch = TrafficHandshake;
                install_direction = TrafficRead;
                install_material = client_material;
              }) :: ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake received_msg0;
              } :: ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake received_msg1;
              } :: ConnLocalEvent client_skip :: ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake received_msg2;
              } :: client_rest)
            client_raw_sent
            client_raw_received
            client_final)
        (ensures
          exists pair0 pair1 pair2 server_tail_sent server_tail_received
            client_tail_sent client_tail_received.
            pair0.pm_sender == server_after_install /\
            pair0.pm_receiver == client_after_install /\
            protected_handshake_event_projection_pair
              pair0
              sent_msg0
              received_msg0 /\
            pair1.pm_sender == server_after0 /\
            pair1.pm_receiver == client_after0 /\
            protected_handshake_event_projection_pair
              pair1
              sent_msg1
              received_msg1 /\
            pair2.pm_sender == server_after_skip /\
            pair2.pm_receiver == client_after_skip /\
            protected_handshake_event_projection_pair
              pair2
              sent_msg2
              received_msg2 /\
            write_read_record_material_aligned server_after2 client_after2 /\
            Seq.equal server_tail_sent client_tail_received /\
            conn_events_sent_seal_replay
              server_after2
              server_rest
              server_tail_sent
              server_tail_received
              server_final /\
            conn_events_received_decode_replay
              client_after2
              client_rest
              client_tail_sent
              client_tail_received
              client_final)
=
  let server_skip_ev = ConnLocalEvent server_skip in
  let client_skip_ev = ConnLocalEvent client_skip in
  let sent_ev2 = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg2;
  } in
  let received_ev2 = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg2;
  } in
  lemma_protected_handshake_event_projection_pairs_after_server_write_client_read_install_and_next_head_with_tails
    server
    client
    server_after_install
    client_after_install
    server_after0
    client_after0
    server_after1
    client_after1
    server_material
    client_material
    sent_msg0
    received_msg0
    sent_msg1
    received_msg1
    (server_skip_ev :: sent_ev2 :: server_rest)
    (client_skip_ev :: received_ev2 :: client_rest)
    server_raw_sent
    server_raw_received
    client_raw_sent
    client_raw_received
    server_final
    client_final;
  eliminate exists
    (pair0:protected_message_replay)
    (pair1:protected_message_replay)
    (server_tail_sent0:B.bytes)
    (server_tail_received0:B.bytes)
    (client_tail_sent0:B.bytes)
    (client_tail_received0:B.bytes).
    pair0.pm_sender == server_after_install /\
    pair0.pm_receiver == client_after_install /\
    protected_handshake_event_projection_pair
        pair0
        sent_msg0
        received_msg0 /\
    pair1.pm_sender == server_after0 /\
    pair1.pm_receiver == client_after0 /\
    protected_handshake_event_projection_pair
        pair1
        sent_msg1
        received_msg1 /\
    write_read_record_material_aligned server_after1 client_after1 /\
    Seq.equal server_tail_sent0 client_tail_received0 /\
    conn_events_sent_seal_replay
        server_after1
        (server_skip_ev :: sent_ev2 :: server_rest)
        server_tail_sent0
        server_tail_received0
        server_final /\
    conn_events_received_decode_replay
        client_after1
        (client_skip_ev :: received_ev2 :: client_rest)
        client_tail_sent0
        client_tail_received0
        client_final
  with
  ( lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
        server_after1
        server_skip
        server_after_skip
        client_after1;
    lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
        server_after_skip
        client_after1
        client_skip
        client_after_skip;
    lemma_protected_handshake_event_projection_pair_after_both_skip_empty_heads_with_next_alignment_and_tails
        server_after1
        server_after_skip
        client_after1
        client_after_skip
        server_after2
        client_after2
        server_skip_ev
        client_skip_ev
        sent_msg2
        received_msg2
        server_rest
        client_rest
        server_tail_sent0
        server_tail_received0
        client_tail_sent0
        client_tail_received0
        server_final
        client_final;
    eliminate exists
        (pair2:protected_message_replay)
        (server_tail_sent2:B.bytes)
        (server_tail_received2:B.bytes)
        (client_tail_sent2:B.bytes)
        (client_tail_received2:B.bytes).
        pair2.pm_sender == server_after_skip /\
        pair2.pm_receiver == client_after_skip /\
        protected_handshake_event_projection_pair
          pair2
          sent_msg2
          received_msg2 /\
        write_read_record_material_aligned server_after2 client_after2 /\
        Seq.equal server_tail_sent2 client_tail_received2 /\
        conn_events_sent_seal_replay
          server_after2
          server_rest
          server_tail_sent2
          server_tail_received2
          server_final /\
        conn_events_received_decode_replay
          client_after2
          client_rest
          client_tail_sent2
          client_tail_received2
          client_final
    with
    ( introduce exists
          (pair0':protected_message_replay)
          (pair1':protected_message_replay)
          (pair2':protected_message_replay)
          (server_tail_sent:B.bytes)
          (server_tail_received:B.bytes)
          (client_tail_sent:B.bytes)
          (client_tail_received:B.bytes).
          pair0'.pm_sender == server_after_install /\
          pair0'.pm_receiver == client_after_install /\
          protected_handshake_event_projection_pair
            pair0'
            sent_msg0
            received_msg0 /\
          pair1'.pm_sender == server_after0 /\
          pair1'.pm_receiver == client_after0 /\
          protected_handshake_event_projection_pair
            pair1'
            sent_msg1
            received_msg1 /\
          pair2'.pm_sender == server_after_skip /\
          pair2'.pm_receiver == client_after_skip /\
          protected_handshake_event_projection_pair
            pair2'
            sent_msg2
            received_msg2 /\
          write_read_record_material_aligned server_after2 client_after2 /\
          Seq.equal server_tail_sent client_tail_received /\
          conn_events_sent_seal_replay
            server_after2
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          conn_events_received_decode_replay
            client_after2
            client_rest
            client_tail_sent
            client_tail_received
            client_final
        with
          pair0
          pair1
          pair2
          server_tail_sent2
          server_tail_received2
          client_tail_sent2
          client_tail_received2
        and () ) )

#restart-solver
#push-options "--z3rlimit 200"
let lemma_protected_handshake_event_projection_pairs_after_server_write_client_read_install_server_encrypted_flight_with_tails
  (server:connection_model)
  (client:connection_model)
  (server_after_install:connection_model)
  (client_after_install:connection_model)
  (server_after0:connection_model)
  (client_after0:connection_model)
  (server_after1:connection_model)
  (client_after1:connection_model)
  (server_after_auth_skip:connection_model)
  (client_after_auth_skip:connection_model)
  (server_after2:connection_model)
  (client_after2:connection_model)
  (client_after_verify_skip:connection_model)
  (server_after3:connection_model)
  (client_after3:connection_model)
  (server_auth_skip:local_event)
  (client_auth_skip:local_event)
  (client_verify_skip:local_event)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
        (requires
          (match
            server.model_handshake.hs_keys.ks_handshake_secret,
            client.model_handshake.hs_keys.ks_handshake_secret
          with
          | Some server_secret, Some client_secret ->
            Seq.equal server_secret client_secret
          | _, _ ->
            False) /\
          Seq.equal
            server.model_handshake.hs_transcript
            client.model_handshake.hs_transcript /\
          negotiated_aead_alg server.model_handshake ==
            negotiated_aead_alg client.model_handshake /\
          local_event_does_not_install_record_keys server_auth_skip /\
          local_event_does_not_install_record_keys client_auth_skip /\
          local_event_does_not_install_record_keys client_verify_skip /\
          Seq.equal server_raw_sent client_raw_received /\
          protected_handshake_wire_round_trip_message sent_msg0 /\
          protected_handshake_wire_round_trip_message received_msg0 /\
          protected_handshake_wire_round_trip_message sent_msg1 /\
          protected_handshake_wire_round_trip_message received_msg1 /\
          protected_handshake_wire_round_trip_message sent_msg2 /\
          protected_handshake_wire_round_trip_message received_msg2 /\
          protected_handshake_wire_round_trip_message sent_msg3 /\
          protected_handshake_wire_round_trip_message received_msg3 /\
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
              })) == Some server_after_install /\
          step_model
            client
            (ConnLocalEvent
              (LocalInstallTrafficKeys {
                install_epoch = TrafficHandshake;
                install_direction = TrafficRead;
                install_material = client_material;
              })) == Some client_after_install /\
          step_model
            server_after_install
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg0;
            }) == Some server_after0 /\
          step_model
            client_after_install
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg0;
            }) == Some client_after0 /\
          server_after0.model_record.record_write ==
            R.next_seq server_after_install.model_record.record_write /\
          client_after0.model_record.record_read ==
            R.next_seq client_after_install.model_record.record_read /\
          step_model
            server_after0
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg1;
            }) == Some server_after1 /\
          step_model
            client_after0
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg1;
            }) == Some client_after1 /\
          server_after1.model_record.record_write ==
            R.next_seq server_after0.model_record.record_write /\
          client_after1.model_record.record_read ==
            R.next_seq client_after0.model_record.record_read /\
          step_model server_after1 (ConnLocalEvent server_auth_skip) ==
            Some server_after_auth_skip /\
          step_model client_after1 (ConnLocalEvent client_auth_skip) ==
            Some client_after_auth_skip /\
          step_model
            server_after_auth_skip
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg2;
            }) == Some server_after2 /\
          step_model
            client_after_auth_skip
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg2;
            }) == Some client_after2 /\
          server_after2.model_record.record_write ==
            R.next_seq server_after_auth_skip.model_record.record_write /\
          client_after2.model_record.record_read ==
            R.next_seq client_after_auth_skip.model_record.record_read /\
          step_model client_after2 (ConnLocalEvent client_verify_skip) ==
            Some client_after_verify_skip /\
          step_model
            server_after2
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg3;
            }) == Some server_after3 /\
          step_model
            client_after_verify_skip
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg3;
            }) == Some client_after3 /\
          server_after3.model_record.record_write ==
            R.next_seq server_after2.model_record.record_write /\
          client_after3.model_record.record_read ==
            R.next_seq client_after_verify_skip.model_record.record_read /\
          conn_events_sent_seal_replay
            server
            (ConnLocalEvent
              (LocalInstallTrafficKeysForRole {
                install_role = ServerEndpoint;
                install_payload = {
                  install_epoch = TrafficHandshake;
                  install_direction = TrafficWrite;
                  install_material = server_material;
                };
              }) :: ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake sent_msg0;
              } :: ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake sent_msg1;
              } :: ConnLocalEvent server_auth_skip :: ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake sent_msg2;
              } :: ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake sent_msg3;
              } :: server_rest)
            server_raw_sent
            server_raw_received
            server_final /\
          conn_events_received_decode_replay
            client
            (ConnLocalEvent
              (LocalInstallTrafficKeys {
                install_epoch = TrafficHandshake;
                install_direction = TrafficRead;
                install_material = client_material;
              }) :: ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake received_msg0;
              } :: ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake received_msg1;
              } :: ConnLocalEvent client_auth_skip :: ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake received_msg2;
              } :: ConnLocalEvent client_verify_skip :: ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake received_msg3;
              } :: client_rest)
            client_raw_sent
            client_raw_received
            client_final)
        (ensures
          exists pair0 pair1 pair2 pair3 server_tail_sent server_tail_received
            client_tail_sent client_tail_received.
            pair0.pm_sender == server_after_install /\
            pair0.pm_receiver == client_after_install /\
            protected_handshake_event_projection_pair
              pair0
              sent_msg0
              received_msg0 /\
            pair1.pm_sender == server_after0 /\
            pair1.pm_receiver == client_after0 /\
            protected_handshake_event_projection_pair
              pair1
              sent_msg1
              received_msg1 /\
            pair2.pm_sender == server_after_auth_skip /\
            pair2.pm_receiver == client_after_auth_skip /\
            protected_handshake_event_projection_pair
              pair2
              sent_msg2
              received_msg2 /\
            pair3.pm_sender == server_after2 /\
            pair3.pm_receiver == client_after_verify_skip /\
            protected_handshake_event_projection_pair
              pair3
              sent_msg3
              received_msg3 /\
            write_read_record_material_aligned server_after3 client_after3 /\
            Seq.equal server_tail_sent client_tail_received /\
            conn_events_sent_seal_replay
              server_after3
              server_rest
              server_tail_sent
              server_tail_received
              server_final /\
            conn_events_received_decode_replay
              client_after3
              client_rest
              client_tail_sent
              client_tail_received
              client_final)
=
  let sent_ev3 = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg3;
  } in
  let client_verify_skip_ev = ConnLocalEvent client_verify_skip in
  let received_ev3 = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg3;
  } in
  lemma_protected_handshake_event_projection_pairs_after_server_write_client_read_install_two_heads_then_both_non_install_local_heads_with_next_alignment_and_tails
    server
    client
    server_after_install
    client_after_install
    server_after0
    client_after0
    server_after1
    client_after1
    server_after_auth_skip
    client_after_auth_skip
    server_after2
    client_after2
    server_auth_skip
    client_auth_skip
    server_material
    client_material
    sent_msg0
    received_msg0
    sent_msg1
    received_msg1
    sent_msg2
    received_msg2
    (sent_ev3 :: server_rest)
    (client_verify_skip_ev :: received_ev3 :: client_rest)
    server_raw_sent
    server_raw_received
    client_raw_sent
    client_raw_received
    server_final
    client_final;
  eliminate exists
    (pair0:protected_message_replay)
    (pair1:protected_message_replay)
    (pair2:protected_message_replay)
    (server_tail_sent0:B.bytes)
    (server_tail_received0:B.bytes)
    (client_tail_sent0:B.bytes)
    (client_tail_received0:B.bytes).
    pair0.pm_sender == server_after_install /\
    pair0.pm_receiver == client_after_install /\
    protected_handshake_event_projection_pair
        pair0
        sent_msg0
        received_msg0 /\
    pair1.pm_sender == server_after0 /\
    pair1.pm_receiver == client_after0 /\
    protected_handshake_event_projection_pair
        pair1
        sent_msg1
        received_msg1 /\
    pair2.pm_sender == server_after_auth_skip /\
    pair2.pm_receiver == client_after_auth_skip /\
    protected_handshake_event_projection_pair
        pair2
        sent_msg2
        received_msg2 /\
    write_read_record_material_aligned server_after2 client_after2 /\
    Seq.equal server_tail_sent0 client_tail_received0 /\
    conn_events_sent_seal_replay
        server_after2
        (sent_ev3 :: server_rest)
        server_tail_sent0
        server_tail_received0
        server_final /\
    conn_events_received_decode_replay
        client_after2
        (client_verify_skip_ev :: received_ev3 :: client_rest)
        client_tail_sent0
        client_tail_received0
        client_final
  with
  ( lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
      server_after2
      client_after2
      client_verify_skip
      client_after_verify_skip;
    lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head_with_next_alignment_and_tails
      server_after2
      client_after2
      client_after_verify_skip
      server_after3
      client_after3
      client_verify_skip_ev
      sent_msg3
      received_msg3
      server_rest
      client_rest
      server_tail_sent0
      server_tail_received0
      client_tail_sent0
      client_tail_received0
      server_final
      client_final;
    eliminate exists
        (pair3:protected_message_replay)
        (server_tail_sent3:B.bytes)
        (server_tail_received3:B.bytes)
        (client_tail_sent3:B.bytes)
        (client_tail_received3:B.bytes).
        pair3.pm_sender == server_after2 /\
        pair3.pm_receiver == client_after_verify_skip /\
        protected_handshake_event_projection_pair
          pair3
          sent_msg3
          received_msg3 /\
        write_read_record_material_aligned server_after3 client_after3 /\
        Seq.equal server_tail_sent3 client_tail_received3 /\
        conn_events_sent_seal_replay
          server_after3
          server_rest
          server_tail_sent3
          server_tail_received3
          server_final /\
        conn_events_received_decode_replay
          client_after3
          client_rest
          client_tail_sent3
          client_tail_received3
          client_final
    with
    ( introduce exists
          (pair0':protected_message_replay)
          (pair1':protected_message_replay)
          (pair2':protected_message_replay)
          (pair3':protected_message_replay)
          (server_tail_sent:B.bytes)
          (server_tail_received:B.bytes)
          (client_tail_sent:B.bytes)
          (client_tail_received:B.bytes).
          pair0'.pm_sender == server_after_install /\
          pair0'.pm_receiver == client_after_install /\
          protected_handshake_event_projection_pair
            pair0'
            sent_msg0
            received_msg0 /\
          pair1'.pm_sender == server_after0 /\
          pair1'.pm_receiver == client_after0 /\
          protected_handshake_event_projection_pair
            pair1'
            sent_msg1
            received_msg1 /\
          pair2'.pm_sender == server_after_auth_skip /\
          pair2'.pm_receiver == client_after_auth_skip /\
          protected_handshake_event_projection_pair
            pair2'
            sent_msg2
            received_msg2 /\
          pair3'.pm_sender == server_after2 /\
          pair3'.pm_receiver == client_after_verify_skip /\
          protected_handshake_event_projection_pair
            pair3'
            sent_msg3
            received_msg3 /\
          write_read_record_material_aligned server_after3 client_after3 /\
          Seq.equal server_tail_sent client_tail_received /\
          conn_events_sent_seal_replay
            server_after3
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          conn_events_received_decode_replay
            client_after3
            client_rest
            client_tail_sent
            client_tail_received
            client_final
        with
          pair0
          pair1
          pair2
          pair3
          server_tail_sent3
          server_tail_received3
          client_tail_sent3
          client_tail_received3
        and () ) )
#pop-options
 
#push-options "--z3rlimit 100"
let lemma_protected_handshake_event_projection_pairs_server_encrypted_flight_after_installs_with_tails
  (server:connection_model)
  (client:connection_model)
  (server_after0:connection_model)
  (client_after0:connection_model)
  (server_after1:connection_model)
  (client_after1:connection_model)
  (server_after_auth_skip:connection_model)
  (client_after_auth_skip:connection_model)
  (server_after2:connection_model)
  (client_after2:connection_model)
  (client_after_verify_skip:connection_model)
  (server_after3:connection_model)
  (client_after3:connection_model)
  (server_auth_skip:local_event)
  (client_auth_skip:local_event)
  (client_verify_skip:local_event)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned server client /\
        local_event_does_not_install_record_keys server_auth_skip /\
        local_event_does_not_install_record_keys client_auth_skip /\
        local_event_does_not_install_record_keys client_verify_skip /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg0 /\
        protected_handshake_wire_round_trip_message received_msg0 /\
        protected_handshake_wire_round_trip_message sent_msg1 /\
        protected_handshake_wire_round_trip_message received_msg1 /\
        protected_handshake_wire_round_trip_message sent_msg2 /\
        protected_handshake_wire_round_trip_message received_msg2 /\
        protected_handshake_wire_round_trip_message sent_msg3 /\
        protected_handshake_wire_round_trip_message received_msg3 /\
        step_model
          server
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        step_model
          client
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        server_after0.model_record.record_write ==
          R.next_seq server.model_record.record_write /\
        client_after0.model_record.record_read ==
          R.next_seq client.model_record.record_read /\
        step_model
          server_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        step_model
          client_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        server_after1.model_record.record_write ==
          R.next_seq server_after0.model_record.record_write /\
        client_after1.model_record.record_read ==
          R.next_seq client_after0.model_record.record_read /\
        step_model server_after1 (ConnLocalEvent server_auth_skip) ==
          Some server_after_auth_skip /\
        step_model client_after1 (ConnLocalEvent client_auth_skip) ==
          Some client_after_auth_skip /\
        step_model
          server_after_auth_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        step_model
          client_after_auth_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        server_after2.model_record.record_write ==
          R.next_seq server_after_auth_skip.model_record.record_write /\
        client_after2.model_record.record_read ==
          R.next_seq client_after_auth_skip.model_record.record_read /\
        step_model client_after2 (ConnLocalEvent client_verify_skip) ==
          Some client_after_verify_skip /\
        step_model
          server_after2
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg3;
          }) == Some server_after3 /\
        step_model
          client_after_verify_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg3;
          }) == Some client_after3 /\
        server_after3.model_record.record_write ==
          R.next_seq server_after2.model_record.record_write /\
        client_after3.model_record.record_read ==
          R.next_seq client_after_verify_skip.model_record.record_read /\
        conn_events_sent_seal_replay
          server
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          } :: ConnLocalEvent server_auth_skip :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg3;
          } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        conn_events_received_decode_replay
          client
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          } :: ConnLocalEvent client_auth_skip :: ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          } :: ConnLocalEvent client_verify_skip :: ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg3;
          } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final)
      (ensures
        exists pair0 pair1 pair2 pair3 server_tail_sent server_tail_received
          client_tail_sent client_tail_received.
          pair0.pm_sender == server /\
          pair0.pm_receiver == client /\
          protected_handshake_event_projection_pair
            pair0
            sent_msg0
            received_msg0 /\
          pair1.pm_sender == server_after0 /\
          pair1.pm_receiver == client_after0 /\
          protected_handshake_event_projection_pair
            pair1
            sent_msg1
            received_msg1 /\
          pair2.pm_sender == server_after_auth_skip /\
          pair2.pm_receiver == client_after_auth_skip /\
          protected_handshake_event_projection_pair
            pair2
            sent_msg2
            received_msg2 /\
          pair3.pm_sender == server_after2 /\
          pair3.pm_receiver == client_after_verify_skip /\
          protected_handshake_event_projection_pair
            pair3
            sent_msg3
            received_msg3 /\
          write_read_record_material_aligned server_after3 client_after3 /\
          Seq.equal server_tail_sent client_tail_received /\
          conn_events_sent_seal_replay
            server_after3
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          conn_events_received_decode_replay
            client_after3
            client_rest
            client_tail_sent
            client_tail_received
            client_final)
=
  let sent_ev3 =
    ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake sent_msg3;
    } in
  let client_verify_skip_ev = ConnLocalEvent client_verify_skip in
  let received_ev3 =
    ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake received_msg3;
    } in
  lemma_protected_handshake_event_projection_pairs_from_two_heads_then_both_non_install_local_heads_with_next_alignment_and_tails
    server
    client
    server_after0
    client_after0
    server_after1
    client_after1
    server_after_auth_skip
    client_after_auth_skip
    server_after2
    client_after2
    server_auth_skip
    client_auth_skip
    sent_msg0
    received_msg0
    sent_msg1
    received_msg1
    sent_msg2
    received_msg2
    (sent_ev3 :: server_rest)
    (client_verify_skip_ev :: received_ev3 :: client_rest)
    server_raw_sent
    server_raw_received
    client_raw_sent
    client_raw_received
    server_final
    client_final;
  eliminate exists
    (pair0:protected_message_replay)
    (pair1:protected_message_replay)
    (pair2:protected_message_replay)
    (server_tail_sent0:B.bytes)
    (server_tail_received0:B.bytes)
    (client_tail_sent0:B.bytes)
    (client_tail_received0:B.bytes).
    pair0.pm_sender == server /\
    pair0.pm_receiver == client /\
    protected_handshake_event_projection_pair
      pair0
      sent_msg0
      received_msg0 /\
    pair1.pm_sender == server_after0 /\
    pair1.pm_receiver == client_after0 /\
    protected_handshake_event_projection_pair
      pair1
      sent_msg1
      received_msg1 /\
    pair2.pm_sender == server_after_auth_skip /\
    pair2.pm_receiver == client_after_auth_skip /\
    protected_handshake_event_projection_pair
      pair2
      sent_msg2
      received_msg2 /\
    write_read_record_material_aligned server_after1 client_after1 /\
    write_read_record_material_aligned server_after2 client_after2 /\
    Seq.equal server_tail_sent0 client_tail_received0 /\
    conn_events_sent_seal_replay
      server_after2
      (sent_ev3 :: server_rest)
      server_tail_sent0
      server_tail_received0
      server_final /\
    conn_events_received_decode_replay
      client_after2
      (client_verify_skip_ev :: received_ev3 :: client_rest)
      client_tail_sent0
      client_tail_received0
      client_final
  with
  (
    lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
      server_after2
      client_after2
      client_verify_skip
      client_after_verify_skip;
    lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head_with_next_alignment_and_tails
      server_after2
      client_after2
      client_after_verify_skip
      server_after3
      client_after3
      client_verify_skip_ev
      sent_msg3
      received_msg3
      server_rest
      client_rest
      server_tail_sent0
      server_tail_received0
      client_tail_sent0
      client_tail_received0
      server_final
      client_final;
    eliminate exists
      (pair3:protected_message_replay)
      (server_tail_sent3:B.bytes)
      (server_tail_received3:B.bytes)
      (client_tail_sent3:B.bytes)
      (client_tail_received3:B.bytes).
      pair3.pm_sender == server_after2 /\
      pair3.pm_receiver == client_after_verify_skip /\
      protected_handshake_event_projection_pair
        pair3
        sent_msg3
        received_msg3 /\
      write_read_record_material_aligned server_after3 client_after3 /\
      Seq.equal server_tail_sent3 client_tail_received3 /\
      conn_events_sent_seal_replay
        server_after3
        server_rest
        server_tail_sent3
        server_tail_received3
        server_final /\
      conn_events_received_decode_replay
        client_after3
        client_rest
        client_tail_sent3
        client_tail_received3
        client_final
    with
    ( introduce exists
        (pair0':protected_message_replay)
        (pair1':protected_message_replay)
        (pair2':protected_message_replay)
        (pair3':protected_message_replay)
        (server_tail_sent:B.bytes)
        (server_tail_received:B.bytes)
        (client_tail_sent:B.bytes)
        (client_tail_received:B.bytes).
        pair0'.pm_sender == server /\
        pair0'.pm_receiver == client /\
        protected_handshake_event_projection_pair
          pair0'
          sent_msg0
          received_msg0 /\
        pair1'.pm_sender == server_after0 /\
        pair1'.pm_receiver == client_after0 /\
        protected_handshake_event_projection_pair
          pair1'
          sent_msg1
          received_msg1 /\
        pair2'.pm_sender == server_after_auth_skip /\
        pair2'.pm_receiver == client_after_auth_skip /\
        protected_handshake_event_projection_pair
          pair2'
          sent_msg2
          received_msg2 /\
        pair3'.pm_sender == server_after2 /\
        pair3'.pm_receiver == client_after_verify_skip /\
        protected_handshake_event_projection_pair
          pair3'
          sent_msg3
          received_msg3 /\
        write_read_record_material_aligned server_after3 client_after3 /\
        Seq.equal server_tail_sent client_tail_received /\
        conn_events_sent_seal_replay
          server_after3
          server_rest
          server_tail_sent
          server_tail_received
          server_final /\
        conn_events_received_decode_replay
          client_after3
          client_rest
          client_tail_sent
          client_tail_received
          client_final
      with pair0 pair1 pair2 pair3
        server_tail_sent3 server_tail_received3
        client_tail_sent3 client_tail_received3
      and () )
  )

#pop-options
#restart-solver
let lemma_server_encrypted_flight_preserves_client_to_server_stream_with_tails
  (server:connection_model)
  (client:connection_model)
  (server_after_install:connection_model)
  (client_after_install:connection_model)
  (server_after0:connection_model)
  (client_after0:connection_model)
  (server_after1:connection_model)
  (client_after1:connection_model)
  (server_after_auth_skip:connection_model)
  (client_after_auth_skip:connection_model)
  (server_after2:connection_model)
  (client_after2:connection_model)
  (client_after_verify_skip:connection_model)
  (server_after3:connection_model)
  (client_after3:connection_model)
  (server_auth_skip:local_event)
  (client_auth_skip:local_event)
  (client_verify_skip:local_event)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        Seq.equal client_raw_sent server_raw_received /\
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
            })) == Some server_after_install /\
        step_model
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            })) == Some client_after_install /\
        step_model
          server_after_install
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        step_model
          client_after_install
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        step_model
          server_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        step_model
          client_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        step_model server_after1 (ConnLocalEvent server_auth_skip) ==
          Some server_after_auth_skip /\
        step_model client_after1 (ConnLocalEvent client_auth_skip) ==
          Some client_after_auth_skip /\
        step_model
          server_after_auth_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        step_model
          client_after_auth_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        step_model client_after2 (ConnLocalEvent client_verify_skip) ==
          Some client_after_verify_skip /\
        step_model
          server_after2
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg3;
          }) == Some server_after3 /\
        step_model
          client_after_verify_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg3;
          }) == Some client_after3 /\
        conn_events_sent_seal_replay
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = server_material;
              };
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg0;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg1;
            } :: ConnLocalEvent server_auth_skip :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg2;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg3;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        conn_events_received_decode_replay
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg0;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg1;
            } :: ConnLocalEvent client_auth_skip :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg2;
            } :: ConnLocalEvent client_verify_skip :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg3;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final)
      (ensures
        exists server_tail_sent server_tail_received
          client_tail_sent client_tail_received.
          Seq.equal client_tail_sent server_tail_received /\
          conn_events_sent_seal_replay
            server_after3
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          conn_events_received_decode_replay
            client_after3
            client_rest
            client_tail_sent
            client_tail_received
            client_final)
=
  let server_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeysForRole {
        install_role = ServerEndpoint;
        install_payload = {
          install_epoch = TrafficHandshake;
          install_direction = TrafficWrite;
          install_material = server_material;
        };
      }) in
  let client_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeys {
        install_epoch = TrafficHandshake;
        install_direction = TrafficRead;
        install_material = client_material;
      }) in
  let sent_ev0 = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg0;
  } in
  let received_ev0 = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg0;
  } in
  let sent_ev1 = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg1;
  } in
  let received_ev1 = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg1;
  } in
  let server_auth_ev = ConnLocalEvent server_auth_skip in
  let client_auth_ev = ConnLocalEvent client_auth_skip in
  let sent_ev2 = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg2;
  } in
  let received_ev2 = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg2;
  } in
  let client_verify_ev = ConnLocalEvent client_verify_skip in
  let sent_ev3 = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg3;
  } in
  let received_ev3 = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg3;
  } in
  lemma_sent_received_replays_skip_zero_opposite_heads_preserve_peer_stream
    server
    client
    server_install_ev
    client_install_ev
    (sent_ev0 :: sent_ev1 :: server_auth_ev :: sent_ev2 :: sent_ev3 :: server_rest)
    (received_ev0 :: received_ev1 :: client_auth_ev :: received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
    server_raw_sent
    server_raw_received
    client_raw_sent
    client_raw_received
    server_final
    client_final;
  eliminate exists
    (server1:connection_model)
    (client1:connection_model)
    (server_sent1:B.bytes)
    (server_received1:B.bytes)
    (client_sent1:B.bytes)
    (client_received1:B.bytes).
    legal_event server server_install_ev /\
    step_model server server_install_ev == Some server1 /\
    legal_event client client_install_ev /\
    step_model client client_install_ev == Some client1 /\
    Seq.equal client_sent1 server_received1 /\
    conn_events_sent_seal_replay
      server1
      (sent_ev0 :: sent_ev1 :: server_auth_ev :: sent_ev2 :: sent_ev3 :: server_rest)
      server_sent1
      server_received1
      server_final /\
    conn_events_received_decode_replay
      client1
      (received_ev0 :: received_ev1 :: client_auth_ev :: received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
      client_sent1
      client_received1
      client_final
  with
  ( assert (server1 == server_after_install);
    assert (client1 == client_after_install);
    lemma_sent_received_replays_skip_zero_opposite_heads_preserve_peer_stream
      server_after_install
      client_after_install
      sent_ev0
      received_ev0
      (sent_ev1 :: server_auth_ev :: sent_ev2 :: sent_ev3 :: server_rest)
      (received_ev1 :: client_auth_ev :: received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
      server_sent1
      server_received1
      client_sent1
      client_received1
      server_final
      client_final;
    eliminate exists
      (server2:connection_model)
      (client2:connection_model)
      (server_sent2:B.bytes)
      (server_received2:B.bytes)
      (client_sent2:B.bytes)
      (client_received2:B.bytes).
      legal_event server_after_install sent_ev0 /\
      step_model server_after_install sent_ev0 == Some server2 /\
      legal_event client_after_install received_ev0 /\
      step_model client_after_install received_ev0 == Some client2 /\
      Seq.equal client_sent2 server_received2 /\
      conn_events_sent_seal_replay
        server2
        (sent_ev1 :: server_auth_ev :: sent_ev2 :: sent_ev3 :: server_rest)
        server_sent2
        server_received2
        server_final /\
      conn_events_received_decode_replay
        client2
        (received_ev1 :: client_auth_ev :: received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
        client_sent2
        client_received2
        client_final
    with
    ( assert (server2 == server_after0);
      assert (client2 == client_after0);
      lemma_sent_received_replays_skip_zero_opposite_heads_preserve_peer_stream
        server_after0
        client_after0
        sent_ev1
        received_ev1
        (server_auth_ev :: sent_ev2 :: sent_ev3 :: server_rest)
        (client_auth_ev :: received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
        server_sent2
        server_received2
        client_sent2
        client_received2
        server_final
        client_final;
      eliminate exists
        (server3:connection_model)
        (client3:connection_model)
        (server_sent3:B.bytes)
        (server_received3:B.bytes)
        (client_sent3:B.bytes)
        (client_received3:B.bytes).
        legal_event server_after0 sent_ev1 /\
        step_model server_after0 sent_ev1 == Some server3 /\
        legal_event client_after0 received_ev1 /\
        step_model client_after0 received_ev1 == Some client3 /\
        Seq.equal client_sent3 server_received3 /\
        conn_events_sent_seal_replay
          server3
          (server_auth_ev :: sent_ev2 :: sent_ev3 :: server_rest)
          server_sent3
          server_received3
          server_final /\
        conn_events_received_decode_replay
          client3
          (client_auth_ev :: received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
          client_sent3
          client_received3
          client_final
      with
      ( assert (server3 == server_after1);
        assert (client3 == client_after1);
        lemma_sent_received_replays_skip_zero_opposite_heads_preserve_peer_stream
          server_after1
          client_after1
          server_auth_ev
          client_auth_ev
          (sent_ev2 :: sent_ev3 :: server_rest)
          (received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
          server_sent3
          server_received3
          client_sent3
          client_received3
          server_final
          client_final;
        eliminate exists
          (server4:connection_model)
          (client4:connection_model)
          (server_sent4:B.bytes)
          (server_received4:B.bytes)
          (client_sent4:B.bytes)
          (client_received4:B.bytes).
          legal_event server_after1 server_auth_ev /\
          step_model server_after1 server_auth_ev == Some server4 /\
          legal_event client_after1 client_auth_ev /\
          step_model client_after1 client_auth_ev == Some client4 /\
          Seq.equal client_sent4 server_received4 /\
          conn_events_sent_seal_replay
            server4
            (sent_ev2 :: sent_ev3 :: server_rest)
            server_sent4
            server_received4
            server_final /\
          conn_events_received_decode_replay
            client4
            (received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
            client_sent4
            client_received4
            client_final
        with
        ( assert (server4 == server_after_auth_skip);
          assert (client4 == client_after_auth_skip);
          lemma_sent_received_replays_skip_zero_opposite_heads_preserve_peer_stream
            server_after_auth_skip
            client_after_auth_skip
            sent_ev2
            received_ev2
            (sent_ev3 :: server_rest)
            (client_verify_ev :: received_ev3 :: client_rest)
            server_sent4
            server_received4
            client_sent4
            client_received4
            server_final
            client_final;
          eliminate exists
            (server5:connection_model)
            (client5:connection_model)
            (server_sent5:B.bytes)
            (server_received5:B.bytes)
            (client_sent5:B.bytes)
            (client_received5:B.bytes).
            legal_event server_after_auth_skip sent_ev2 /\
            step_model server_after_auth_skip sent_ev2 == Some server5 /\
            legal_event client_after_auth_skip received_ev2 /\
            step_model client_after_auth_skip received_ev2 == Some client5 /\
            Seq.equal client_sent5 server_received5 /\
            conn_events_sent_seal_replay
              server5
              (sent_ev3 :: server_rest)
              server_sent5
              server_received5
              server_final /\
            conn_events_received_decode_replay
              client5
              (client_verify_ev :: received_ev3 :: client_rest)
              client_sent5
              client_received5
              client_final
          with
          ( assert (server5 == server_after2);
            assert (client5 == client_after2);
            lemma_received_replay_skip_zero_sent_head_preserves_peer_stream
              client_after2
              client_verify_ev
              (received_ev3 :: client_rest)
              client_sent5
              client_received5
              server_received5
              client_final;
            eliminate exists
              (client6:connection_model)
              (client_sent6:B.bytes)
              (client_received6:B.bytes).
              legal_event client_after2 client_verify_ev /\
              step_model client_after2 client_verify_ev == Some client6 /\
              Seq.equal client_sent6 server_received5 /\
              conn_events_received_decode_replay
                client6
                (received_ev3 :: client_rest)
                client_sent6
                client_received6
                client_final
            with
            ( assert (client6 == client_after_verify_skip);
              lemma_sent_received_replays_skip_zero_opposite_heads_preserve_peer_stream
                server_after2
                client_after_verify_skip
                sent_ev3
                received_ev3
                server_rest
                client_rest
                server_sent5
                server_received5
                client_sent6
                client_received6
                server_final
                client_final;
              eliminate exists
                (server6:connection_model)
                (client7:connection_model)
                (server_tail_sent:B.bytes)
                (server_tail_received:B.bytes)
                (client_tail_sent:B.bytes)
                (client_tail_received:B.bytes).
                legal_event server_after2 sent_ev3 /\
                step_model server_after2 sent_ev3 == Some server6 /\
                legal_event client_after_verify_skip received_ev3 /\
                step_model client_after_verify_skip received_ev3 == Some client7 /\
                Seq.equal client_tail_sent server_tail_received /\
                conn_events_sent_seal_replay
                  server6
                  server_rest
                  server_tail_sent
                  server_tail_received
                  server_final /\
                conn_events_received_decode_replay
                  client7
                  client_rest
                  client_tail_sent
                  client_tail_received
                  client_final
              with
              ( assert (server6 == server_after3);
                assert (client7 == client_after3);
                introduce exists
                  (server_tail_sent':B.bytes)
                  (server_tail_received':B.bytes)
                  (client_tail_sent':B.bytes)
                  (client_tail_received':B.bytes).
                  Seq.equal client_tail_sent' server_tail_received' /\
                  conn_events_sent_seal_replay
                    server_after3
                    server_rest
                    server_tail_sent'
                    server_tail_received'
                    server_final /\
                  conn_events_received_decode_replay
                    client_after3
                    client_rest
                    client_tail_sent'
                    client_tail_received'
                    client_final
                with
                  server_tail_sent
                  server_tail_received
                  client_tail_sent
                  client_tail_received
                and () ) ) ) ) ) ) )

let lemma_server_encrypted_flight_preserves_client_to_server_replay_tails_with_tails
  (server:connection_model)
  (client:connection_model)
  (server_after_install:connection_model)
  (client_after_install:connection_model)
  (server_after0:connection_model)
  (client_after0:connection_model)
  (server_after1:connection_model)
  (client_after1:connection_model)
  (server_after_auth_skip:connection_model)
  (client_after_auth_skip:connection_model)
  (server_after2:connection_model)
  (client_after2:connection_model)
  (client_after_verify_skip:connection_model)
  (server_after3:connection_model)
  (client_after3:connection_model)
  (server_auth_skip:local_event)
  (client_auth_skip:local_event)
  (client_verify_skip:local_event)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        Seq.equal client_raw_sent server_raw_received /\
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
            })) == Some server_after_install /\
        step_model
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            })) == Some client_after_install /\
        step_model
          server_after_install
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        step_model
          client_after_install
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        step_model
          server_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        step_model
          client_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        step_model server_after1 (ConnLocalEvent server_auth_skip) ==
          Some server_after_auth_skip /\
        step_model client_after1 (ConnLocalEvent client_auth_skip) ==
          Some client_after_auth_skip /\
        step_model
          server_after_auth_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        step_model
          client_after_auth_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        step_model client_after2 (ConnLocalEvent client_verify_skip) ==
          Some client_after_verify_skip /\
        step_model
          server_after2
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg3;
          }) == Some server_after3 /\
        step_model
          client_after_verify_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg3;
          }) == Some client_after3 /\
        conn_events_sent_seal_replay
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg0;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg1;
            } :: ConnLocalEvent client_auth_skip :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg2;
            } :: ConnLocalEvent client_verify_skip :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg3;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final /\
        conn_events_received_decode_replay
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = server_material;
              };
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg0;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg1;
            } :: ConnLocalEvent server_auth_skip :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg2;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg3;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final)
      (ensures
        exists client_tail_sent client_tail_received
          server_tail_sent server_tail_received.
          Seq.equal client_tail_sent server_tail_received /\
          conn_events_sent_seal_replay
            client_after3
            client_rest
            client_tail_sent
            client_tail_received
            client_final /\
          conn_events_received_decode_replay
            server_after3
            server_rest
            server_tail_sent
            server_tail_received
            server_final)
=
  let server_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeysForRole {
        install_role = ServerEndpoint;
        install_payload = {
          install_epoch = TrafficHandshake;
          install_direction = TrafficWrite;
          install_material = server_material;
        };
      }) in
  let client_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeys {
        install_epoch = TrafficHandshake;
        install_direction = TrafficRead;
        install_material = client_material;
      }) in
  let sent_ev0 = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg0;
  } in
  let received_ev0 = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg0;
  } in
  let sent_ev1 = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg1;
  } in
  let received_ev1 = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg1;
  } in
  let server_auth_ev = ConnLocalEvent server_auth_skip in
  let client_auth_ev = ConnLocalEvent client_auth_skip in
  let sent_ev2 = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg2;
  } in
  let received_ev2 = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg2;
  } in
  let client_verify_ev = ConnLocalEvent client_verify_skip in
  let sent_ev3 = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg3;
  } in
  let received_ev3 = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg3;
  } in
  lemma_sent_received_replays_skip_empty_opposite_heads_preserve_peer_stream
    client
    server
    client_install_ev
    server_install_ev
    (received_ev0 :: received_ev1 :: client_auth_ev :: received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
    (sent_ev0 :: sent_ev1 :: server_auth_ev :: sent_ev2 :: sent_ev3 :: server_rest)
    client_raw_sent
    client_raw_received
    server_raw_sent
    server_raw_received
    client_final
    server_final;
  eliminate exists
    (client1:connection_model)
    (server1:connection_model)
    (client_sent1:B.bytes)
    (client_received1:B.bytes)
    (server_sent1:B.bytes)
    (server_received1:B.bytes).
    legal_event client client_install_ev /\
    step_model client client_install_ev == Some client1 /\
    legal_event server server_install_ev /\
    step_model server server_install_ev == Some server1 /\
    Seq.equal client_sent1 server_received1 /\
    conn_events_sent_seal_replay
      client1
      (received_ev0 :: received_ev1 :: client_auth_ev :: received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
      client_sent1
      client_received1
      client_final /\
    conn_events_received_decode_replay
      server1
      (sent_ev0 :: sent_ev1 :: server_auth_ev :: sent_ev2 :: sent_ev3 :: server_rest)
      server_sent1
      server_received1
      server_final
  with
  ( assert (client1 == client_after_install);
    assert (server1 == server_after_install);
    lemma_sent_received_replays_skip_empty_opposite_heads_preserve_peer_stream
      client_after_install
      server_after_install
      received_ev0
      sent_ev0
      (received_ev1 :: client_auth_ev :: received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
      (sent_ev1 :: server_auth_ev :: sent_ev2 :: sent_ev3 :: server_rest)
      client_sent1
      client_received1
      server_sent1
      server_received1
      client_final
      server_final;
    eliminate exists
      (client2:connection_model)
      (server2:connection_model)
      (client_sent2:B.bytes)
      (client_received2:B.bytes)
      (server_sent2:B.bytes)
      (server_received2:B.bytes).
      legal_event client_after_install received_ev0 /\
      step_model client_after_install received_ev0 == Some client2 /\
      legal_event server_after_install sent_ev0 /\
      step_model server_after_install sent_ev0 == Some server2 /\
      Seq.equal client_sent2 server_received2 /\
      conn_events_sent_seal_replay
        client2
        (received_ev1 :: client_auth_ev :: received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
        client_sent2
        client_received2
        client_final /\
      conn_events_received_decode_replay
        server2
        (sent_ev1 :: server_auth_ev :: sent_ev2 :: sent_ev3 :: server_rest)
        server_sent2
        server_received2
        server_final
    with
    ( assert (client2 == client_after0);
      assert (server2 == server_after0);
      lemma_sent_received_replays_skip_empty_opposite_heads_preserve_peer_stream
        client_after0
        server_after0
        received_ev1
        sent_ev1
        (client_auth_ev :: received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
        (server_auth_ev :: sent_ev2 :: sent_ev3 :: server_rest)
        client_sent2
        client_received2
        server_sent2
        server_received2
        client_final
        server_final;
      eliminate exists
        (client3:connection_model)
        (server3:connection_model)
        (client_sent3:B.bytes)
        (client_received3:B.bytes)
        (server_sent3:B.bytes)
        (server_received3:B.bytes).
        legal_event client_after0 received_ev1 /\
        step_model client_after0 received_ev1 == Some client3 /\
        legal_event server_after0 sent_ev1 /\
        step_model server_after0 sent_ev1 == Some server3 /\
        Seq.equal client_sent3 server_received3 /\
        conn_events_sent_seal_replay
          client3
          (client_auth_ev :: received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
          client_sent3
          client_received3
          client_final /\
        conn_events_received_decode_replay
          server3
          (server_auth_ev :: sent_ev2 :: sent_ev3 :: server_rest)
          server_sent3
          server_received3
          server_final
      with
      ( assert (client3 == client_after1);
        assert (server3 == server_after1);
        lemma_sent_received_replays_skip_empty_opposite_heads_preserve_peer_stream
          client_after1
          server_after1
          client_auth_ev
          server_auth_ev
          (received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
          (sent_ev2 :: sent_ev3 :: server_rest)
          client_sent3
          client_received3
          server_sent3
          server_received3
          client_final
          server_final;
        eliminate exists
          (client4:connection_model)
          (server4:connection_model)
          (client_sent4:B.bytes)
          (client_received4:B.bytes)
          (server_sent4:B.bytes)
          (server_received4:B.bytes).
          legal_event client_after1 client_auth_ev /\
          step_model client_after1 client_auth_ev == Some client4 /\
          legal_event server_after1 server_auth_ev /\
          step_model server_after1 server_auth_ev == Some server4 /\
          Seq.equal client_sent4 server_received4 /\
          conn_events_sent_seal_replay
            client4
            (received_ev2 :: client_verify_ev :: received_ev3 :: client_rest)
            client_sent4
            client_received4
            client_final /\
          conn_events_received_decode_replay
            server4
            (sent_ev2 :: sent_ev3 :: server_rest)
            server_sent4
            server_received4
            server_final
        with
        ( assert (client4 == client_after_auth_skip);
          assert (server4 == server_after_auth_skip);
          lemma_sent_received_replays_skip_empty_opposite_heads_preserve_peer_stream
            client_after_auth_skip
            server_after_auth_skip
            received_ev2
            sent_ev2
            (client_verify_ev :: received_ev3 :: client_rest)
            (sent_ev3 :: server_rest)
            client_sent4
            client_received4
            server_sent4
            server_received4
            client_final
            server_final;
          eliminate exists
            (client5:connection_model)
            (server5:connection_model)
            (client_sent5:B.bytes)
            (client_received5:B.bytes)
            (server_sent5:B.bytes)
            (server_received5:B.bytes).
            legal_event client_after_auth_skip received_ev2 /\
            step_model client_after_auth_skip received_ev2 == Some client5 /\
            legal_event server_after_auth_skip sent_ev2 /\
            step_model server_after_auth_skip sent_ev2 == Some server5 /\
            Seq.equal client_sent5 server_received5 /\
            conn_events_sent_seal_replay
              client5
              (client_verify_ev :: received_ev3 :: client_rest)
              client_sent5
              client_received5
              client_final /\
            conn_events_received_decode_replay
              server5
              (sent_ev3 :: server_rest)
              server_sent5
              server_received5
              server_final
          with
          ( assert (client5 == client_after2);
            assert (server5 == server_after2);
            lemma_sent_replay_skip_empty_head_preserves_peer_stream
              client_after2
              client_verify_ev
              (received_ev3 :: client_rest)
              client_sent5
              client_received5
              server_received5
              client_final;
            eliminate exists
              (client6:connection_model)
              (client_sent6:B.bytes)
              (client_received6:B.bytes).
              legal_event client_after2 client_verify_ev /\
              step_model client_after2 client_verify_ev == Some client6 /\
              Seq.equal client_sent6 server_received5 /\
              conn_events_sent_seal_replay
                client6
                (received_ev3 :: client_rest)
                client_sent6
                client_received6
                client_final
            with
            ( assert (client6 == client_after_verify_skip);
              lemma_sent_received_replays_skip_empty_opposite_heads_preserve_peer_stream
                client_after_verify_skip
                server_after2
                received_ev3
                sent_ev3
                client_rest
                server_rest
                client_sent6
                client_received6
                server_sent5
                server_received5
                client_final
                server_final;
              eliminate exists
                (client7:connection_model)
                (server6:connection_model)
                (client_tail_sent:B.bytes)
                (client_tail_received:B.bytes)
                (server_tail_sent:B.bytes)
                (server_tail_received:B.bytes).
                legal_event client_after_verify_skip received_ev3 /\
                step_model client_after_verify_skip received_ev3 == Some client7 /\
                legal_event server_after2 sent_ev3 /\
                step_model server_after2 sent_ev3 == Some server6 /\
                Seq.equal client_tail_sent server_tail_received /\
                conn_events_sent_seal_replay
                  client7
                  client_rest
                  client_tail_sent
                  client_tail_received
                  client_final /\
                conn_events_received_decode_replay
                  server6
                  server_rest
                  server_tail_sent
                  server_tail_received
                  server_final
              with
              ( assert (client7 == client_after3);
                assert (server6 == server_after3);
                introduce exists
                  (client_tail_sent':B.bytes)
                  (client_tail_received':B.bytes)
                  (server_tail_sent':B.bytes)
                  (server_tail_received':B.bytes).
                  Seq.equal client_tail_sent' server_tail_received' /\
                  conn_events_sent_seal_replay
                    client_after3
                    client_rest
                    client_tail_sent'
                    client_tail_received'
                    client_final /\
                  conn_events_received_decode_replay
                    server_after3
                    server_rest
                    server_tail_sent'
                    server_tail_received'
                    server_final
                with
                  client_tail_sent
                  client_tail_received
                  server_tail_sent
                  server_tail_received
                and () ) ) ) ) ) ) )

#restart-solver
let lemma_server_encrypted_flight_produces_client_finished_replay_inputs_with_tails
  (server:connection_model)
  (client:connection_model)
  (server_after_install:connection_model)
  (client_after_install:connection_model)
  (server_after0:connection_model)
  (client_after0:connection_model)
  (server_after1:connection_model)
  (client_after1:connection_model)
  (server_after_auth_skip:connection_model)
  (client_after_auth_skip:connection_model)
  (server_after2:connection_model)
  (client_after2:connection_model)
  (client_after_verify_skip:connection_model)
  (server_after3:connection_model)
  (client_after3:connection_model)
  (server_auth_skip:local_event)
  (client_auth_skip:local_event)
  (client_verify_skip:local_event)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned client server /\
        local_event_does_not_install_record_keys server_auth_skip /\
        local_event_does_not_install_record_keys client_auth_skip /\
        local_event_does_not_install_record_keys client_verify_skip /\
        Seq.equal client_raw_sent server_raw_received /\
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
            })) == Some server_after_install /\
        step_model
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            })) == Some client_after_install /\
        step_model
          server_after_install
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        step_model
          client_after_install
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        step_model
          server_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        step_model
          client_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        step_model server_after1 (ConnLocalEvent server_auth_skip) ==
          Some server_after_auth_skip /\
        step_model client_after1 (ConnLocalEvent client_auth_skip) ==
          Some client_after_auth_skip /\
        step_model
          server_after_auth_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        step_model
          client_after_auth_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        step_model client_after2 (ConnLocalEvent client_verify_skip) ==
          Some client_after_verify_skip /\
        step_model
          server_after2
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg3;
          }) == Some server_after3 /\
        step_model
          client_after_verify_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg3;
          }) == Some client_after3 /\
        conn_events_sent_seal_replay
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg0;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg1;
            } :: ConnLocalEvent client_auth_skip :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg2;
            } :: ConnLocalEvent client_verify_skip :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg3;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final /\
        conn_events_received_decode_replay
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = server_material;
              };
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg0;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg1;
            } :: ConnLocalEvent server_auth_skip :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg2;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg3;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final)
      (ensures
        exists client_tail_sent client_tail_received
          server_tail_sent server_tail_received.
          write_read_record_material_aligned client_after3 server_after3 /\
          Seq.equal client_tail_sent server_tail_received /\
          conn_events_sent_seal_replay
            client_after3
            client_rest
            client_tail_sent
            client_tail_received
            client_final /\
          conn_events_received_decode_replay
            server_after3
            server_rest
            server_tail_sent
            server_tail_received
            server_final)
=
  lemma_server_encrypted_flight_preserves_client_to_server_replay_tails_with_tails
    server
    client
    server_after_install
    client_after_install
    server_after0
    client_after0
    server_after1
    client_after1
    server_after_auth_skip
    client_after_auth_skip
    server_after2
    client_after2
    client_after_verify_skip
    server_after3
    client_after3
    server_auth_skip
    client_auth_skip
    client_verify_skip
    server_material
    client_material
    sent_msg0
    received_msg0
    sent_msg1
    received_msg1
    sent_msg2
    received_msg2
    sent_msg3
    received_msg3
    server_rest
    client_rest
    server_raw_sent
    server_raw_received
    client_raw_sent
    client_raw_received
    server_final
    client_final;
  eliminate exists
    (client_tail_sent:B.bytes)
    (client_tail_received:B.bytes)
    (server_tail_sent:B.bytes)
    (server_tail_received:B.bytes).
    Seq.equal client_tail_sent server_tail_received /\
    conn_events_sent_seal_replay
      client_after3
      client_rest
      client_tail_sent
      client_tail_received
      client_final /\
    conn_events_received_decode_replay
      server_after3
      server_rest
      server_tail_sent
      server_tail_received
      server_final
  with
  ( let server_install =
      LocalInstallTrafficKeysForRole {
        install_role = ServerEndpoint;
        install_payload = {
          install_epoch = TrafficHandshake;
          install_direction = TrafficWrite;
          install_material = server_material;
        };
      } in
    let client_install =
      LocalInstallTrafficKeys {
        install_epoch = TrafficHandshake;
        install_direction = TrafficRead;
        install_material = client_material;
      } in
    assert (local_event_preserves_record_read server_install);
    lemma_step_receiver_local_event_preserves_write_read_record_material_alignment
      client
      server
      server_install
      server_after_install;
    assert (local_event_preserves_record_write client_install);
    lemma_step_sender_local_event_preserves_write_read_record_material_alignment
      client
      client_install
      client_after_install
      server_after_install;
    lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
      client_after_install
      (M.TlsHandshake received_msg0)
      client_after0
      server_after_install
      (M.TlsHandshake sent_msg0)
      server_after0;
    lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
      client_after0
      (M.TlsHandshake received_msg1)
      client_after1
      server_after0
      (M.TlsHandshake sent_msg1)
      server_after1;
    lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
      client_after1
      server_after1
      server_auth_skip
      server_after_auth_skip;
    lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
      client_after1
      client_auth_skip
      client_after_auth_skip
      server_after_auth_skip;
    lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
      client_after_auth_skip
      (M.TlsHandshake received_msg2)
      client_after2
      server_after_auth_skip
      (M.TlsHandshake sent_msg2)
      server_after2;
    lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
      client_after2
      client_verify_skip
      client_after_verify_skip
      server_after2;
    lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
      client_after_verify_skip
      (M.TlsHandshake received_msg3)
      client_after3
      server_after2
      (M.TlsHandshake sent_msg3)
      server_after3;
    introduce exists
      (client_tail_sent':B.bytes)
      (client_tail_received':B.bytes)
      (server_tail_sent':B.bytes)
      (server_tail_received':B.bytes).
      write_read_record_material_aligned client_after3 server_after3 /\
      Seq.equal client_tail_sent' server_tail_received' /\
      conn_events_sent_seal_replay
        client_after3
        client_rest
        client_tail_sent'
        client_tail_received'
        client_final /\
      conn_events_received_decode_replay
        server_after3
        server_rest
        server_tail_sent'
        server_tail_received'
        server_final
    with
      client_tail_sent
      client_tail_received
      server_tail_sent
      server_tail_received
    and () )

let lemma_server_encrypted_flight_preserves_client_write_server_read_alignment
  (server:connection_model)
  (client:connection_model)
  (server_after_install:connection_model)
  (client_after_install:connection_model)
  (server_after0:connection_model)
  (client_after0:connection_model)
  (server_after1:connection_model)
  (client_after1:connection_model)
  (server_after_auth_skip:connection_model)
  (client_after_auth_skip:connection_model)
  (server_after2:connection_model)
  (client_after2:connection_model)
  (client_after_verify_skip:connection_model)
  (server_after3:connection_model)
  (client_after3:connection_model)
  (server_auth_skip:local_event)
  (client_auth_skip:local_event)
  (client_verify_skip:local_event)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  : Lemma
      (requires
        write_read_record_material_aligned client server /\
        local_event_does_not_install_record_keys server_auth_skip /\
        local_event_does_not_install_record_keys client_auth_skip /\
        local_event_does_not_install_record_keys client_verify_skip /\
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
            })) == Some server_after_install /\
        step_model
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            })) == Some client_after_install /\
        step_model
          server_after_install
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        step_model
          client_after_install
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        step_model
          server_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        step_model
          client_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        step_model server_after1 (ConnLocalEvent server_auth_skip) ==
          Some server_after_auth_skip /\
        step_model client_after1 (ConnLocalEvent client_auth_skip) ==
          Some client_after_auth_skip /\
        step_model
          server_after_auth_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        step_model
          client_after_auth_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        step_model client_after2 (ConnLocalEvent client_verify_skip) ==
          Some client_after_verify_skip /\
        step_model
          server_after2
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg3;
          }) == Some server_after3 /\
        step_model
          client_after_verify_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg3;
          }) == Some client_after3)
      (ensures write_read_record_material_aligned client_after3 server_after3)
=
  let server_install =
    LocalInstallTrafficKeysForRole {
      install_role = ServerEndpoint;
      install_payload = {
        install_epoch = TrafficHandshake;
        install_direction = TrafficWrite;
        install_material = server_material;
      };
    } in
  let client_install =
    LocalInstallTrafficKeys {
      install_epoch = TrafficHandshake;
      install_direction = TrafficRead;
      install_material = client_material;
    } in
  assert (local_event_preserves_record_read server_install);
  lemma_step_receiver_local_event_preserves_write_read_record_material_alignment
    client
    server
    server_install
    server_after_install;
  assert (local_event_preserves_record_write client_install);
  lemma_step_sender_local_event_preserves_write_read_record_material_alignment
    client
    client_install
    client_after_install
    server_after_install;
  lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
    client_after_install
    (M.TlsHandshake received_msg0)
    client_after0
    server_after_install
    (M.TlsHandshake sent_msg0)
    server_after0;
  lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
    client_after0
    (M.TlsHandshake received_msg1)
    client_after1
    server_after0
    (M.TlsHandshake sent_msg1)
    server_after1;
  lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
    client_after1
    server_after1
    server_auth_skip
    server_after_auth_skip;
  lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
    client_after1
    client_auth_skip
    client_after_auth_skip
    server_after_auth_skip;
  lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
    client_after_auth_skip
    (M.TlsHandshake received_msg2)
    client_after2
    server_after_auth_skip
    (M.TlsHandshake sent_msg2)
    server_after2;
  lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
    client_after2
    client_verify_skip
    client_after_verify_skip
    server_after2;
  lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
    client_after_verify_skip
    (M.TlsHandshake received_msg3)
    client_after3
    server_after2
    (M.TlsHandshake sent_msg3)
    server_after3

let lemma_server_encrypted_flight_after_installs_preserves_client_write_server_read_alignment
  (server:connection_model)
  (client:connection_model)
  (server_after0:connection_model)
  (client_after0:connection_model)
  (server_after1:connection_model)
  (client_after1:connection_model)
  (server_after_auth_skip:connection_model)
  (client_after_auth_skip:connection_model)
  (server_after2:connection_model)
  (client_after2:connection_model)
  (client_after_verify_skip:connection_model)
  (server_after3:connection_model)
  (client_after3:connection_model)
  (server_auth_skip:local_event)
  (client_auth_skip:local_event)
  (client_verify_skip:local_event)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  : Lemma
      (requires
        write_read_record_material_aligned client server /\
        local_event_does_not_install_record_keys server_auth_skip /\
        local_event_does_not_install_record_keys client_auth_skip /\
        local_event_does_not_install_record_keys client_verify_skip /\
        step_model
          server
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        step_model
          client
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        step_model
          server_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        step_model
          client_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        step_model server_after1 (ConnLocalEvent server_auth_skip) ==
          Some server_after_auth_skip /\
        step_model client_after1 (ConnLocalEvent client_auth_skip) ==
          Some client_after_auth_skip /\
        step_model
          server_after_auth_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        step_model
          client_after_auth_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        step_model client_after2 (ConnLocalEvent client_verify_skip) ==
          Some client_after_verify_skip /\
        step_model
          server_after2
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg3;
          }) == Some server_after3 /\
        step_model
          client_after_verify_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg3;
          }) == Some client_after3)
      (ensures write_read_record_material_aligned client_after3 server_after3)
=
  lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
    client
    (M.TlsHandshake received_msg0)
    client_after0
    server
    (M.TlsHandshake sent_msg0)
    server_after0;
  lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
    client_after0
    (M.TlsHandshake received_msg1)
    client_after1
    server_after0
    (M.TlsHandshake sent_msg1)
    server_after1;
  lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
    client_after1
    server_after1
    server_auth_skip
    server_after_auth_skip;
  lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
    client_after1
    client_auth_skip
    client_after_auth_skip
    server_after_auth_skip;
  lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
    client_after_auth_skip
    (M.TlsHandshake received_msg2)
    client_after2
    server_after_auth_skip
    (M.TlsHandshake sent_msg2)
    server_after2;
  lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
    client_after2
    client_verify_skip
    client_after_verify_skip
    server_after2;
  lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
    client_after_verify_skip
    (M.TlsHandshake received_msg3)
    client_after3
    server_after2
    (M.TlsHandshake sent_msg3)
    server_after3

#pop-options
