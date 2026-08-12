module TLS13.ConnectionState.ProtectedWireClientFinished

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CSL = TLS13.ConnectionState.Lemmas
module K = TLS13.Keys
module M = TLS13.Messages
module GFin = TLS13.Wire.Generated.Finished
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
open TLS13.ConnectionState.ProtectedWireRecordAlignment
open TLS13.ConnectionState.ProtectedWireHead

#push-options "--split_queries always --z3rlimit 10"
let lemma_protected_handshake_event_projection_pair_after_client_write_server_read_install_heads_with_tails
  (client:connection_model)
  (server:connection_model)
  (client_material:traffic_key_material)
  (server_material:traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (client_rest:list conn_event)
  (server_rest:list conn_event)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_final:connection_model)
  (server_final:connection_model)
  : Lemma
      (requires
        (match
          client.model_handshake.hs_keys.ks_handshake_secret,
          server.model_handshake.hs_keys.ks_handshake_secret
        with
        | Some client_secret, Some server_secret ->
          Seq.equal client_secret server_secret
        | _, _ ->
          False) /\
        Seq.equal
          client.model_handshake.hs_transcript
          server.model_handshake.hs_transcript /\
        negotiated_aead_alg client.model_handshake ==
          negotiated_aead_alg server.model_handshake /\
        Seq.equal client_raw_sent server_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficWrite;
              install_material = client_material;
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
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
                install_direction = TrafficRead;
                install_material = server_material;
              };
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final)
      (ensures
        exists client_after server_after client_after_head server_after_head pair
          client_tail_sent client_tail_received
          server_tail_sent server_tail_received.
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
              })) == Some server_after /\
          step_model
            client_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some client_after_head /\
          step_model
            server_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some server_after_head /\
          pair.pm_sender == client_after /\
          pair.pm_receiver == server_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal client_tail_sent server_tail_received /\
          conn_events_sent_seal_replay
            client_after_head
            client_rest
            client_tail_sent
            client_tail_received
            client_final /\
          conn_events_received_decode_replay
            server_after_head
            server_rest
            server_tail_sent
            server_tail_received
            server_final)
=
  let client_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeys {
        install_epoch = TrafficHandshake;
        install_direction = TrafficWrite;
        install_material = client_material;
      }) in
  let server_install_ev =
    ConnLocalEvent
      (LocalInstallTrafficKeysForRole {
        install_role = ServerEndpoint;
        install_payload = {
          install_epoch = TrafficHandshake;
          install_direction = TrafficRead;
          install_material = server_material;
        };
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
    client
    client_install_ev
    (sent_ev :: client_rest)
    client_raw_sent
    client_raw_received
    server_raw_received
    client_final;
  eliminate exists
    (client_after:connection_model)
    (client_sent_after_install:B.bytes)
    (client_received_after_install:B.bytes).
    legal_event client client_install_ev /\
    step_model client client_install_ev == Some client_after /\
    Seq.equal client_sent_after_install server_raw_received /\
    conn_events_sent_seal_replay
      client_after
      (sent_ev :: client_rest)
      client_sent_after_install
      client_received_after_install
      client_final
  with
  ( lemma_received_replay_skip_empty_head_preserves_peer_stream
      client_sent_after_install
      server
      server_install_ev
      (received_ev :: server_rest)
      server_raw_sent
      server_raw_received
      server_final;
    eliminate exists
      (server_after:connection_model)
      (server_sent_after_install:B.bytes)
      (server_received_after_install:B.bytes).
      legal_event server server_install_ev /\
      step_model server server_install_ev == Some server_after /\
      Seq.equal client_sent_after_install server_received_after_install /\
      conn_events_received_decode_replay
        server_after
        (received_ev :: server_rest)
        server_sent_after_install
        server_received_after_install
        server_final
    with
    ( assert (traffic_install_matches_key_schedule
        client.model_handshake
        {
          install_epoch = TrafficHandshake;
          install_direction = TrafficWrite;
          install_material = client_material;
        });
      assert (traffic_install_matches_key_schedule_for_role
        ServerEndpoint
        server.model_handshake
        {
          install_epoch = TrafficHandshake;
          install_direction = TrafficRead;
          install_material = server_material;
        });
      lemma_client_handshake_write_server_handshake_read_install_aligned_from_key_schedule
        client
        server
        client_material
        server_material
        client_after
        server_after;
      lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
        client_after
        server_after
        sent_msg
        received_msg
        client_rest
        server_rest
        client_sent_after_install
        client_received_after_install
        server_sent_after_install
        server_received_after_install
        client_final
        server_final;
      eliminate exists
        (client_after_head0:connection_model)
        (server_after_head0:connection_model)
        (pair0:protected_message_replay)
        (client_tail_sent:B.bytes)
        (client_tail_received:B.bytes)
        (server_tail_sent:B.bytes)
        (server_tail_received:B.bytes).
        step_model client_after sent_ev == Some client_after_head0 /\
        step_model server_after received_ev == Some server_after_head0 /\
        pair0.pm_sender == client_after /\
        pair0.pm_receiver == server_after /\
        protected_handshake_event_projection_pair
          pair0
          sent_msg
          received_msg /\
        Seq.equal client_sent_after_install (B.append pair0.pm_raw_sent client_tail_sent) /\
        Seq.equal server_received_after_install (B.append pair0.pm_raw_received server_tail_received) /\
        Seq.equal client_tail_sent server_tail_received /\
        conn_events_sent_seal_replay
          client_after_head0
          client_rest
          client_tail_sent
          client_tail_received
          client_final /\
        conn_events_received_decode_replay
          server_after_head0
          server_rest
          server_tail_sent
          server_tail_received
          server_final
      with
      ( introduce exists
          (client_after':connection_model)
          (server_after':connection_model)
          (client_after_head:connection_model)
          (server_after_head:connection_model)
          (pair:protected_message_replay)
          (client_tail_sent':B.bytes)
          (client_tail_received':B.bytes)
          (server_tail_sent':B.bytes)
          (server_tail_received':B.bytes).
          step_model client client_install_ev == Some client_after' /\
          step_model server server_install_ev == Some server_after' /\
          step_model client_after' sent_ev == Some client_after_head /\
          step_model server_after' received_ev == Some server_after_head /\
          pair.pm_sender == client_after' /\
          pair.pm_receiver == server_after' /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal client_tail_sent' server_tail_received' /\
          conn_events_sent_seal_replay
            client_after_head
            client_rest
            client_tail_sent'
            client_tail_received'
            client_final /\
          conn_events_received_decode_replay
            server_after_head
            server_rest
            server_tail_sent'
            server_tail_received'
            server_final
        with
          client_after
          server_after
          client_after_head0
          server_after_head0
          pair0
          client_tail_sent
          client_tail_received
          server_tail_sent
          server_tail_received
        and () ) ) )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_protected_handshake_event_projection_pair_after_client_finished_local_skips_with_tails
  (client:connection_model)
  (server:connection_model)
  (client_after_verify:connection_model)
  (client_after_app_write:connection_model)
  (client_after_app_read:connection_model)
  (server_after_app_write:connection_model)
  (client_after_finished:connection_model)
  (server_after_finished:connection_model)
  (verified_server_finished:GFin.finished)
  (client_app_write_material:traffic_key_material)
  (client_app_read_material:traffic_key_material)
  (server_app_write_material:traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (client_rest:list conn_event)
  (server_rest:list conn_event)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_final:connection_model)
  (server_final:connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned client server /\
        Seq.equal client_raw_sent server_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        step_model
          client
          (ConnLocalEvent (LocalVerifyFinished verified_server_finished)) ==
          Some client_after_verify /\
        step_model
          client_after_verify
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficApplication;
              install_direction = TrafficWrite;
              install_material = client_app_write_material;
            })) == Some client_after_app_write /\
        step_model
          client_after_app_write
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficApplication;
              install_direction = TrafficRead;
              install_material = client_app_read_material;
            })) == Some client_after_app_read /\
        step_model
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficApplication;
                install_direction = TrafficWrite;
                install_material = server_app_write_material;
              };
            })) == Some server_after_app_write /\
        step_model
          client_after_app_read
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some client_after_finished /\
        step_model
          server_after_app_write
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some server_after_finished /\
        conn_events_sent_seal_replay
          client
          (ConnLocalEvent (LocalVerifyFinished verified_server_finished) ::
           ConnLocalEvent
             (LocalInstallTrafficKeys {
               install_epoch = TrafficApplication;
               install_direction = TrafficWrite;
               install_material = client_app_write_material;
             }) ::
           ConnLocalEvent
             (LocalInstallTrafficKeys {
               install_epoch = TrafficApplication;
               install_direction = TrafficRead;
               install_material = client_app_read_material;
             }) ::
           ConnNetworkEvent {
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake sent_msg;
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
                 install_epoch = TrafficApplication;
                 install_direction = TrafficWrite;
                 install_material = server_app_write_material;
               };
             }) ::
           ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake received_msg;
           } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final)
      (ensures
        exists pair client_tail_sent client_tail_received
          server_tail_sent server_tail_received.
          pair.pm_sender == client_after_app_read /\
          pair.pm_receiver == server_after_app_write /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal client_tail_sent server_tail_received /\
          conn_events_sent_seal_replay
            client_after_finished
            client_rest
            client_tail_sent
            client_tail_received
            client_final /\
          conn_events_received_decode_replay
            server_after_finished
            server_rest
            server_tail_sent
            server_tail_received
            server_final)
=
  let client_verify_local = LocalVerifyFinished verified_server_finished in
  let client_verify_ev = ConnLocalEvent client_verify_local in
  let client_app_write_local =
    LocalInstallTrafficKeys {
      install_epoch = TrafficApplication;
      install_direction = TrafficWrite;
      install_material = client_app_write_material;
    } in
  let client_app_write_ev = ConnLocalEvent client_app_write_local in
  let client_app_read_local =
    LocalInstallTrafficKeys {
      install_epoch = TrafficApplication;
      install_direction = TrafficRead;
      install_material = client_app_read_material;
    } in
  let client_app_read_ev = ConnLocalEvent client_app_read_local in
  let server_app_write_local =
    LocalInstallTrafficKeysForRole {
      install_role = ServerEndpoint;
      install_payload = {
        install_epoch = TrafficApplication;
        install_direction = TrafficWrite;
        install_material = server_app_write_material;
      };
    } in
  let server_app_write_ev = ConnLocalEvent server_app_write_local in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    client
    client_verify_ev
    (client_app_write_ev :: client_app_read_ev :: sent_ev :: client_rest)
    client_raw_sent
    client_raw_received
    server_raw_received
    client_final;
  eliminate exists
    (client_after_verify0:connection_model)
    (client_sent_after_verify:B.bytes)
    (client_received_after_verify:B.bytes).
    legal_event client client_verify_ev /\
    step_model client client_verify_ev == Some client_after_verify0 /\
    Seq.equal client_sent_after_verify server_raw_received /\
    conn_events_sent_seal_replay
      client_after_verify0
      (client_app_write_ev :: client_app_read_ev :: sent_ev :: client_rest)
      client_sent_after_verify
      client_received_after_verify
      client_final
  with
  ( assert (client_after_verify0 == client_after_verify);
    lemma_step_sender_local_event_preserves_write_read_record_material_alignment
      client
      client_verify_local
      client_after_verify
      server;
    lemma_sent_replay_skip_empty_head_preserves_peer_stream
      client_after_verify
      client_app_write_ev
      (client_app_read_ev :: sent_ev :: client_rest)
      client_sent_after_verify
      client_received_after_verify
      server_raw_received
      client_final;
    eliminate exists
      (client_after_app_write0:connection_model)
      (client_sent_after_app_write:B.bytes)
      (client_received_after_app_write:B.bytes).
      legal_event client_after_verify client_app_write_ev /\
      step_model client_after_verify client_app_write_ev ==
        Some client_after_app_write0 /\
      Seq.equal client_sent_after_app_write server_raw_received /\
      conn_events_sent_seal_replay
        client_after_app_write0
        (client_app_read_ev :: sent_ev :: client_rest)
        client_sent_after_app_write
        client_received_after_app_write
        client_final
    with
    ( assert (client_after_app_write0 == client_after_app_write);
      lemma_step_sender_local_event_preserves_write_read_record_material_alignment
        client_after_verify
        client_app_write_local
        client_after_app_write
        server;
      lemma_sent_replay_skip_empty_head_preserves_peer_stream
        client_after_app_write
        client_app_read_ev
        (sent_ev :: client_rest)
        client_sent_after_app_write
        client_received_after_app_write
        server_raw_received
        client_final;
      eliminate exists
        (client_after_app_read0:connection_model)
        (client_sent_after_app_read:B.bytes)
        (client_received_after_app_read:B.bytes).
        legal_event client_after_app_write client_app_read_ev /\
        step_model client_after_app_write client_app_read_ev ==
          Some client_after_app_read0 /\
        Seq.equal client_sent_after_app_read server_raw_received /\
        conn_events_sent_seal_replay
          client_after_app_read0
          (sent_ev :: client_rest)
          client_sent_after_app_read
          client_received_after_app_read
          client_final
      with
      ( assert (client_after_app_read0 == client_after_app_read);
        lemma_step_sender_local_event_preserves_write_read_record_material_alignment
          client_after_app_write
          client_app_read_local
          client_after_app_read
          server;
        lemma_received_replay_skip_empty_head_preserves_peer_stream
          client_sent_after_app_read
          server
          server_app_write_ev
          (received_ev :: server_rest)
          server_raw_sent
          server_raw_received
          server_final;
        eliminate exists
          (server_after_app_write0:connection_model)
          (server_sent_after_app_write:B.bytes)
          (server_received_after_app_write:B.bytes).
          legal_event server server_app_write_ev /\
          step_model server server_app_write_ev == Some server_after_app_write0 /\
          Seq.equal client_sent_after_app_read server_received_after_app_write /\
          conn_events_received_decode_replay
            server_after_app_write0
            (received_ev :: server_rest)
            server_sent_after_app_write
            server_received_after_app_write
            server_final
        with
        ( assert (server_after_app_write0 == server_after_app_write);
          lemma_step_receiver_local_event_preserves_write_read_record_material_alignment
            client_after_app_read
            server
            server_app_write_local
            server_after_app_write;
          lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
            client_after_app_read
            server_after_app_write
            sent_msg
            received_msg
            client_rest
            server_rest
            client_sent_after_app_read
            client_received_after_app_read
            server_sent_after_app_write
            server_received_after_app_write
            client_final
            server_final;
          eliminate exists
            (client_after_finished0:connection_model)
            (server_after_finished0:connection_model)
            (pair0:protected_message_replay)
            (client_tail_sent:B.bytes)
            (client_tail_received:B.bytes)
            (server_tail_sent:B.bytes)
            (server_tail_received:B.bytes).
            step_model client_after_app_read sent_ev ==
              Some client_after_finished0 /\
            step_model server_after_app_write received_ev ==
              Some server_after_finished0 /\
            pair0.pm_sender == client_after_app_read /\
            pair0.pm_receiver == server_after_app_write /\
            protected_handshake_event_projection_pair
              pair0
              sent_msg
              received_msg /\
            Seq.equal client_sent_after_app_read (B.append pair0.pm_raw_sent client_tail_sent) /\
            Seq.equal server_received_after_app_write (B.append pair0.pm_raw_received server_tail_received) /\
            Seq.equal client_tail_sent server_tail_received /\
            conn_events_sent_seal_replay
              client_after_finished0
              client_rest
              client_tail_sent
              client_tail_received
              client_final /\
            conn_events_received_decode_replay
              server_after_finished0
              server_rest
              server_tail_sent
              server_tail_received
              server_final
          with
          ( assert (client_after_finished0 == client_after_finished);
            assert (server_after_finished0 == server_after_finished);
            introduce exists
              (pair:protected_message_replay)
              (client_tail_sent':B.bytes)
              (client_tail_received':B.bytes)
              (server_tail_sent':B.bytes)
              (server_tail_received':B.bytes).
              pair.pm_sender == client_after_app_read /\
              pair.pm_receiver == server_after_app_write /\
              protected_handshake_event_projection_pair
                pair
                sent_msg
                received_msg /\
              Seq.equal client_tail_sent' server_tail_received' /\
              conn_events_sent_seal_replay
                client_after_finished
                client_rest
                client_tail_sent'
                client_tail_received'
                client_final /\
              conn_events_received_decode_replay
                server_after_finished
                server_rest
                server_tail_sent'
                server_tail_received'
                server_final
            with
              pair0
              client_tail_sent
              client_tail_received
              server_tail_sent
              server_tail_received
            and () ) ) ) ) )
#pop-options
