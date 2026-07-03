module TLS13.ConnectionState.ProtectedWireServerFlight

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

val lemma_protected_handshake_event_projection_pair_after_server_write_client_read_install_heads_with_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (server_rest:list CS.conn_event)
  (client_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (requires
        (match
          server.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.CS.model_handshake.CS.hs_transcript
          client.CS.model_handshake.CS.hs_transcript /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        CS.conn_events_received_decode_replay
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            }) :: CS.ConnNetworkEvent {
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
          CS.step_model
            server
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = server_material;
                };
              })) == Some server_after /\
          CS.step_model
            client
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = client_material;
              })) == Some client_after /\
          CS.step_model
            server_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some server_after_head /\
          CS.step_model
            client_after
            (CS.ConnNetworkEvent {
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
          CS.conn_events_sent_seal_replay
            server_after_head
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          CS.conn_events_received_decode_replay
            client_after_head
            client_rest
            client_tail_sent
            client_tail_received
            client_final)

val lemma_protected_handshake_event_projection_pair_after_server_write_client_read_install_heads_with_next_alignment_and_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_after:CS.connection_model)
  (client_after:CS.connection_model)
  (server_after_head:CS.connection_model)
  (client_after_head:CS.connection_model)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (server_rest:list CS.conn_event)
  (client_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (requires
        (match
          server.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.CS.model_handshake.CS.hs_transcript
          client.CS.model_handshake.CS.hs_transcript /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            })) == Some server_after /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            })) == Some client_after /\
        CS.step_model
          server_after
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some server_after_head /\
        CS.step_model
          client_after
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some client_after_head /\
        server_after_head.CS.model_record.CS.record_write ==
          R.next_seq server_after.CS.model_record.CS.record_write /\
        client_after_head.CS.model_record.CS.record_read ==
          R.next_seq client_after.CS.model_record.CS.record_read /\
        CS.conn_events_sent_seal_replay
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        CS.conn_events_received_decode_replay
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            }) :: CS.ConnNetworkEvent {
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
          CS.conn_events_sent_seal_replay
            server_after_head
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          CS.conn_events_received_decode_replay
            client_after_head
            client_rest
            client_tail_sent
            client_tail_received
            client_final)

val lemma_protected_handshake_event_projection_pairs_after_server_write_client_read_install_and_next_head_with_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_after_install:CS.connection_model)
  (client_after_install:CS.connection_model)
  (server_after0:CS.connection_model)
  (client_after0:CS.connection_model)
  (server_after1:CS.connection_model)
  (client_after1:CS.connection_model)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (server_rest:list CS.conn_event)
  (client_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (requires
        (match
          server.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.CS.model_handshake.CS.hs_transcript
          client.CS.model_handshake.CS.hs_transcript /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg0 /\
        protected_handshake_wire_round_trip_message received_msg0 /\
        protected_handshake_wire_round_trip_message sent_msg1 /\
        protected_handshake_wire_round_trip_message received_msg1 /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            })) == Some server_after_install /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            })) == Some client_after_install /\
        CS.step_model
          server_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        CS.step_model
          client_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        server_after0.CS.model_record.CS.record_write ==
          R.next_seq server_after_install.CS.model_record.CS.record_write /\
        client_after0.CS.model_record.CS.record_read ==
          R.next_seq client_after_install.CS.model_record.CS.record_read /\
        CS.step_model
          server_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        CS.step_model
          client_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        server_after1.CS.model_record.CS.record_write ==
          R.next_seq server_after0.CS.model_record.CS.record_write /\
        client_after1.CS.model_record.CS.record_read ==
          R.next_seq client_after0.CS.model_record.CS.record_read /\
        CS.conn_events_sent_seal_replay
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg0;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg1;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        CS.conn_events_received_decode_replay
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg0;
            } :: CS.ConnNetworkEvent {
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
          CS.conn_events_sent_seal_replay
            server_after1
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          CS.conn_events_received_decode_replay
            client_after1
            client_rest
            client_tail_sent
            client_tail_received
            client_final)

val lemma_protected_handshake_event_projection_pairs_after_server_write_client_read_install_two_heads_then_both_non_install_local_heads_with_next_alignment_and_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_after_install:CS.connection_model)
  (client_after_install:CS.connection_model)
  (server_after0:CS.connection_model)
  (client_after0:CS.connection_model)
  (server_after1:CS.connection_model)
  (client_after1:CS.connection_model)
  (server_after_skip:CS.connection_model)
  (client_after_skip:CS.connection_model)
  (server_after2:CS.connection_model)
  (client_after2:CS.connection_model)
  (server_skip:CS.local_event)
  (client_skip:CS.local_event)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (server_rest:list CS.conn_event)
  (client_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (requires
        (match
          server.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.CS.model_handshake.CS.hs_transcript
          client.CS.model_handshake.CS.hs_transcript /\
        local_event_does_not_install_record_keys server_skip /\
        local_event_does_not_install_record_keys client_skip /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg0 /\
        protected_handshake_wire_round_trip_message received_msg0 /\
        protected_handshake_wire_round_trip_message sent_msg1 /\
        protected_handshake_wire_round_trip_message received_msg1 /\
        protected_handshake_wire_round_trip_message sent_msg2 /\
        protected_handshake_wire_round_trip_message received_msg2 /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            })) == Some server_after_install /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            })) == Some client_after_install /\
        CS.step_model
          server_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        CS.step_model
          client_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        server_after0.CS.model_record.CS.record_write ==
          R.next_seq server_after_install.CS.model_record.CS.record_write /\
        client_after0.CS.model_record.CS.record_read ==
          R.next_seq client_after_install.CS.model_record.CS.record_read /\
        CS.step_model
          server_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        CS.step_model
          client_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        server_after1.CS.model_record.CS.record_write ==
          R.next_seq server_after0.CS.model_record.CS.record_write /\
        client_after1.CS.model_record.CS.record_read ==
          R.next_seq client_after0.CS.model_record.CS.record_read /\
        CS.step_model server_after1 (CS.ConnLocalEvent server_skip) ==
          Some server_after_skip /\
        CS.step_model client_after1 (CS.ConnLocalEvent client_skip) ==
          Some client_after_skip /\
        CS.step_model
          server_after_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        CS.step_model
          client_after_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        server_after2.CS.model_record.CS.record_write ==
          R.next_seq server_after_skip.CS.model_record.CS.record_write /\
        client_after2.CS.model_record.CS.record_read ==
          R.next_seq client_after_skip.CS.model_record.CS.record_read /\
        CS.conn_events_sent_seal_replay
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg0;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg1;
            } :: CS.ConnLocalEvent server_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg2;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        CS.conn_events_received_decode_replay
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg0;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg1;
            } :: CS.ConnLocalEvent client_skip :: CS.ConnNetworkEvent {
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
          CS.conn_events_sent_seal_replay
            server_after2
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          CS.conn_events_received_decode_replay
            client_after2
            client_rest
            client_tail_sent
            client_tail_received
            client_final)

val lemma_protected_handshake_event_projection_pairs_after_server_write_client_read_install_server_encrypted_flight_with_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_after_install:CS.connection_model)
  (client_after_install:CS.connection_model)
  (server_after0:CS.connection_model)
  (client_after0:CS.connection_model)
  (server_after1:CS.connection_model)
  (client_after1:CS.connection_model)
  (server_after_auth_skip:CS.connection_model)
  (client_after_auth_skip:CS.connection_model)
  (server_after2:CS.connection_model)
  (client_after2:CS.connection_model)
  (client_after_verify_skip:CS.connection_model)
  (server_after3:CS.connection_model)
  (client_after3:CS.connection_model)
  (server_auth_skip:CS.local_event)
  (client_auth_skip:CS.local_event)
  (client_verify_skip:CS.local_event)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (server_rest:list CS.conn_event)
  (client_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (requires
        (match
          server.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.CS.model_handshake.CS.hs_transcript
          client.CS.model_handshake.CS.hs_transcript /\
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
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            })) == Some server_after_install /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            })) == Some client_after_install /\
        CS.step_model
          server_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        CS.step_model
          client_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        server_after0.CS.model_record.CS.record_write ==
          R.next_seq server_after_install.CS.model_record.CS.record_write /\
        client_after0.CS.model_record.CS.record_read ==
          R.next_seq client_after_install.CS.model_record.CS.record_read /\
        CS.step_model
          server_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        CS.step_model
          client_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        server_after1.CS.model_record.CS.record_write ==
          R.next_seq server_after0.CS.model_record.CS.record_write /\
        client_after1.CS.model_record.CS.record_read ==
          R.next_seq client_after0.CS.model_record.CS.record_read /\
        CS.step_model server_after1 (CS.ConnLocalEvent server_auth_skip) ==
          Some server_after_auth_skip /\
        CS.step_model client_after1 (CS.ConnLocalEvent client_auth_skip) ==
          Some client_after_auth_skip /\
        CS.step_model
          server_after_auth_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        CS.step_model
          client_after_auth_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        server_after2.CS.model_record.CS.record_write ==
          R.next_seq server_after_auth_skip.CS.model_record.CS.record_write /\
        client_after2.CS.model_record.CS.record_read ==
          R.next_seq client_after_auth_skip.CS.model_record.CS.record_read /\
        CS.step_model client_after2 (CS.ConnLocalEvent client_verify_skip) ==
          Some client_after_verify_skip /\
        CS.step_model
          server_after2
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg3;
          }) == Some server_after3 /\
        CS.step_model
          client_after_verify_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg3;
          }) == Some client_after3 /\
        server_after3.CS.model_record.CS.record_write ==
          R.next_seq server_after2.CS.model_record.CS.record_write /\
        client_after3.CS.model_record.CS.record_read ==
          R.next_seq client_after_verify_skip.CS.model_record.CS.record_read /\
        CS.conn_events_sent_seal_replay
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg0;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg1;
            } :: CS.ConnLocalEvent server_auth_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg2;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg3;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        CS.conn_events_received_decode_replay
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg0;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg1;
            } :: CS.ConnLocalEvent client_auth_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg2;
            } :: CS.ConnLocalEvent client_verify_skip :: CS.ConnNetworkEvent {
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
          CS.conn_events_sent_seal_replay
            server_after3
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          CS.conn_events_received_decode_replay
            client_after3
            client_rest
            client_tail_sent
            client_tail_received
            client_final)

val lemma_server_encrypted_flight_preserves_client_to_server_stream_with_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_after_install:CS.connection_model)
  (client_after_install:CS.connection_model)
  (server_after0:CS.connection_model)
  (client_after0:CS.connection_model)
  (server_after1:CS.connection_model)
  (client_after1:CS.connection_model)
  (server_after_auth_skip:CS.connection_model)
  (client_after_auth_skip:CS.connection_model)
  (server_after2:CS.connection_model)
  (client_after2:CS.connection_model)
  (client_after_verify_skip:CS.connection_model)
  (server_after3:CS.connection_model)
  (client_after3:CS.connection_model)
  (server_auth_skip:CS.local_event)
  (client_auth_skip:CS.local_event)
  (client_verify_skip:CS.local_event)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (server_rest:list CS.conn_event)
  (client_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (requires
        Seq.equal client_raw_sent server_raw_received /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            })) == Some server_after_install /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            })) == Some client_after_install /\
        CS.step_model
          server_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        CS.step_model
          client_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        CS.step_model
          server_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        CS.step_model
          client_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        CS.step_model server_after1 (CS.ConnLocalEvent server_auth_skip) ==
          Some server_after_auth_skip /\
        CS.step_model client_after1 (CS.ConnLocalEvent client_auth_skip) ==
          Some client_after_auth_skip /\
        CS.step_model
          server_after_auth_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        CS.step_model
          client_after_auth_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        CS.step_model client_after2 (CS.ConnLocalEvent client_verify_skip) ==
          Some client_after_verify_skip /\
        CS.step_model
          server_after2
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg3;
          }) == Some server_after3 /\
        CS.step_model
          client_after_verify_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg3;
          }) == Some client_after3 /\
        CS.conn_events_sent_seal_replay
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg0;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg1;
            } :: CS.ConnLocalEvent server_auth_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg2;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg3;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        CS.conn_events_received_decode_replay
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg0;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg1;
            } :: CS.ConnLocalEvent client_auth_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg2;
            } :: CS.ConnLocalEvent client_verify_skip :: CS.ConnNetworkEvent {
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
          CS.conn_events_sent_seal_replay
            server_after3
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          CS.conn_events_received_decode_replay
            client_after3
            client_rest
            client_tail_sent
            client_tail_received
            client_final)

val lemma_server_encrypted_flight_preserves_client_to_server_replay_tails_with_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_after_install:CS.connection_model)
  (client_after_install:CS.connection_model)
  (server_after0:CS.connection_model)
  (client_after0:CS.connection_model)
  (server_after1:CS.connection_model)
  (client_after1:CS.connection_model)
  (server_after_auth_skip:CS.connection_model)
  (client_after_auth_skip:CS.connection_model)
  (server_after2:CS.connection_model)
  (client_after2:CS.connection_model)
  (client_after_verify_skip:CS.connection_model)
  (server_after3:CS.connection_model)
  (client_after3:CS.connection_model)
  (server_auth_skip:CS.local_event)
  (client_auth_skip:CS.local_event)
  (client_verify_skip:CS.local_event)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (server_rest:list CS.conn_event)
  (client_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (requires
        Seq.equal client_raw_sent server_raw_received /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            })) == Some server_after_install /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            })) == Some client_after_install /\
        CS.step_model
          server_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        CS.step_model
          client_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        CS.step_model
          server_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        CS.step_model
          client_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        CS.step_model server_after1 (CS.ConnLocalEvent server_auth_skip) ==
          Some server_after_auth_skip /\
        CS.step_model client_after1 (CS.ConnLocalEvent client_auth_skip) ==
          Some client_after_auth_skip /\
        CS.step_model
          server_after_auth_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        CS.step_model
          client_after_auth_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        CS.step_model client_after2 (CS.ConnLocalEvent client_verify_skip) ==
          Some client_after_verify_skip /\
        CS.step_model
          server_after2
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg3;
          }) == Some server_after3 /\
        CS.step_model
          client_after_verify_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg3;
          }) == Some client_after3 /\
        CS.conn_events_sent_seal_replay
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg0;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg1;
            } :: CS.ConnLocalEvent client_auth_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg2;
            } :: CS.ConnLocalEvent client_verify_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg3;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final /\
        CS.conn_events_received_decode_replay
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg0;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg1;
            } :: CS.ConnLocalEvent server_auth_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg2;
            } :: CS.ConnNetworkEvent {
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
          CS.conn_events_sent_seal_replay
            client_after3
            client_rest
            client_tail_sent
            client_tail_received
            client_final /\
          CS.conn_events_received_decode_replay
            server_after3
            server_rest
            server_tail_sent
            server_tail_received
            server_final)

val lemma_server_encrypted_flight_produces_client_finished_replay_inputs_with_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_after_install:CS.connection_model)
  (client_after_install:CS.connection_model)
  (server_after0:CS.connection_model)
  (client_after0:CS.connection_model)
  (server_after1:CS.connection_model)
  (client_after1:CS.connection_model)
  (server_after_auth_skip:CS.connection_model)
  (client_after_auth_skip:CS.connection_model)
  (server_after2:CS.connection_model)
  (client_after2:CS.connection_model)
  (client_after_verify_skip:CS.connection_model)
  (server_after3:CS.connection_model)
  (client_after3:CS.connection_model)
  (server_auth_skip:CS.local_event)
  (client_auth_skip:CS.local_event)
  (client_verify_skip:CS.local_event)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (server_rest:list CS.conn_event)
  (client_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned client server /\
        local_event_does_not_install_record_keys server_auth_skip /\
        local_event_does_not_install_record_keys client_auth_skip /\
        local_event_does_not_install_record_keys client_verify_skip /\
        Seq.equal client_raw_sent server_raw_received /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            })) == Some server_after_install /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            })) == Some client_after_install /\
        CS.step_model
          server_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        CS.step_model
          client_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        CS.step_model
          server_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        CS.step_model
          client_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        CS.step_model server_after1 (CS.ConnLocalEvent server_auth_skip) ==
          Some server_after_auth_skip /\
        CS.step_model client_after1 (CS.ConnLocalEvent client_auth_skip) ==
          Some client_after_auth_skip /\
        CS.step_model
          server_after_auth_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        CS.step_model
          client_after_auth_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        CS.step_model client_after2 (CS.ConnLocalEvent client_verify_skip) ==
          Some client_after_verify_skip /\
        CS.step_model
          server_after2
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg3;
          }) == Some server_after3 /\
        CS.step_model
          client_after_verify_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg3;
          }) == Some client_after3 /\
        CS.conn_events_sent_seal_replay
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg0;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg1;
            } :: CS.ConnLocalEvent client_auth_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg2;
            } :: CS.ConnLocalEvent client_verify_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg3;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final /\
        CS.conn_events_received_decode_replay
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg0;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg1;
            } :: CS.ConnLocalEvent server_auth_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg2;
            } :: CS.ConnNetworkEvent {
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
          CS.conn_events_sent_seal_replay
            client_after3
            client_rest
            client_tail_sent
            client_tail_received
            client_final /\
          CS.conn_events_received_decode_replay
            server_after3
            server_rest
            server_tail_sent
            server_tail_received
            server_final)

val lemma_server_encrypted_flight_preserves_client_write_server_read_alignment
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_after_install:CS.connection_model)
  (client_after_install:CS.connection_model)
  (server_after0:CS.connection_model)
  (client_after0:CS.connection_model)
  (server_after1:CS.connection_model)
  (client_after1:CS.connection_model)
  (server_after_auth_skip:CS.connection_model)
  (client_after_auth_skip:CS.connection_model)
  (server_after2:CS.connection_model)
  (client_after2:CS.connection_model)
  (client_after_verify_skip:CS.connection_model)
  (server_after3:CS.connection_model)
  (client_after3:CS.connection_model)
  (server_auth_skip:CS.local_event)
  (client_auth_skip:CS.local_event)
  (client_verify_skip:CS.local_event)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
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
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            })) == Some server_after_install /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            })) == Some client_after_install /\
        CS.step_model
          server_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        CS.step_model
          client_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        CS.step_model
          server_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        CS.step_model
          client_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        CS.step_model server_after1 (CS.ConnLocalEvent server_auth_skip) ==
          Some server_after_auth_skip /\
        CS.step_model client_after1 (CS.ConnLocalEvent client_auth_skip) ==
          Some client_after_auth_skip /\
        CS.step_model
          server_after_auth_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        CS.step_model
          client_after_auth_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        CS.step_model client_after2 (CS.ConnLocalEvent client_verify_skip) ==
          Some client_after_verify_skip /\
        CS.step_model
          server_after2
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg3;
          }) == Some server_after3 /\
        CS.step_model
          client_after_verify_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg3;
          }) == Some client_after3)
      (ensures write_read_record_material_aligned client_after3 server_after3)
