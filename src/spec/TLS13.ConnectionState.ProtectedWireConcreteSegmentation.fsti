module TLS13.ConnectionState.ProtectedWireConcreteSegmentation

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module GFin = TLS13.Wire.Generated.Finished
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module Seq = FStar.Seq

val lemma_paired_protected_handshake_contiguous_replay_views_from_cleartext_prefix_full_replays_known_start
  (server_model0:CS.connection_model)
  (client_model0:CS.connection_model)
  (start:CS.handshake_start)
  (ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (client_shared:C.x25519_shared_secret)
  (sh:GSH.serverHello)
  (server_model1:CS.connection_model)
  (server_model2:CS.connection_model)
  (server_model3:CS.connection_model)
  (server_model4:CS.connection_model)
  (server_model5:CS.connection_model)
  (client_model1:CS.connection_model)
  (client_model2:CS.connection_model)
  (client_model3:CS.connection_model)
  (client_model4:CS.connection_model)
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
  (verified_server_finished:GFin.finished)
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
          Some client_model4 /\
        CS.conn_events_sent_seal_replay
          server_model0
          (FStar.List.Tot.append server_prefix server_suffix)
          server_full_sent
          server_full_received
          server_final /\
        CS.conn_events_received_decode_replay
          server_model0
          (FStar.List.Tot.append server_prefix server_suffix)
          server_full_sent
          server_full_received
          server_final /\
        CS.conn_events_sent_seal_replay
          client_model0
          (FStar.List.Tot.append client_prefix client_suffix)
          client_full_sent
          client_full_received
          client_final /\
        CS.conn_events_received_decode_replay
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

val lemma_paired_protected_handshake_contiguous_replay_views_from_cleartext_prefix_state_logs_known_start
  (server:CS.connection_state)
  (client:CS.connection_state)
  (start:CS.handshake_start)
  (ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (client_shared:C.x25519_shared_secret)
  (sh:GSH.serverHello)
  (server_model1:CS.connection_model)
  (server_model2:CS.connection_model)
  (server_model3:CS.connection_model)
  (server_model4:CS.connection_model)
  (server_model5:CS.connection_model)
  (client_model1:CS.connection_model)
  (client_model2:CS.connection_model)
  (client_model3:CS.connection_model)
  (client_model4:CS.connection_model)
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
  (verified_server_finished:GFin.finished)
  (client_app_write_material:CS.traffic_key_material)
  (client_app_read_material:CS.traffic_key_material)
  (server_app_write_material:CS.traffic_key_material)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  (client_finished_rest:list CS.conn_event)
  (server_finished_rest:list CS.conn_event)
  : Lemma
      (requires (
        let server_model0 = CS.initial_model server.CS.cs_model.CS.model_config in
        let client_model0 = CS.initial_model client.CS.cs_model.CS.model_config in
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
          server.CS.cs_wire_log.CL.raw_sent
          client.CS.cs_wire_log.CL.raw_received /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_sent
          server.CS.cs_wire_log.CL.raw_received /\
        server.CS.cs_event_log ==
          FStar.List.Tot.append server_prefix server_suffix /\
        client.CS.cs_event_log ==
          FStar.List.Tot.append client_prefix client_suffix /\
        CS.connection_state_sent_seal_replay_consistent server /\
        CS.connection_state_received_decode_replay_consistent server /\
        CS.connection_state_sent_seal_replay_consistent client /\
        CS.connection_state_received_decode_replay_consistent client /\
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
            server.CS.cs_model
            client.CS.cs_model)
