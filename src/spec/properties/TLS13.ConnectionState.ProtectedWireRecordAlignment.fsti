module TLS13.ConnectionState.ProtectedWireRecordAlignment

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

open TLS13.ConnectionState.ProtectedWireBase

val lemma_client_traffic_peer_record_material_agrees_and_seq_write_read_aligned
  (epoch:CS.traffic_epoch)
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        client.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
          server.CS.cs_model.CS.model_record.CS.record_read.R.seq /\
        TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
          (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id epoch CS.ClientTraffic)
          client
          server)
      (ensures
        write_read_record_material_aligned
          client.CS.cs_model
          server.CS.cs_model)

val lemma_server_traffic_peer_record_material_agrees_and_seq_write_read_aligned
  (epoch:CS.traffic_epoch)
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        server.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
          client.CS.cs_model.CS.model_record.CS.record_read.R.seq /\
        TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
          (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id epoch CS.ServerTraffic)
          client
          server)
      (ensures
        write_read_record_material_aligned
          server.CS.cs_model
          client.CS.cs_model)


val lemma_step_received_network_event_preserves_record_write
  (model:CS.connection_model)
  (msg:M.tls_message)
  (model_after:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          }) == Some model_after)
      (ensures
        model_after.CS.model_record.CS.record_write ==
          model.CS.model_record.CS.record_write)

val lemma_step_sent_network_event_preserves_record_read
  (model:CS.connection_model)
  (msg:M.tls_message)
  (model_after:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          }) == Some model_after)
      (ensures
        model_after.CS.model_record.CS.record_read ==
          model.CS.model_record.CS.record_read)

val lemma_step_received_network_event_preserves_write_read_record_material_alignment
  (sender:CS.connection_model)
  (msg:M.tls_message)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          }) == Some sender_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver)

val lemma_step_sent_network_event_preserves_write_read_record_material_alignment
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (msg:M.tls_message)
  (receiver_after:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          }) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender receiver_after)

val lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
  (sender:CS.connection_model)
  (sender_msg:M.tls_message)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  (receiver_msg:M.tls_message)
  (receiver_after:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = sender_msg;
          }) == Some sender_after /\
        CS.step_model
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = receiver_msg;
          }) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver_after)

val lemma_step_non_install_local_event_preserves_record_layer
  (model:CS.connection_model)
  (ev:CS.local_event)
  (model_after:CS.connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys ev /\
        CS.step_model
          model
          (CS.ConnLocalEvent ev) == Some model_after)
      (ensures model_after.CS.model_record == model.CS.model_record)

val lemma_step_local_event_preserves_record_write
  (model:CS.connection_model)
  (ev:CS.local_event)
  (model_after:CS.connection_model)
  : Lemma
      (requires
        local_event_preserves_record_write ev /\
        CS.step_model
          model
          (CS.ConnLocalEvent ev) == Some model_after)
      (ensures
        model_after.CS.model_record.CS.record_write ==
          model.CS.model_record.CS.record_write)

val lemma_step_local_event_preserves_record_read
  (model:CS.connection_model)
  (ev:CS.local_event)
  (model_after:CS.connection_model)
  : Lemma
      (requires
        local_event_preserves_record_read ev /\
        CS.step_model
          model
          (CS.ConnLocalEvent ev) == Some model_after)
      (ensures
        model_after.CS.model_record.CS.record_read ==
          model.CS.model_record.CS.record_read)

val lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
  (sender:CS.connection_model)
  (ev:CS.local_event)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys ev /\
        CS.step_model
          sender
          (CS.ConnLocalEvent ev) == Some sender_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver)

val lemma_step_sender_local_event_preserves_write_read_record_material_alignment
  (sender:CS.connection_model)
  (ev:CS.local_event)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  : Lemma
      (requires
        local_event_preserves_record_write ev /\
        CS.step_model
          sender
          (CS.ConnLocalEvent ev) == Some sender_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver)

val lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (ev:CS.local_event)
  (receiver_after:CS.connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys ev /\
        CS.step_model
          receiver
          (CS.ConnLocalEvent ev) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender receiver_after)

val lemma_step_receiver_local_event_preserves_write_read_record_material_alignment
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (ev:CS.local_event)
  (receiver_after:CS.connection_model)
  : Lemma
      (requires
        local_event_preserves_record_read ev /\
        CS.step_model
          receiver
          (CS.ConnLocalEvent ev) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender receiver_after)

val lemma_next_seq_models_preserve_write_read_record_material_alignment
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sender_after:CS.connection_model)
  (receiver_after:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        sender_after.CS.model_record.CS.record_write ==
          R.next_seq sender.CS.model_record.CS.record_write /\
        receiver_after.CS.model_record.CS.record_read ==
          R.next_seq receiver.CS.model_record.CS.record_read)
      (ensures write_read_record_material_aligned sender_after receiver_after)

val lemma_server_handshake_write_client_handshake_read_install_aligned
  (server:CS.connection_model)
  (client:CS.connection_model)
  (material:CS.traffic_key_material)
  (server_after:CS.connection_model)
  (client_after:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = material;
              };
            })) == Some server_after /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = material;
            })) == Some client_after)
      (ensures write_read_record_material_aligned server_after client_after)

val lemma_server_handshake_write_client_handshake_read_install_materials_aligned
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (server_after:CS.connection_model)
  (client_after:CS.connection_model)
  : Lemma
      (requires
        TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees
          (TLS13.Spec.StateMachine.KeyMaterial.record_material_of_traffic_material server_material)
          (TLS13.Spec.StateMachine.KeyMaterial.record_material_of_traffic_material client_material) /\
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
            })) == Some client_after)
      (ensures write_read_record_material_aligned server_after client_after)

val lemma_server_handshake_install_materials_agree_from_key_schedule
  (server_hs:CS.handshake_state)
  (client_hs:CS.handshake_state)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  : Lemma
      (requires
        (match
          server_hs.CS.hs_keys.CS.ks_handshake_secret,
          client_hs.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal server_hs.CS.hs_transcript client_hs.CS.hs_transcript /\
        CS.traffic_install_matches_key_schedule_for_role
          CS.ServerEndpoint
          server_hs
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = server_material;
          } /\
        CS.traffic_install_matches_key_schedule
          client_hs
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = client_material;
          })
      (ensures
        TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees
          (TLS13.Spec.StateMachine.KeyMaterial.record_material_of_traffic_material server_material)
          (TLS13.Spec.StateMachine.KeyMaterial.record_material_of_traffic_material client_material))

val lemma_server_handshake_write_client_handshake_read_install_aligned_from_key_schedule
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (server_after:CS.connection_model)
  (client_after:CS.connection_model)
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
        CS.traffic_install_matches_key_schedule_for_role
          CS.ServerEndpoint
          server.CS.model_handshake
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = server_material;
          } /\
        CS.traffic_install_matches_key_schedule
          client.CS.model_handshake
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = client_material;
          } /\
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
            })) == Some client_after)
      (ensures write_read_record_material_aligned server_after client_after)

val lemma_client_handshake_write_server_handshake_read_install_aligned
  (client:CS.connection_model)
  (server:CS.connection_model)
  (material:CS.traffic_key_material)
  (client_after:CS.connection_model)
  (server_after:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = material;
            })) == Some client_after /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = material;
              };
            })) == Some server_after)
      (ensures write_read_record_material_aligned client_after server_after)

val lemma_client_handshake_write_server_handshake_read_install_materials_aligned
  (client:CS.connection_model)
  (server:CS.connection_model)
  (client_material:CS.traffic_key_material)
  (server_material:CS.traffic_key_material)
  (client_after:CS.connection_model)
  (server_after:CS.connection_model)
  : Lemma
      (requires
        TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees
          (TLS13.Spec.StateMachine.KeyMaterial.record_material_of_traffic_material client_material)
          (TLS13.Spec.StateMachine.KeyMaterial.record_material_of_traffic_material server_material) /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = client_material;
            })) == Some client_after /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = server_material;
              };
            })) == Some server_after)
      (ensures write_read_record_material_aligned client_after server_after)

val lemma_client_handshake_install_materials_agree_from_key_schedule
  (client_hs:CS.handshake_state)
  (server_hs:CS.handshake_state)
  (client_material:CS.traffic_key_material)
  (server_material:CS.traffic_key_material)
  : Lemma
      (requires
        (match
          client_hs.CS.hs_keys.CS.ks_handshake_secret,
          server_hs.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some client_secret, Some server_secret ->
          Seq.equal client_secret server_secret
        | _, _ ->
          False) /\
        Seq.equal client_hs.CS.hs_transcript server_hs.CS.hs_transcript /\
        CS.traffic_install_matches_key_schedule
          client_hs
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = client_material;
          } /\
        CS.traffic_install_matches_key_schedule_for_role
          CS.ServerEndpoint
          server_hs
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = server_material;
          })
      (ensures
        TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees
          (TLS13.Spec.StateMachine.KeyMaterial.record_material_of_traffic_material client_material)
          (TLS13.Spec.StateMachine.KeyMaterial.record_material_of_traffic_material server_material))

val lemma_client_handshake_write_server_handshake_read_install_aligned_from_key_schedule
  (client:CS.connection_model)
  (server:CS.connection_model)
  (client_material:CS.traffic_key_material)
  (server_material:CS.traffic_key_material)
  (client_after:CS.connection_model)
  (server_after:CS.connection_model)
  : Lemma
      (requires
        (match
          client.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          server.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some client_secret, Some server_secret ->
          Seq.equal client_secret server_secret
        | _, _ ->
          False) /\
        Seq.equal
          client.CS.model_handshake.CS.hs_transcript
          server.CS.model_handshake.CS.hs_transcript /\
        CS.traffic_install_matches_key_schedule
          client.CS.model_handshake
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = client_material;
          } /\
        CS.traffic_install_matches_key_schedule_for_role
          CS.ServerEndpoint
          server.CS.model_handshake
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = server_material;
          } /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = client_material;
            })) == Some client_after /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = server_material;
              };
            })) == Some server_after)
      (ensures write_read_record_material_aligned client_after server_after)
