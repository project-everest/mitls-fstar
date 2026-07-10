module TLS13.ConnectionState.ProtectedWireClientFinished

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module GFin = TLS13.Wire.Generated.Finished
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

open TLS13.ConnectionState.ProtectedWireBase

val lemma_protected_handshake_event_projection_pair_after_client_write_server_read_install_heads_with_tails
  (client:CS.connection_model)
  (server:CS.connection_model)
  (client_material:CS.traffic_key_material)
  (server_material:CS.traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (client_rest:list CS.conn_event)
  (server_rest:list CS.conn_event)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_final:CS.connection_model)
  (server_final:CS.connection_model)
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
        Seq.equal client_raw_sent server_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = client_material;
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
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
                CS.install_direction = CS.TrafficRead;
                CS.install_material = server_material;
              };
            }) :: CS.ConnNetworkEvent {
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
              })) == Some server_after /\
          CS.step_model
            client_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some client_after_head /\
          CS.step_model
            server_after
            (CS.ConnNetworkEvent {
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
          CS.conn_events_sent_seal_replay
            client_after_head
            client_rest
            client_tail_sent
            client_tail_received
            client_final /\
          CS.conn_events_received_decode_replay
            server_after_head
            server_rest
            server_tail_sent
            server_tail_received
            server_final)

val lemma_protected_handshake_event_projection_pair_after_client_finished_local_skips_with_tails
  (client:CS.connection_model)
  (server:CS.connection_model)
  (client_after_verify:CS.connection_model)
  (client_after_app_write:CS.connection_model)
  (client_after_app_read:CS.connection_model)
  (server_after_app_write:CS.connection_model)
  (client_after_finished:CS.connection_model)
  (server_after_finished:CS.connection_model)
  (verified_server_finished:GFin.finished)
  (client_app_write_material:CS.traffic_key_material)
  (client_app_read_material:CS.traffic_key_material)
  (server_app_write_material:CS.traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (client_rest:list CS.conn_event)
  (server_rest:list CS.conn_event)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_final:CS.connection_model)
  (server_final:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned client server /\
        Seq.equal client_raw_sent server_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.step_model
          client
          (CS.ConnLocalEvent (CS.LocalVerifyFinished verified_server_finished)) ==
          Some client_after_verify /\
        CS.step_model
          client_after_verify
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = client_app_write_material;
            })) == Some client_after_app_write /\
        CS.step_model
          client_after_app_write
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_app_read_material;
            })) == Some client_after_app_read /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_app_write_material;
              };
            })) == Some server_after_app_write /\
        CS.step_model
          client_after_app_read
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some client_after_finished /\
        CS.step_model
          server_after_app_write
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some server_after_finished /\
        CS.conn_events_sent_seal_replay
          client
          (CS.ConnLocalEvent (CS.LocalVerifyFinished verified_server_finished) ::
           CS.ConnLocalEvent
             (CS.LocalInstallTrafficKeys {
               CS.install_epoch = CS.TrafficApplication;
               CS.install_direction = CS.TrafficWrite;
               CS.install_material = client_app_write_material;
             }) ::
           CS.ConnLocalEvent
             (CS.LocalInstallTrafficKeys {
               CS.install_epoch = CS.TrafficApplication;
               CS.install_direction = CS.TrafficRead;
               CS.install_material = client_app_read_material;
             }) ::
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake sent_msg;
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
                 CS.install_epoch = CS.TrafficApplication;
                 CS.install_direction = CS.TrafficWrite;
                 CS.install_material = server_app_write_material;
               };
             }) ::
           CS.ConnNetworkEvent {
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
          CS.conn_events_sent_seal_replay
            client_after_finished
            client_rest
            client_tail_sent
            client_tail_received
            client_final /\
          CS.conn_events_received_decode_replay
            server_after_finished
            server_rest
            server_tail_sent
            server_tail_received
            server_final)
