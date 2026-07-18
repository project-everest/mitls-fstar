module TLS13.Impl.Driver.PairingNoTailProtectedProjectionDerivation

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module GFin  = TLS13.Wire.Generated.Finished
module Pairing = TLS13.Impl.Driver.Pairing
module PWL = TLS13.ConnectionState.ProtectedWireBase
module R = TLS13.Record.Spec
module Seq = FStar.Seq

(**
  Narrow projection-facing bridge for the clean16 no-tail audit.

  This module deliberately does not depend on
  [PairingNoTailStagedBoundaryDerivation], so that that module can later import
  this one without creating a cycle.  The predicate below is exactly the
  installed-state replay surface consumed by
  [ProtectedWireStaged.lemma_paired_protected_handshake_event_projection_pair_witnesses_from_installed_server_flight_replays]:
  the server-flight slices start after the server-write/client-read handshake
  traffic keys are installed, while the ClientFinished slice starts from the real
  post-server-flight client-write/server-read installed states.
**)
noextract
unfold let installed_protected_projection_replay_inputs
  (client_state:CS.connection_state)
  (server_state:CS.connection_state)
  (server_flight_sender:CS.connection_model)
  (server_flight_receiver:CS.connection_model)
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
  (client_finished_sender:CS.connection_model)
  (client_finished_receiver:CS.connection_model)
  (cf_client_after_verify:CS.connection_model)
  (cf_client_after_app_write:CS.connection_model)
  (cf_client_after_app_read:CS.connection_model)
  (cf_server_after_app_write:CS.connection_model)
  (cf_client_after_finished:CS.connection_model)
  (cf_server_after_finished:CS.connection_model)
  (verified_server_finished:GFin.finished)
  (client_app_write_material:CS.traffic_key_material)
  (client_app_read_material:CS.traffic_key_material)
  (server_app_write_material:CS.traffic_key_material)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  (client_finished_rest:list CS.conn_event)
  (server_finished_rest:list CS.conn_event)
  (client_finished_raw_sent:B.bytes)
  (client_finished_raw_received:B.bytes)
  (server_finished_raw_sent:B.bytes)
  (server_finished_raw_received:B.bytes)
  (client_finished_final:CS.connection_model)
  (server_finished_final:CS.connection_model)
  : prop =
  (match
    client_state.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
    server_state.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
    client_state.CS.cs_model.CS.model_handshake.CS.hs_certificate,
    server_state.CS.cs_model.CS.model_handshake.CS.hs_certificate,
    client_state.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
    server_state.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
    client_state.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
    server_state.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
    client_state.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
    server_state.CS.cs_model.CS.model_handshake.CS.hs_client_finished
   with
   | Some client_ee, Some server_ee_msg,
     Some client_cert, Some server_cert_msg,
     Some client_cv, Some server_cv_msg,
     Some client_sf, Some server_sf,
     Some client_cf, Some server_cf ->
     sent_msg0 == M.EncryptedExtensions server_ee_msg /\
     received_msg0 == M.EncryptedExtensions client_ee /\
     sent_msg1 == M.Certificate server_cert_msg /\
     received_msg1 == M.Certificate client_cert /\
     sent_msg2 == M.CertificateVerify server_cv_msg /\
     received_msg2 == M.CertificateVerify client_cv /\
     sent_msg3 == M.Finished server_sf /\
     received_msg3 == M.Finished client_sf /\
     sent_msg4 == M.Finished client_cf /\
     received_msg4 == M.Finished server_cf
   | _, _, _, _, _, _, _, _, _, _ ->
     False) /\
  PWL.write_read_record_material_aligned
    server_flight_sender
    server_flight_receiver /\
  PWL.local_event_does_not_install_record_keys server_auth_skip /\
  PWL.local_event_does_not_install_record_keys client_auth_skip /\
  PWL.local_event_does_not_install_record_keys client_verify_skip /\
  Seq.equal server_raw_sent client_raw_received /\
  PWL.protected_handshake_wire_round_trip_message sent_msg0 /\
  PWL.protected_handshake_wire_round_trip_message received_msg0 /\
  PWL.protected_handshake_wire_round_trip_message sent_msg1 /\
  PWL.protected_handshake_wire_round_trip_message received_msg1 /\
  PWL.protected_handshake_wire_round_trip_message sent_msg2 /\
  PWL.protected_handshake_wire_round_trip_message received_msg2 /\
  PWL.protected_handshake_wire_round_trip_message sent_msg3 /\
  PWL.protected_handshake_wire_round_trip_message received_msg3 /\
  CS.step_model
    server_flight_sender
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake sent_msg0;
    }) == Some server_after0 /\
  CS.step_model
    server_flight_receiver
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake received_msg0;
    }) == Some client_after0 /\
  server_after0.CS.model_record.CS.record_write ==
    R.next_seq server_flight_sender.CS.model_record.CS.record_write /\
  client_after0.CS.model_record.CS.record_read ==
    R.next_seq server_flight_receiver.CS.model_record.CS.record_read /\
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
  TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
    server_flight_sender
    (CS.ConnNetworkEvent {
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
  TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
    server_flight_receiver
    (CS.ConnNetworkEvent {
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
  PWL.write_read_record_material_aligned
    client_finished_sender
    client_finished_receiver /\
  Seq.equal client_finished_raw_sent server_finished_raw_received /\
  PWL.protected_handshake_wire_round_trip_message sent_msg4 /\
  PWL.protected_handshake_wire_round_trip_message received_msg4 /\
  CS.step_model
    client_finished_sender
    (CS.ConnLocalEvent (CS.LocalVerifyFinished verified_server_finished)) ==
    Some cf_client_after_verify /\
  CS.step_model
    cf_client_after_verify
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = client_app_write_material;
      })) == Some cf_client_after_app_write /\
  CS.step_model
    cf_client_after_app_write
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = client_app_read_material;
      })) == Some cf_client_after_app_read /\
  CS.step_model
    client_finished_receiver
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = server_app_write_material;
        };
      })) == Some cf_server_after_app_write /\
  CS.step_model
    cf_client_after_app_read
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake sent_msg4;
    }) == Some cf_client_after_finished /\
  CS.step_model
    cf_server_after_app_write
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake received_msg4;
    }) == Some cf_server_after_finished /\
  TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
    client_finished_sender
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
       CL.message_value = M.TlsHandshake sent_msg4;
     } :: client_finished_rest)
    client_finished_raw_sent
    client_finished_raw_received
    client_finished_final /\
  TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
    client_finished_receiver
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
       CL.message_value = M.TlsHandshake received_msg4;
     } :: server_finished_rest)
    server_finished_raw_sent
    server_finished_raw_received
    server_finished_final

noeq
type installed_protected_projection_replay_witness_pack = {
  ippr_server_flight_sender: CS.connection_model;
  ippr_server_flight_receiver: CS.connection_model;
  ippr_server_after0: CS.connection_model;
  ippr_client_after0: CS.connection_model;
  ippr_server_after1: CS.connection_model;
  ippr_client_after1: CS.connection_model;
  ippr_server_after_auth_skip: CS.connection_model;
  ippr_client_after_auth_skip: CS.connection_model;
  ippr_server_after2: CS.connection_model;
  ippr_client_after2: CS.connection_model;
  ippr_client_after_verify_skip: CS.connection_model;
  ippr_server_after3: CS.connection_model;
  ippr_client_after3: CS.connection_model;
  ippr_server_auth_skip: CS.local_event;
  ippr_client_auth_skip: CS.local_event;
  ippr_client_verify_skip: CS.local_event;
  ippr_sent_msg0: M.handshake_msg;
  ippr_received_msg0: M.handshake_msg;
  ippr_sent_msg1: M.handshake_msg;
  ippr_received_msg1: M.handshake_msg;
  ippr_sent_msg2: M.handshake_msg;
  ippr_received_msg2: M.handshake_msg;
  ippr_sent_msg3: M.handshake_msg;
  ippr_received_msg3: M.handshake_msg;
  ippr_server_rest: list CS.conn_event;
  ippr_client_rest: list CS.conn_event;
  ippr_server_raw_sent: B.bytes;
  ippr_server_raw_received: B.bytes;
  ippr_client_raw_sent: B.bytes;
  ippr_client_raw_received: B.bytes;
  ippr_server_final: CS.connection_model;
  ippr_client_final: CS.connection_model;
  ippr_client_finished_sender: CS.connection_model;
  ippr_client_finished_receiver: CS.connection_model;
  ippr_cf_client_after_verify: CS.connection_model;
  ippr_cf_client_after_app_write: CS.connection_model;
  ippr_cf_client_after_app_read: CS.connection_model;
  ippr_cf_server_after_app_write: CS.connection_model;
  ippr_cf_client_after_finished: CS.connection_model;
  ippr_cf_server_after_finished: CS.connection_model;
  ippr_verified_server_finished: GFin.finished;
  ippr_client_app_write_material: CS.traffic_key_material;
  ippr_client_app_read_material: CS.traffic_key_material;
  ippr_server_app_write_material: CS.traffic_key_material;
  ippr_sent_msg4: M.handshake_msg;
  ippr_received_msg4: M.handshake_msg;
  ippr_client_finished_rest: list CS.conn_event;
  ippr_server_finished_rest: list CS.conn_event;
  ippr_client_finished_raw_sent: B.bytes;
  ippr_client_finished_raw_received: B.bytes;
  ippr_server_finished_raw_sent: B.bytes;
  ippr_server_finished_raw_received: B.bytes;
  ippr_client_finished_final: CS.connection_model;
  ippr_server_finished_final: CS.connection_model;
}

noextract
unfold let installed_protected_projection_replay_pack_inputs
  (client_state:CS.connection_state)
  (server_state:CS.connection_state)
  (w:installed_protected_projection_replay_witness_pack)
  : prop =
  installed_protected_projection_replay_inputs
    client_state
    server_state
    w.ippr_server_flight_sender
    w.ippr_server_flight_receiver
    w.ippr_server_after0
    w.ippr_client_after0
    w.ippr_server_after1
    w.ippr_client_after1
    w.ippr_server_after_auth_skip
    w.ippr_client_after_auth_skip
    w.ippr_server_after2
    w.ippr_client_after2
    w.ippr_client_after_verify_skip
    w.ippr_server_after3
    w.ippr_client_after3
    w.ippr_server_auth_skip
    w.ippr_client_auth_skip
    w.ippr_client_verify_skip
    w.ippr_sent_msg0
    w.ippr_received_msg0
    w.ippr_sent_msg1
    w.ippr_received_msg1
    w.ippr_sent_msg2
    w.ippr_received_msg2
    w.ippr_sent_msg3
    w.ippr_received_msg3
    w.ippr_server_rest
    w.ippr_client_rest
    w.ippr_server_raw_sent
    w.ippr_server_raw_received
    w.ippr_client_raw_sent
    w.ippr_client_raw_received
    w.ippr_server_final
    w.ippr_client_final
    w.ippr_client_finished_sender
    w.ippr_client_finished_receiver
    w.ippr_cf_client_after_verify
    w.ippr_cf_client_after_app_write
    w.ippr_cf_client_after_app_read
    w.ippr_cf_server_after_app_write
    w.ippr_cf_client_after_finished
    w.ippr_cf_server_after_finished
    w.ippr_verified_server_finished
    w.ippr_client_app_write_material
    w.ippr_client_app_read_material
    w.ippr_server_app_write_material
    w.ippr_sent_msg4
    w.ippr_received_msg4
    w.ippr_client_finished_rest
    w.ippr_server_finished_rest
    w.ippr_client_finished_raw_sent
    w.ippr_client_finished_raw_received
    w.ippr_server_finished_raw_sent
    w.ippr_server_finished_raw_received
    w.ippr_client_finished_final
    w.ippr_server_finished_final

noextract
let installed_protected_projection_replay_witnesses
  (client_state:CS.connection_state)
  (server_state:CS.connection_state)
  : prop =
  exists (w:installed_protected_projection_replay_witness_pack).
    installed_protected_projection_replay_pack_inputs
      client_state
      server_state
      w

val lemma_pairing_protected_projection_witnesses_from_installed_replay_inputs
  (client_state:CS.connection_state)
  (server_state:CS.connection_state)
  (server_flight_sender:CS.connection_model)
  (server_flight_receiver:CS.connection_model)
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
  (client_finished_sender:CS.connection_model)
  (client_finished_receiver:CS.connection_model)
  (cf_client_after_verify:CS.connection_model)
  (cf_client_after_app_write:CS.connection_model)
  (cf_client_after_app_read:CS.connection_model)
  (cf_server_after_app_write:CS.connection_model)
  (cf_client_after_finished:CS.connection_model)
  (cf_server_after_finished:CS.connection_model)
  (verified_server_finished:GFin.finished)
  (client_app_write_material:CS.traffic_key_material)
  (client_app_read_material:CS.traffic_key_material)
  (server_app_write_material:CS.traffic_key_material)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  (client_finished_rest:list CS.conn_event)
  (server_finished_rest:list CS.conn_event)
  (client_finished_raw_sent:B.bytes)
  (client_finished_raw_received:B.bytes)
  (server_finished_raw_sent:B.bytes)
  (server_finished_raw_received:B.bytes)
  (client_finished_final:CS.connection_model)
  (server_finished_final:CS.connection_model)
  : Lemma
      (requires
        installed_protected_projection_replay_inputs
          client_state
          server_state
          server_flight_sender
          server_flight_receiver
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
          client_final
          client_finished_sender
          client_finished_receiver
          cf_client_after_verify
          cf_client_after_app_write
          cf_client_after_app_read
          cf_server_after_app_write
          cf_client_after_finished
          cf_server_after_finished
          verified_server_finished
          client_app_write_material
          client_app_read_material
          server_app_write_material
          sent_msg4
          received_msg4
          client_finished_rest
          server_finished_rest
          client_finished_raw_sent
          client_finished_raw_received
          server_finished_raw_sent
          server_finished_raw_received
          client_finished_final
          server_finished_final)
      (ensures
        Pairing.paired_protected_handshake_event_projection_pair_witnesses
          client_state
          server_state)

val lemma_pairing_protected_projection_witnesses_from_installed_replay_witnesses
  (client_state:CS.connection_state)
  (server_state:CS.connection_state)
  : Lemma
      (requires
       installed_protected_projection_replay_witnesses
         client_state
         server_state)
      (ensures
       Pairing.paired_protected_handshake_event_projection_pair_witnesses
         client_state
         server_state)
