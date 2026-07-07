module TLS13.Impl.Driver.PairingNoTailServerFlightReplay

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PNB = TLS13.Impl.Driver.PairingNormalizedBoundary
module PNTSFS = TLS13.Impl.Driver.PairingNoTailServerFlightStaged
module PWL = TLS13.ConnectionState.ProtectedWireBase
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module Tac = FStar.Tactics

#push-options "--split_queries always --z3rlimit 10"

noextract
let normalized_replay_boundary_server_flight_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  : prop =
  Seq.equal server_raw_sent client_raw_received /\
  PWL.local_event_does_not_install_record_keys w.PCB.hcb_server_auth_skip /\
  PWL.local_event_does_not_install_record_keys w.PCB.hcb_client_auth_skip /\
  PWL.local_event_does_not_install_record_keys w.PCB.hcb_client_verify_skip /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg0 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg0 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg1 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg1 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg2 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg2 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg3 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg3 /\
  CS.step_model
    w.PCB.hcb_server_model5
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = w.PCB.hcb_server_material;
        };
      })) == Some w.PCB.hcb_server_after_install /\
  CS.step_model
    w.PCB.hcb_client_model4
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = w.PCB.hcb_client_material;
      })) == Some w.PCB.hcb_client_after_install /\
  CS.step_model
    w.PCB.hcb_server_after_install
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg0;
    }) == Some w.PCB.hcb_server_after0 /\
  CS.step_model
    w.PCB.hcb_client_after_install
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg0;
    }) == Some w.PCB.hcb_client_after0 /\
  w.PCB.hcb_server_after0.CS.model_record.CS.record_write ==
    R.next_seq w.PCB.hcb_server_after_install.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after0.CS.model_record.CS.record_read ==
    R.next_seq w.PCB.hcb_client_after_install.CS.model_record.CS.record_read /\
  CS.step_model
    w.PCB.hcb_server_after0
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg1;
    }) == Some w.PCB.hcb_server_after1 /\
  CS.step_model
    w.PCB.hcb_client_after0
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg1;
    }) == Some w.PCB.hcb_client_after1 /\
  w.PCB.hcb_server_after1.CS.model_record.CS.record_write ==
    R.next_seq w.PCB.hcb_server_after0.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after1.CS.model_record.CS.record_read ==
    R.next_seq w.PCB.hcb_client_after0.CS.model_record.CS.record_read /\
  CS.step_model
    w.PCB.hcb_server_after1
    (CS.ConnLocalEvent w.PCB.hcb_server_auth_skip) ==
    Some w.PCB.hcb_server_after_auth_skip /\
  CS.step_model
    w.PCB.hcb_client_after1
    (CS.ConnLocalEvent w.PCB.hcb_client_auth_skip) ==
    Some w.PCB.hcb_client_after_auth_skip /\
  CS.step_model
    w.PCB.hcb_server_after_auth_skip
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg2;
    }) == Some w.PCB.hcb_server_after2 /\
  CS.step_model
    w.PCB.hcb_client_after_auth_skip
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg2;
    }) == Some w.PCB.hcb_client_after2 /\
  w.PCB.hcb_server_after2.CS.model_record.CS.record_write ==
    R.next_seq w.PCB.hcb_server_after_auth_skip.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after2.CS.model_record.CS.record_read ==
    R.next_seq w.PCB.hcb_client_after_auth_skip.CS.model_record.CS.record_read /\
  CS.step_model
    w.PCB.hcb_client_after2
    (CS.ConnLocalEvent w.PCB.hcb_client_verify_skip) ==
    Some w.PCB.hcb_client_after_verify_skip /\
  CS.step_model
    w.PCB.hcb_server_after2
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg3;
    }) == Some w.PCB.hcb_server_after3 /\
  CS.step_model
    w.PCB.hcb_client_after_verify_skip
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg3;
    }) == Some w.PCB.hcb_client_after3 /\
  w.PCB.hcb_server_after3.CS.model_record.CS.record_write ==
    R.next_seq w.PCB.hcb_server_after2.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after3.CS.model_record.CS.record_read ==
    R.next_seq w.PCB.hcb_client_after_verify_skip.CS.model_record.CS.record_read /\
  PWL.paired_protected_handshake_contiguous_replay_views
    w.PCB.hcb_server_model5
    w.PCB.hcb_client_model4
    w.PCB.hcb_server_material
    w.PCB.hcb_client_material
    w.PCB.hcb_sent_msg0
    w.PCB.hcb_received_msg0
    w.PCB.hcb_sent_msg1
    w.PCB.hcb_received_msg1
    w.PCB.hcb_server_auth_skip
    w.PCB.hcb_client_auth_skip
    w.PCB.hcb_sent_msg2
    w.PCB.hcb_received_msg2
    w.PCB.hcb_client_verify_skip
    w.PCB.hcb_sent_msg3
    w.PCB.hcb_received_msg3
    w.PCB.hcb_verified_server_finished
    w.PCB.hcb_client_app_write_material
    w.PCB.hcb_client_app_read_material
    w.PCB.hcb_server_app_write_material
    w.PCB.hcb_sent_msg4
    w.PCB.hcb_received_msg4
    w.PCB.hcb_client_finished_rest
    w.PCB.hcb_server_finished_rest
    server_raw_sent
    server_raw_received
    client_raw_sent
    client_raw_received
    server.CS.cs_model
    client.CS.cs_model

let lemma_server_encrypted_flight_staged_replay_fragment_from_normalized_replay_boundary_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : Lemma
      (requires
        PNB.paired_supported_normalized_replay_boundary_inputs
          client
          server
          w)
      (ensures
        exists r.
          server_encrypted_flight_staged_replay_fragment client server w r)
=
  assert (exists server_raw_sent server_raw_received client_raw_sent client_raw_received.
    normalized_replay_boundary_server_flight_inputs
      client
      server
      w
      server_raw_sent
      server_raw_received
      client_raw_sent
      client_raw_received)
  by (
    Tac.norm
      [delta_only
        [`%PNB.paired_supported_normalized_replay_boundary_inputs;
         `%normalized_replay_boundary_server_flight_inputs]];
    Tac.smt ());
  eliminate exists
    (server_raw_sent:B.bytes)
    (server_raw_received:B.bytes)
    (client_raw_sent:B.bytes)
    (client_raw_received:B.bytes).
    normalized_replay_boundary_server_flight_inputs
      client
      server
      w
      server_raw_sent
      server_raw_received
      client_raw_sent
      client_raw_received
  returns
    exists r.
      server_encrypted_flight_staged_replay_fragment client server w r
  with _.
  (
    let server_rest =
      PWL.server_receive_client_finished_replay_events
        w.PCB.hcb_server_app_write_material
        w.PCB.hcb_received_msg4
        w.PCB.hcb_server_finished_rest in
    let client_rest =
      PWL.client_finished_replay_events
        w.PCB.hcb_verified_server_finished
        w.PCB.hcb_client_app_write_material
        w.PCB.hcb_client_app_read_material
        w.PCB.hcb_sent_msg4
        w.PCB.hcb_client_finished_rest in
    let r = {
      sfr_server_flight_rest = server_rest;
      sfr_client_flight_rest = client_rest;
      sfr_server_raw_sent = server_raw_sent;
      sfr_server_raw_received = server_raw_received;
      sfr_client_raw_sent = client_raw_sent;
      sfr_client_raw_received = client_raw_received;
      sfr_server_final = server.CS.cs_model;
      sfr_client_final = client.CS.cs_model;
    } in
    assert (server_encrypted_flight_staged_replay_fragment client server w r)
    by (
      Tac.norm
        [delta_only
          [`%PNB.paired_supported_normalized_replay_boundary_inputs;
           `%normalized_replay_boundary_server_flight_inputs;
           `%server_encrypted_flight_staged_replay_fragment;
           `%PWL.paired_protected_handshake_contiguous_replay_views;
           `%PWL.server_protected_handshake_contiguous_replay_events;
           `%PWL.client_protected_handshake_contiguous_replay_events;
           `%PWL.server_encrypted_flight_replay_events;
           `%PWL.client_receive_server_encrypted_flight_replay_events;
           `%PWL.server_receive_client_finished_replay_events;
           `%PWL.client_finished_replay_events]];
      Tac.smt ());
    introduce exists (r':server_flight_replay_witnesses).
      server_encrypted_flight_staged_replay_fragment client server w r'
    with r and ()
  )

let lemma_clean16_server_encrypted_flight_staged_replay_fragment_from_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : Lemma
      (requires
        PNTSFS.clean16_server_encrypted_flight_staged_milestone
          client
          server /\
        clean16_server_encrypted_flight_semantic_replay_completion
          client
          server
          w)
      (ensures
        exists r.
          server_encrypted_flight_staged_replay_fragment client server w r)
=
  assert (exists r.
    server_encrypted_flight_staged_replay_fragment client server w r)

#pop-options
