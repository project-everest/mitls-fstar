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

(**
  A narrow package for exactly the server encrypted-flight part of
  [PairingStagedNormalizedBoundary.paired_supported_normalized_staged_replay_boundary_inputs].

  The two replay predicates start at the post-cleartext models
  [hcb_server_model5] and [hcb_client_model4], use the staged canonical event
  lists (server handshake write install; EE; Certificate; auth-skip;
  CertificateVerify; Finished; rest, and dually on the client), and expose the
  raw streams for that slice.
**)
noeq
type server_flight_replay_witnesses = {
  sfr_server_flight_rest: list CS.conn_event;
  sfr_client_flight_rest: list CS.conn_event;
  sfr_server_raw_sent: B.bytes;
  sfr_server_raw_received: B.bytes;
  sfr_client_raw_sent: B.bytes;
  sfr_client_raw_received: B.bytes;
  sfr_server_final: CS.connection_model;
  sfr_client_final: CS.connection_model;
}

noextract
let server_encrypted_flight_staged_replay_fragment
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  (r:server_flight_replay_witnesses)
  : prop =
  Seq.equal r.sfr_server_raw_sent r.sfr_client_raw_received /\
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
  CS.conn_events_sent_seal_replay
    w.PCB.hcb_server_model5
    (PWL.server_encrypted_flight_replay_events
      w.PCB.hcb_server_material
      w.PCB.hcb_sent_msg0
      w.PCB.hcb_sent_msg1
      w.PCB.hcb_server_auth_skip
      w.PCB.hcb_sent_msg2
      w.PCB.hcb_sent_msg3
      r.sfr_server_flight_rest)
    r.sfr_server_raw_sent
    r.sfr_server_raw_received
    r.sfr_server_final /\
  CS.conn_events_received_decode_replay
    w.PCB.hcb_client_model4
    (PWL.client_receive_server_encrypted_flight_replay_events
      w.PCB.hcb_client_material
      w.PCB.hcb_received_msg0
      w.PCB.hcb_received_msg1
      w.PCB.hcb_client_auth_skip
      w.PCB.hcb_received_msg2
      w.PCB.hcb_client_verify_skip
      w.PCB.hcb_received_msg3
      r.sfr_client_flight_rest)
    r.sfr_client_raw_sent
    r.sfr_client_raw_received
    r.sfr_client_final

(**
  Current clean16 milestones do not yet expose enough information to construct
  the fragment above for an arbitrary [handshake_complete_boundary_witnesses].
  This predicate names the exact remaining fact needed to finish the
  server-flight part of the staged normalized boundary from those milestones.
**)
noextract
let clean16_server_encrypted_flight_semantic_replay_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : prop =
  PNTSFS.clean16_server_encrypted_flight_staged_milestone client server ==>
  exists r.
    server_encrypted_flight_staged_replay_fragment client server w r

val lemma_server_encrypted_flight_staged_replay_fragment_from_normalized_replay_boundary_inputs
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

val lemma_clean16_server_encrypted_flight_staged_replay_fragment_from_completion
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
