module TLS13.Impl.Driver.PairingNoTailClientFinishedReplay

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PNTCFRE = TLS13.Impl.Driver.PairingNoTailClientFinishedRawEquality
module PNTCFS = TLS13.Impl.Driver.PairingNoTailClientFinishedStaged
module PSNB = TLS13.Impl.Driver.PairingStagedNormalizedBoundary
module PWL = TLS13.ConnectionState.ProtectedWireBase
module Seq = FStar.Seq

(**
  A narrow package for exactly the ClientFinished part of
  [PairingStagedNormalizedBoundary.paired_supported_normalized_staged_replay_boundary_inputs].

  The sender replay starts at the explicit client-handshake-write installed
  model, runs local server-Finished verification, the canonical client
  application write/read installs, and the protected client Finished send.  The
  receiver replay starts at the explicit server-handshake-read installed model,
  runs the server application write install, and receives the protected client
  Finished.
**)
noeq
type client_finished_replay_witnesses = {
  cfr_client_finished_write_install_source: CS.connection_model;
  cfr_client_finished_read_install_source: CS.connection_model;
  cfr_client_finished_client_write_material: CS.traffic_key_material;
  cfr_client_finished_server_read_material: CS.traffic_key_material;
  cfr_client_finished_sender: CS.connection_model;
  cfr_client_finished_receiver: CS.connection_model;
  cfr_client_finished_raw_sent: B.bytes;
  cfr_client_finished_raw_received: B.bytes;
  cfr_server_finished_raw_sent: B.bytes;
  cfr_server_finished_raw_received: B.bytes;
  cfr_client_finished_final: CS.connection_model;
  cfr_server_finished_final: CS.connection_model;
}

noextract
let client_finished_staged_replay_fragment
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  (r:client_finished_replay_witnesses)
  : prop =
  CS.record_key_iv_material_agrees
    (CS.record_material_of_traffic_material
      r.cfr_client_finished_client_write_material)
    (CS.record_material_of_traffic_material
      r.cfr_client_finished_server_read_material) /\
  CS.step_model
    r.cfr_client_finished_write_install_source
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = r.cfr_client_finished_client_write_material;
      })) == Some r.cfr_client_finished_sender /\
  CS.step_model
    r.cfr_client_finished_read_install_source
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = r.cfr_client_finished_server_read_material;
        };
      })) == Some r.cfr_client_finished_receiver /\
  Seq.equal
    r.cfr_client_finished_raw_sent
    r.cfr_server_finished_raw_received /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg4 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg4 /\
  CS.step_model
    r.cfr_client_finished_sender
    (CS.ConnLocalEvent (CS.LocalVerifyFinished w.PCB.hcb_verified_server_finished)) ==
    Some w.PCB.hcb_cf_client_after_verify /\
  CS.step_model
    w.PCB.hcb_cf_client_after_verify
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = w.PCB.hcb_client_app_write_material;
      })) == Some w.PCB.hcb_cf_client_after_app_write /\
  CS.step_model
    w.PCB.hcb_cf_client_after_app_write
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = w.PCB.hcb_client_app_read_material;
      })) == Some w.PCB.hcb_cf_client_after_app_read /\
  CS.step_model
    r.cfr_client_finished_receiver
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = w.PCB.hcb_server_app_write_material;
        };
      })) == Some w.PCB.hcb_cf_server_after_app_write /\
  CS.step_model
    w.PCB.hcb_cf_client_after_app_read
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg4;
    }) == Some w.PCB.hcb_cf_client_after_finished /\
  CS.step_model
    w.PCB.hcb_cf_server_after_app_write
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg4;
    }) == Some w.PCB.hcb_cf_server_after_finished /\
  CS.conn_events_sent_seal_replay
    r.cfr_client_finished_sender
    (CS.ConnLocalEvent (CS.LocalVerifyFinished w.PCB.hcb_verified_server_finished) ::
     CS.ConnLocalEvent
       (CS.LocalInstallTrafficKeys {
         CS.install_epoch = CS.TrafficApplication;
         CS.install_direction = CS.TrafficWrite;
         CS.install_material = w.PCB.hcb_client_app_write_material;
       }) ::
     CS.ConnLocalEvent
       (CS.LocalInstallTrafficKeys {
         CS.install_epoch = CS.TrafficApplication;
         CS.install_direction = CS.TrafficRead;
         CS.install_material = w.PCB.hcb_client_app_read_material;
       }) ::
     CS.ConnNetworkEvent {
       CL.message_direction = CL.Sent;
       CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg4;
     } :: w.PCB.hcb_client_finished_rest)
    r.cfr_client_finished_raw_sent
    r.cfr_client_finished_raw_received
    r.cfr_client_finished_final /\
  CS.conn_events_received_decode_replay
    r.cfr_client_finished_receiver
    (CS.ConnLocalEvent
       (CS.LocalInstallTrafficKeysForRole {
         CS.install_role = CS.ServerEndpoint;
         CS.install_payload = {
           CS.install_epoch = CS.TrafficApplication;
           CS.install_direction = CS.TrafficWrite;
           CS.install_material = w.PCB.hcb_server_app_write_material;
         };
       }) ::
     CS.ConnNetworkEvent {
       CL.message_direction = CL.Received;
       CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg4;
     } :: w.PCB.hcb_server_finished_rest)
    r.cfr_server_finished_raw_sent
    r.cfr_server_finished_raw_received
    r.cfr_server_finished_final

(**
  The exact clean16 fact still needed for the ClientFinished side of the staged
  boundary.
**)
noextract
let clean16_client_finished_semantic_replay_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : prop =
  PNTCFS.paired_no_tail_client_finished_staged_milestone client server /\
  PNTCFRE.paired_client_finished_raw_record_equality client server ==>
  exists r.
    client_finished_staged_replay_fragment client server w r

val lemma_client_finished_staged_replay_fragment_from_staged_boundary_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  (s:PSNB.staged_replay_witnesses)
  : Lemma
      (requires
        PSNB.paired_supported_normalized_staged_replay_boundary_inputs
          client
          server
          w
          s)
      (ensures
        exists r.
          client_finished_staged_replay_fragment client server w r)

val lemma_clean16_client_finished_staged_replay_fragment_from_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : Lemma
      (requires
        PNTCFS.paired_no_tail_client_finished_staged_milestone client server /\
        PNTCFRE.paired_client_finished_raw_record_equality client server /\
        clean16_client_finished_semantic_replay_completion client server w)
      (ensures
        exists r.
          client_finished_staged_replay_fragment client server w r)
