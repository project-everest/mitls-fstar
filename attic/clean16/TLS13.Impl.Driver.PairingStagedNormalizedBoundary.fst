module TLS13.Impl.Driver.PairingStagedNormalizedBoundary

#lang-pulse

open Pulse.Lib.Pervasives

module CS = TLS13.Spec.ConnectionState
module Pairing = TLS13.Impl.Driver.Pairing
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PR = TLS13.Impl.Driver.PairingProtectedReplay

let lemma_client_server_application_record_material_agrees_from_normalized_projection_boundary_core
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_supported_normalized_projection_boundary_core client server)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  eliminate exists
    (w:normalized_projection_boundary_witnesses).
    paired_supported_normalized_projection_boundary_core_inputs client server w
  returns
    CS.supported_profile_client_server_key_material_agrees client server /\
    CS.peer_record_material_agrees
      (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
      client
      server /\
    CS.peer_record_material_agrees
      (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
      client
      server
  with _.
  (
    Pairing.lemma_client_server_application_record_material_agrees_from_cleartext_raw_key_shares_and_protected_event_projection_witnesses
      client
      server
      w.npb_client_ch
      w.npb_server_ch
      w.npb_client_sh
      w.npb_server_sh
      w.npb_client_ch_raw
      w.npb_server_ch_raw
      w.npb_client_sh_raw
      w.npb_server_sh_raw
  )

let lemma_client_server_application_record_material_agrees_from_normalized_projection_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_supported_normalized_projection_boundary client server)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  eliminate exists
    (w:PCB.handshake_complete_boundary_witnesses).
    paired_supported_normalized_projection_boundary_inputs client server w
  returns
    CS.supported_profile_client_server_key_material_agrees client server /\
    CS.peer_record_material_agrees
      (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
      client
      server /\
    CS.peer_record_material_agrees
      (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
      client
      server
  with _.
  (
    Pairing.lemma_client_server_application_record_material_agrees_from_cleartext_raw_key_shares_and_protected_event_projection_witnesses
      client
      server
      w.PCB.hcb_client_ch
      w.PCB.hcb_server_ch
      w.PCB.hcb_client_sh
      w.PCB.hcb_server_sh
      w.PCB.hcb_client_ch_raw
      w.PCB.hcb_server_ch_raw
      w.PCB.hcb_client_sh_raw
      w.PCB.hcb_server_sh_raw
  )

let lemma_client_server_application_record_material_agrees_from_normalized_staged_replay_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_supported_normalized_staged_replay_boundary client server)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  eliminate exists
    (w:PCB.handshake_complete_boundary_witnesses)
    (s:staged_replay_witnesses).
    paired_supported_normalized_staged_replay_boundary_inputs client server w s
  returns
    CS.supported_profile_client_server_key_material_agrees client server /\
    CS.peer_record_material_agrees
      (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
      client
      server /\
    CS.peer_record_material_agrees
      (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
      client
      server
  with _.
  (
    PR.lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_staged_replays_v2
      client
      server
      w.PCB.hcb_client_ch
      w.PCB.hcb_server_ch
      w.PCB.hcb_client_sh
      w.PCB.hcb_server_sh
      w.PCB.hcb_client_ch_raw
      w.PCB.hcb_server_ch_raw
      w.PCB.hcb_client_sh_raw
      w.PCB.hcb_server_sh_raw
      w.PCB.hcb_server_model5
      w.PCB.hcb_client_model4
      w.PCB.hcb_server_after_install
      w.PCB.hcb_client_after_install
      w.PCB.hcb_server_after0
      w.PCB.hcb_client_after0
      w.PCB.hcb_server_after1
      w.PCB.hcb_client_after1
      w.PCB.hcb_server_after_auth_skip
      w.PCB.hcb_client_after_auth_skip
      w.PCB.hcb_server_after2
      w.PCB.hcb_client_after2
      w.PCB.hcb_client_after_verify_skip
      w.PCB.hcb_server_after3
      w.PCB.hcb_client_after3
      w.PCB.hcb_server_auth_skip
      w.PCB.hcb_client_auth_skip
      w.PCB.hcb_client_verify_skip
      w.PCB.hcb_server_material
      w.PCB.hcb_client_material
      w.PCB.hcb_sent_msg0
      w.PCB.hcb_received_msg0
      w.PCB.hcb_sent_msg1
      w.PCB.hcb_received_msg1
      w.PCB.hcb_sent_msg2
      w.PCB.hcb_received_msg2
      w.PCB.hcb_sent_msg3
      w.PCB.hcb_received_msg3
      s.snb_server_flight_rest
      s.snb_client_flight_rest
      s.snb_server_raw_sent
      s.snb_server_raw_received
      s.snb_client_raw_sent
      s.snb_client_raw_received
      s.snb_server_final
      s.snb_client_final
      s.snb_client_finished_write_install_source
      s.snb_client_finished_read_install_source
      s.snb_client_finished_client_write_material
      s.snb_client_finished_server_read_material
      s.snb_client_finished_sender
      s.snb_client_finished_receiver
      w.PCB.hcb_cf_client_after_verify
      w.PCB.hcb_cf_client_after_app_write
      w.PCB.hcb_cf_client_after_app_read
      w.PCB.hcb_cf_server_after_app_write
      w.PCB.hcb_cf_client_after_finished
      w.PCB.hcb_cf_server_after_finished
      w.PCB.hcb_verified_server_finished
      w.PCB.hcb_client_app_write_material
      w.PCB.hcb_client_app_read_material
      w.PCB.hcb_server_app_write_material
      w.PCB.hcb_sent_msg4
      w.PCB.hcb_received_msg4
      w.PCB.hcb_client_finished_rest
      w.PCB.hcb_server_finished_rest
      s.snb_client_finished_raw_sent
      s.snb_client_finished_raw_received
      s.snb_server_finished_raw_sent
      s.snb_server_finished_raw_received
      s.snb_client_finished_final
      s.snb_server_finished_final
  )
