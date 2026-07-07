module TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PNB = TLS13.Impl.Driver.PairingNormalizedBoundary
module PNTCFRE = TLS13.Impl.Driver.PairingNoTailClientFinishedRawEquality
module PNTCFR = TLS13.Impl.Driver.PairingNoTailClientFinishedReplay
module PNTCFS = TLS13.Impl.Driver.PairingNoTailClientFinishedStaged
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PNTSFR = TLS13.Impl.Driver.PairingNoTailServerFlightReplay
module PNTSFS = TLS13.Impl.Driver.PairingNoTailServerFlightStaged
module PSNB = TLS13.Impl.Driver.PairingStagedNormalizedBoundary
module Tac = FStar.Tactics

#push-options "--split_queries always --z3rlimit 10"

let lemma_clean16_no_tail_valid_byte_traces_staged_boundary_derivation_milestones
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        clean16_staged_boundary_derivation_milestones client server)
=
  PNTN.lemma_clean16_no_tail_valid_byte_traces_normalized_cleartext_replay_suffixes
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSFS.lemma_clean16_no_tail_valid_byte_traces_server_encrypted_flight_staged_milestone
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTCFS.lemma_clean16_no_tail_valid_byte_traces_client_finished_staged_milestone
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTCFRE.lemma_clean16_no_tail_valid_byte_traces_client_finished_raw_record_equality
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (clean16_staged_boundary_derivation_milestones client server)

let lemma_normalized_replay_boundary_inputs_with_staged_fragments
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  (server_fragment:PNTSFR.server_flight_replay_witnesses)
  (client_fragment:PNTCFR.client_finished_replay_witnesses)
  : Lemma
      (requires
        PNB.paired_supported_normalized_replay_boundary_inputs
          client
          server
          w /\
        PNTSFR.server_encrypted_flight_staged_replay_fragment
          client
          server
          w
          server_fragment /\
        PNTCFR.client_finished_staged_replay_fragment
          client
          server
          w
          client_fragment)
      (ensures
        PSNB.paired_supported_normalized_staged_replay_boundary client server)
=
  let s = {
    PSNB.snb_server_flight_rest =
      server_fragment.PNTSFR.sfr_server_flight_rest;
    PSNB.snb_client_flight_rest =
      server_fragment.PNTSFR.sfr_client_flight_rest;
    PSNB.snb_server_raw_sent =
      server_fragment.PNTSFR.sfr_server_raw_sent;
    PSNB.snb_server_raw_received =
      server_fragment.PNTSFR.sfr_server_raw_received;
    PSNB.snb_client_raw_sent =
      server_fragment.PNTSFR.sfr_client_raw_sent;
    PSNB.snb_client_raw_received =
      server_fragment.PNTSFR.sfr_client_raw_received;
    PSNB.snb_server_final =
      server_fragment.PNTSFR.sfr_server_final;
    PSNB.snb_client_final =
      server_fragment.PNTSFR.sfr_client_final;
    PSNB.snb_client_finished_write_install_source =
      client_fragment.PNTCFR.cfr_client_finished_write_install_source;
    PSNB.snb_client_finished_read_install_source =
      client_fragment.PNTCFR.cfr_client_finished_read_install_source;
    PSNB.snb_client_finished_client_write_material =
      client_fragment.PNTCFR.cfr_client_finished_client_write_material;
    PSNB.snb_client_finished_server_read_material =
      client_fragment.PNTCFR.cfr_client_finished_server_read_material;
    PSNB.snb_client_finished_sender =
      client_fragment.PNTCFR.cfr_client_finished_sender;
    PSNB.snb_client_finished_receiver =
      client_fragment.PNTCFR.cfr_client_finished_receiver;
    PSNB.snb_client_finished_raw_sent =
      client_fragment.PNTCFR.cfr_client_finished_raw_sent;
    PSNB.snb_client_finished_raw_received =
      client_fragment.PNTCFR.cfr_client_finished_raw_received;
    PSNB.snb_server_finished_raw_sent =
      client_fragment.PNTCFR.cfr_server_finished_raw_sent;
    PSNB.snb_server_finished_raw_received =
      client_fragment.PNTCFR.cfr_server_finished_raw_received;
    PSNB.snb_client_finished_final =
      client_fragment.PNTCFR.cfr_client_finished_final;
    PSNB.snb_server_finished_final =
      client_fragment.PNTCFR.cfr_server_finished_final;
  } in
  assert (PSNB.paired_supported_normalized_staged_replay_boundary_inputs client server w s)
  by (
    Tac.norm
      [delta_only
        [`%PNB.paired_supported_normalized_replay_boundary_inputs;
         `%PSNB.paired_supported_normalized_staged_replay_boundary_inputs;
         `%PNTSFR.server_encrypted_flight_staged_replay_fragment;
         `%PNTCFR.client_finished_staged_replay_fragment]];
    Tac.smt ());
  introduce exists (w':PCB.handshake_complete_boundary_witnesses)
                   (s':PSNB.staged_replay_witnesses).
    PSNB.paired_supported_normalized_staged_replay_boundary_inputs
      client
      server
      w'
      s'
  with w s and ()

let lemma_normalized_replay_boundary_inputs_with_clean16_fragment_completions
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : Lemma
      (requires
        PNB.paired_supported_normalized_replay_boundary_inputs
          client
          server
          w /\
        clean16_staged_boundary_derivation_milestones client server /\
        PNTSFR.clean16_server_encrypted_flight_semantic_replay_completion
          client
          server
          w /\
        PNTCFR.clean16_client_finished_semantic_replay_completion
          client
          server
          w)
      (ensures
        PSNB.paired_supported_normalized_staged_replay_boundary client server)
=
  PNTSFR.lemma_clean16_server_encrypted_flight_staged_replay_fragment_from_completion
    client
    server
    w;
  PNTCFR.lemma_clean16_client_finished_staged_replay_fragment_from_completion
    client
    server
    w;
  eliminate exists server_fragment.
    PNTSFR.server_encrypted_flight_staged_replay_fragment
      client
      server
      w
      server_fragment
  returns PSNB.paired_supported_normalized_staged_replay_boundary client server
  with _.
  (
    eliminate exists client_fragment.
      PNTCFR.client_finished_staged_replay_fragment
        client
        server
        w
        client_fragment
    returns PSNB.paired_supported_normalized_staged_replay_boundary client server
    with _.
    (
      lemma_normalized_replay_boundary_inputs_with_staged_fragments
        client
        server
        w
        server_fragment
        client_fragment
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_normalized_staged_replay_boundary_from_completion
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        clean16_staged_boundary_completion client server)
      (ensures
        PSNB.paired_supported_normalized_staged_replay_boundary client server)
=
  lemma_clean16_no_tail_valid_byte_traces_staged_boundary_derivation_milestones
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (clean16_staged_boundary_derivation_milestones client server);
  assert (PSNB.paired_supported_normalized_staged_replay_boundary client server)

let lemma_client_server_application_record_material_agrees_from_clean16_no_tail_valid_byte_traces_and_staged_boundary_completion
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        clean16_staged_boundary_completion client server)
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
  lemma_clean16_no_tail_valid_byte_traces_normalized_staged_replay_boundary_from_completion
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PSNB.lemma_client_server_application_record_material_agrees_from_normalized_staged_replay_boundary
    client
    server

#pop-options
