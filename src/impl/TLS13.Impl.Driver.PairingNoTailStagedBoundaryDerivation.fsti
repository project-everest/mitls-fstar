module TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module EC = TLS13.Spec.Endpoint.Client
module ES = TLS13.Spec.Endpoint.Server
module CD = TLS13.Impl.Client.Driver
module M = TLS13.Messages
module Pairing = TLS13.Impl.Driver.Pairing
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PNB = TLS13.Impl.Driver.PairingNormalizedBoundary
module PNTCFRE = TLS13.Impl.Driver.PairingNoTailClientFinishedRawEquality
module PNTCFRR = TLS13.Impl.Driver.PairingNoTailClientFinishedReceiverReplay
module PNTCFR = TLS13.Impl.Driver.PairingNoTailClientFinishedReplay
module PNTCFS = TLS13.Impl.Driver.PairingNoTailClientFinishedStaged
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PNTPPD = TLS13.Impl.Driver.PairingNoTailProtectedProjectionDerivation
module PNTRB = TLS13.Impl.Driver.PairingNoTailRawBridge
module PNTSFR = TLS13.Impl.Driver.PairingNoTailServerFlightReplay
module PNTSFS = TLS13.Impl.Driver.PairingNoTailServerFlightStaged
module PNTPH = TLS13.Impl.Driver.PairingNoTailServerPostHelloShape
module PSNB = TLS13.Impl.Driver.PairingStagedNormalizedBoundary
module SD = TLS13.Impl.Server.Driver
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

module Foundation = TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Foundation

noextract
let clean16_cleartext_final_hello_slot_milestone
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  Foundation.clean16_cleartext_final_hello_slot_milestone client server

noextract
let clean16_staged_boundary_derivation_milestones
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  Foundation.clean16_staged_boundary_derivation_milestones client server

noextract
let clean16_staged_boundary_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  Foundation.clean16_staged_boundary_completion client server

noextract
let clean16_projection_boundary_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  Foundation.clean16_projection_boundary_completion client server

noextract
let clean16_projection_cleartext_boundary_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  Foundation.clean16_projection_cleartext_boundary_completion client server

noextract
let clean16_cleartext_key_shares_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  Foundation.clean16_cleartext_key_shares_completion client server

noextract
let clean16_server_hello_key_shares_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  Foundation.clean16_server_hello_key_shares_completion client server

noextract
let clean16_protected_projection_witnesses_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  Foundation.clean16_protected_projection_witnesses_completion client server

noextract
let clean16_installed_protected_projection_replay_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  Foundation.clean16_installed_protected_projection_replay_completion client server

val lemma_clean16_no_tail_valid_byte_traces_cleartext_final_hello_slot_milestone
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
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
        clean16_cleartext_final_hello_slot_milestone client server)

val lemma_clean16_no_tail_valid_byte_traces_staged_boundary_derivation_milestones
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
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

(**
  Verified ClientFinished-sender piece of
  [clean16_installed_protected_projection_replay_completion].

  Strengthening the milestone package with replay consistency discharges the
  sender-side gap: the staged ClientFinished milestone now canonically yields
  the installed ClientFinished sent/seal suffix used by
  [PNTPPD.installed_protected_projection_replay_inputs].  The remaining
  installed replay completion is to combine this slice with the installed
  server-flight/server-receiver slices and prove their cross-endpoint raw-stream
  equality and record-material alignment.
**)
val lemma_clean16_staged_boundary_derivation_milestones_client_finished_canonical_sent_seal_replay_slice
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires clean16_staged_boundary_derivation_milestones client server)
      (ensures PNTCFR.client_finished_canonical_sent_seal_replay_slice client)

val lemma_normalized_replay_boundary_inputs_with_staged_fragments
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

val lemma_normalized_replay_boundary_inputs_with_clean16_fragment_completions
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

val lemma_clean16_no_tail_valid_byte_traces_normalized_staged_replay_boundary_from_completion
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
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

val lemma_clean16_no_tail_valid_byte_traces_normalized_projection_boundary_from_completion
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
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
        clean16_projection_boundary_completion client server)
      (ensures
        PSNB.paired_supported_normalized_projection_boundary_core client server)

val lemma_clean16_projection_boundary_completion_from_split_completions
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
       clean16_projection_cleartext_boundary_completion client server /\
       clean16_protected_projection_witnesses_completion client server)
      (ensures clean16_projection_boundary_completion client server)

val lemma_clean16_projection_cleartext_boundary_completion_from_key_shares_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires clean16_cleartext_key_shares_completion client server)
      (ensures clean16_projection_cleartext_boundary_completion client server)

val lemma_clean16_cleartext_key_shares_completion_from_server_hello_key_shares_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires clean16_server_hello_key_shares_completion client server)
      (ensures clean16_cleartext_key_shares_completion client server)

val lemma_clean16_protected_projection_witnesses_completion_from_installed_replay_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        clean16_installed_protected_projection_replay_completion
          client
          server)
      (ensures
        clean16_protected_projection_witnesses_completion
          client
          server)

val lemma_clean16_projection_boundary_completion_from_cleartext_and_installed_replay_completions
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        clean16_projection_cleartext_boundary_completion
          client
          server /\
        clean16_installed_protected_projection_replay_completion
          client
          server)
      (ensures
        clean16_projection_boundary_completion
          client
          server)

val lemma_client_server_application_record_material_agrees_from_clean16_no_tail_valid_byte_traces_and_projection_boundary_completion
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
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
        clean16_projection_boundary_completion client server)
      (ensures
        TLS13.Spec.StateMachine.KeyMaterial.supported_profile_client_server_key_material_agrees client server /\
        TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
         (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ClientTraffic)
         client
         server /\
        TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
         (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ServerTraffic)
         client
         server)

val lemma_client_server_application_record_material_agrees_from_clean16_no_tail_valid_byte_traces_and_staged_boundary_completion
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
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
        TLS13.Spec.StateMachine.KeyMaterial.supported_profile_client_server_key_material_agrees client server /\
        TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
          (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
          (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)

val lemma_installed_protected_projection_replay_witnesses_from_milestones_and_hello_key_shares
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        clean16_staged_boundary_derivation_milestones client server /\
        WFL.paired_cleartext_hello_key_shares client server)
      (ensures
        PNTPPD.installed_protected_projection_replay_witnesses client server)

val lemma_paired_protected_witnesses_from_clean16_valid_byte_traces_and_hello_key_shares
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
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
        WFL.paired_cleartext_hello_key_shares client server)
      (ensures
        Pairing.paired_protected_handshake_event_projection_pair_witnesses client server)
