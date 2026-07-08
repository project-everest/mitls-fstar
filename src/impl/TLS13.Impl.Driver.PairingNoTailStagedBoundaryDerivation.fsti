module TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
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
module WFL = TLS13.Spec.WireFormatLemmas

noextract
let clean16_cleartext_final_hello_slot_milestone
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  exists
    client_start
    client_ch
    client_sh
    client_shared
    client_rest
    server_ch
    selection
    server_shared
    server_sh
    server_rest.
    PNTRB.role_local_cleartext_prefix_shape
      client
      server
      client_start
      client_ch
      client_sh
      client_shared
      client_rest
      server_ch
      selection
      server_shared
      server_sh
      server_rest /\
    WFL.supported_client_hello_wire_profile client_ch /\
    PNTRB.normalized_cleartext_raw_wire_bridge
      client_ch
      server_ch
      client_sh
      server_sh /\
    client.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      Some client_ch /\
    client.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      Some client_sh /\
    server.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      Some server_ch /\
    server.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      Some server_sh

(**
  Narrow staging package derivable today from the clean16 no-tail byte-trace
  audit surface.

  This deliberately aggregates only already-verified role-local/raw milestones:
  normalized cleartext suffix replays, the server encrypted-flight staging
  milestone, the ClientFinished staging milestone, and the paired raw equality
  for the ClientFinished record.  The remaining proof obligation to close the
  final audit theorem is exactly to turn this package into
  [PSNB.paired_supported_normalized_staged_replay_boundary].
**)
noextract
let clean16_staged_boundary_derivation_milestones
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  PNTN.paired_no_tail_normalized_cleartext_replay_suffixes_clean16
    client
    server /\
  clean16_cleartext_final_hello_slot_milestone
    client
    server /\
  CD.client_driver_application_ready client /\
  SD.server_driver_application_ready server /\
  Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
    client
    server /\
  PNTSFS.clean16_server_encrypted_flight_staged_milestone
    client
    server /\
  PNTPH.server_no_tail_post_two_handshake_installs_tail_order
    server /\
  PNTSFR.server_post_server_hello_sent_seal_replay_slice
    server /\
  PNTSFR.server_post_server_hello_ordered_sent_seal_replay_slice
    server /\
  PNTSFR.server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice
    server /\
  PNTSFR.server_after_handshake_installs_sent_seal_replay_slice
    server /\
  PNTSFR.server_post_server_hello_received_decode_replay_slice
    server /\
  PNTSFR.server_post_server_hello_ordered_received_decode_replay_slice
    server /\
  PNTCFRR.server_client_finished_received_decode_suffix_replay_slice
    server /\
  PNTSFR.client_post_derive_received_decode_replay_slice
    client /\
  PNTSFR.client_post_derive_ordered_received_decode_replay_slice
    client /\
  PNTSFR.client_after_handshake_installs_received_decode_replay_slice
    client /\
  PNTCFS.paired_no_tail_client_finished_staged_milestone
    client
    server /\
  PNTCFRE.paired_client_finished_raw_record_equality
    client
    server /\
  CS.connection_state_sent_seal_replay_consistent client /\
  CS.connection_state_received_decode_replay_consistent client /\
  CS.connection_state_sent_seal_replay_consistent server /\
  CS.connection_state_received_decode_replay_consistent server

(**
  The precise remaining local/staged completion lemma.

  Keeping this as a named predicate makes the current gap explicit without
  reintroducing the old caller-supplied staged replay boundary.  A future proof
  should discharge this predicate by constructing the
  [PSNB.staged_replay_witnesses] from the milestones above, including the
  needed local install-order commute if the client application installs are
  observed in read-then-write order.
**)
noextract
let clean16_staged_boundary_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  clean16_staged_boundary_derivation_milestones client server ==>
  PSNB.paired_supported_normalized_staged_replay_boundary client server

(**
  Corrected remaining completion target.

  Unlike [clean16_staged_boundary_completion], this does not require satisfying
  the staged-v2 delayed ClientFinished handshake-install schedule.  It asks only
  for the normalized projection boundary: the clean16 milestones must be turned
  into protected projection witnesses, with the ClientFinished projection
  starting from the real post-server-flight states where the handshake write/read
  keys are already installed.
**)
noextract
let clean16_projection_boundary_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  clean16_staged_boundary_derivation_milestones client server ==>
  PSNB.paired_supported_normalized_projection_boundary_core client server

(**
  Cleartext half of the normalized projection boundary.

  This is intentionally split from
  [clean16_protected_projection_witnesses_completion].  The clean16 proof now has
  two precise remaining obligations instead of one opaque boundary assumption:
  normalized cleartext/raw facts, cleartext key-share agreement, first-epoch
  state facts, and the five protected-message projection witnesses.
**)
noextract
let clean16_projection_cleartext_boundary_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  clean16_staged_boundary_derivation_milestones client server ==>
  PSNB.paired_supported_normalized_projection_boundary_cleartext_core
    client
    server

(**
  The narrower remaining proof obligation.

  The normalized cleartext/raw and first-epoch facts are already part of
  [clean16_staged_boundary_derivation_milestones] via
  [PNTN.paired_no_tail_normalized_cleartext_replay_suffixes_clean16] and the
  clean16 trace predicate.  The cleartext key-share link is intentionally kept
  with the cleartext boundary; the protected completion below is just the
  protected-message projection witness package.
**)
noextract
let clean16_protected_projection_witnesses_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  clean16_staged_boundary_derivation_milestones client server ==>
  Pairing.paired_protected_handshake_event_projection_pair_witnesses
   client
   server

noextract
let clean16_installed_protected_projection_replay_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  clean16_staged_boundary_derivation_milestones client server ==>
  PNTPPD.installed_protected_projection_replay_witnesses
    client
    server

val lemma_clean16_no_tail_valid_byte_traces_cleartext_final_hello_slot_milestone
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
        clean16_cleartext_final_hello_slot_milestone client server)

val lemma_clean16_no_tail_valid_byte_traces_staged_boundary_derivation_milestones
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

val lemma_clean16_no_tail_valid_byte_traces_normalized_projection_boundary_from_completion
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
        clean16_projection_boundary_completion client server)
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

val lemma_client_server_application_record_material_agrees_from_clean16_no_tail_valid_byte_traces_and_staged_boundary_completion
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
