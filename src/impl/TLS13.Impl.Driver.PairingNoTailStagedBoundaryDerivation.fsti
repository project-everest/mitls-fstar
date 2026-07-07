module TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module PNTCFRE = TLS13.Impl.Driver.PairingNoTailClientFinishedRawEquality
module PNTCFS = TLS13.Impl.Driver.PairingNoTailClientFinishedStaged
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PNTSFS = TLS13.Impl.Driver.PairingNoTailServerFlightStaged
module PSNB = TLS13.Impl.Driver.PairingStagedNormalizedBoundary

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
  PNTSFS.clean16_server_encrypted_flight_staged_milestone
    client
    server /\
  PNTCFS.paired_no_tail_client_finished_staged_milestone
    client
    server /\
  PNTCFRE.paired_client_finished_raw_record_equality
    client
    server

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
