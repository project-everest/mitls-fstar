module TLS13.Impl.Driver.PairingNormalizedBridge

#lang-pulse

open Pulse.Lib.Pervasives

module CS = TLS13.Spec.ConnectionState
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PNB = TLS13.Impl.Driver.PairingNormalizedBoundary
module PNS = TLS13.Impl.Driver.PairingNormalizedShape

(**
  Bridge the normalized boundary/replay view used by
  [PairingNormalizedBoundary] to the smaller normalized replay-shape predicate
  used by [PairingNormalizedShape].

  This is still not the final no-tail inversion theorem: the precondition here
  is the existing normalized replay boundary.  The point of this module is to
  keep the protected projection witness construction private to the bridge and
  let downstream proofs depend on [PNS.paired_successful_handshake_normalized_replay_shape]
  instead of on exact trace shape or caller-supplied
  [Pairing.paired_protected_handshake_event_projection_pair_witnesses].
**)
val lemma_paired_successful_handshake_normalized_replay_shape_from_normalized_replay_boundary_inputs
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
        PNS.paired_successful_handshake_normalized_replay_shape
          client
          server)

val lemma_paired_successful_handshake_normalized_replay_shape_from_normalized_replay_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires PNB.paired_supported_normalized_replay_boundary client server)
      (ensures
        PNS.paired_successful_handshake_normalized_replay_shape
          client
          server)
