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
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PSNB = TLS13.Impl.Driver.PairingStagedNormalizedBoundary
module PWL = TLS13.ConnectionState.ProtectedWireBase
module Seq = FStar.Seq
module Tac = FStar.Tactics

#push-options "--split_queries always --z3rlimit 10"

let lemma_client_finished_staged_replay_fragment_from_staged_boundary_inputs
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
=
  let r = {
    cfr_client_finished_write_install_source =
      s.PSNB.snb_client_finished_write_install_source;
    cfr_client_finished_read_install_source =
      s.PSNB.snb_client_finished_read_install_source;
    cfr_client_finished_client_write_material =
      s.PSNB.snb_client_finished_client_write_material;
    cfr_client_finished_server_read_material =
      s.PSNB.snb_client_finished_server_read_material;
    cfr_client_finished_sender =
      s.PSNB.snb_client_finished_sender;
    cfr_client_finished_receiver =
      s.PSNB.snb_client_finished_receiver;
    cfr_client_finished_raw_sent =
      s.PSNB.snb_client_finished_raw_sent;
    cfr_client_finished_raw_received =
      s.PSNB.snb_client_finished_raw_received;
    cfr_server_finished_raw_sent =
      s.PSNB.snb_server_finished_raw_sent;
    cfr_server_finished_raw_received =
      s.PSNB.snb_server_finished_raw_received;
    cfr_client_finished_final =
      s.PSNB.snb_client_finished_final;
    cfr_server_finished_final =
      s.PSNB.snb_server_finished_final;
  } in
  assert (client_finished_staged_replay_fragment client server w r)
  by (
    Tac.norm
      [delta_only
        [`%PSNB.paired_supported_normalized_staged_replay_boundary_inputs;
         `%client_finished_staged_replay_fragment]];
    Tac.smt ());
  introduce exists (r':client_finished_replay_witnesses).
    client_finished_staged_replay_fragment client server w r'
  with r and ()

let lemma_clean16_client_finished_staged_replay_fragment_from_completion
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
=
  assert (exists r.
    client_finished_staged_replay_fragment client server w r)

let lemma_clean16_no_tail_valid_byte_traces_client_finished_staged_replay_fragment_from_completion
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  (w:PCB.handshake_complete_boundary_witnesses)
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
        clean16_client_finished_semantic_replay_completion client server w)
      (ensures
        exists r.
          client_finished_staged_replay_fragment client server w r)
=
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
  lemma_clean16_client_finished_staged_replay_fragment_from_completion
    client
    server
    w

#pop-options
