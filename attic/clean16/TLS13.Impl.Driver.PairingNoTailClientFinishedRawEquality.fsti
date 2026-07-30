module TLS13.Impl.Driver.PairingNoTailClientFinishedRawEquality

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module EC = TLS13.Spec.Endpoint.Client
module ES = TLS13.Spec.Endpoint.Server
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module Seq = FStar.Seq
module Staged = TLS13.Impl.Driver.PairingNoTailClientFinishedStaged
module T = TLS13.Types

noextract
let paired_client_finished_raw_record_equality
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  exists client_ch_raw server_ch_raw client_finished_raw server_finished_raw.
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append client_ch_raw client_finished_raw) /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_received
      (B.append server_ch_raw server_finished_raw) /\
    CS.raw_records_exactly client_finished_raw T.Application_data 1 /\
    CS.raw_records_exactly server_finished_raw T.Application_data 1 /\
    Seq.equal client_finished_raw server_finished_raw

val lemma_paired_no_tail_client_finished_staged_milestone_client_finished_raw_record_equality
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        Staged.paired_no_tail_client_finished_staged_milestone client server)
      (ensures paired_client_finished_raw_record_equality client server)

val lemma_clean16_no_tail_valid_byte_traces_client_finished_raw_record_equality
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
      (ensures paired_client_finished_raw_record_equality client server)
