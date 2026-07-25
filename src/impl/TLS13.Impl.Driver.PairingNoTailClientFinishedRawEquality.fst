module TLS13.Impl.Driver.PairingNoTailClientFinishedRawEquality

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module EC = TLS13.Spec.Endpoint.Client
module ES = TLS13.Spec.Endpoint.Server
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GFin  = TLS13.Wire.Generated.Finished
module PNTCSR = TLS13.Impl.Driver.PairingNoTailClientSentRawShape
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module Seq = FStar.Seq
module Staged = TLS13.Impl.Driver.PairingNoTailClientFinishedStaged
module T = TLS13.Types

let lemma_paired_no_tail_client_finished_staged_milestone_client_finished_raw_record_equality
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        Staged.paired_no_tail_client_finished_staged_milestone client server)
      (ensures paired_client_finished_raw_record_equality client server)
=
  assert (PNTCSR.client_sent_cleartext_and_finished_raw_slices client);
  assert (TLS13.Spec.StateMachine.Correspondence.paired_wire_logs client server);
  eliminate exists (ch:GCH.clientHello) (cf:GFin.finished) client_ch_raw client_finished_raw.
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append client_ch_raw client_finished_raw) /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello ch))
      client_ch_raw /\
    CS.raw_records_exactly client_finished_raw T.Application_data 1
  returns paired_client_finished_raw_record_equality client server
  with _.
  (
    assert (Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received);
    Seq.lemma_eq_elim
      server.CS.cs_wire_log.CL.raw_received
      client.CS.cs_wire_log.CL.raw_sent;
    assert (Seq.equal
      server.CS.cs_wire_log.CL.raw_received
      (B.append client_ch_raw client_finished_raw));
    assert (paired_client_finished_raw_record_equality client server)
  )

let lemma_clean16_no_tail_valid_byte_traces_client_finished_raw_record_equality
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
=
  Staged.lemma_clean16_no_tail_valid_byte_traces_client_finished_staged_milestone
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_paired_no_tail_client_finished_staged_milestone_client_finished_raw_record_equality
    client
    server
