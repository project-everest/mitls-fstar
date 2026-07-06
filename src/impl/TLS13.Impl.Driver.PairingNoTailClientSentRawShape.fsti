module TLS13.Impl.Driver.PairingNoTailClientSentRawShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module Seq = FStar.Seq
module T = TLS13.Types

noextract
let client_sent_cleartext_and_finished_raw_slices
  (client:CS.connection_state)
  : prop =
  exists (ch:M.client_hello) (cf:M.finished) client_ch_raw client_finished_raw.
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append client_ch_raw client_finished_raw) /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello ch))
      client_ch_raw /\
    CS.raw_records_exactly client_finished_raw T.ApplicationData 1

val lemma_client_no_tail_finished_sent_raw_slices
  (client:CS.connection_state)
  : Lemma
      (requires
        PNTCAS.client_no_tail_finished_sent_shape client /\
        CS.connection_state_raw_event_replay_consistent client)
      (ensures client_sent_cleartext_and_finished_raw_slices client)
