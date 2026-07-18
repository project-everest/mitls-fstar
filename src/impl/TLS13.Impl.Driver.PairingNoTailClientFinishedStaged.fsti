module TLS13.Impl.Driver.PairingNoTailClientFinishedStaged

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module EC = TLS13.Spec.Endpoint.Client
module ES = TLS13.Spec.Endpoint.Server
module M = TLS13.Messages
module GFin  = TLS13.Wire.Generated.Finished
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PNTCSR = TLS13.Impl.Driver.PairingNoTailClientSentRawShape
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module T = TLS13.Types

noextract
let client_finished_model12_replay_slice
  (client:CS.connection_state)
  : prop =
  exists (model12:CS.connection_model) (rest8:list CS.conn_event) tail_sent tail_received.
    model12.CS.model_config.CS.config_role == CS.ClientEndpoint /\
    model12.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedReceived /\
    Some? model12.CS.model_handshake.CS.hs_server_finished /\
    Some? model12.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
    Some? model12.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
    FStar.List.Tot.length rest8 == 4 /\
    TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      model12
      rest8
      tail_sent
      tail_received
      client.CS.cs_model

noextract
let client_finished_model12_exact_suffix_replay_slice
  (client:CS.connection_state)
  : prop =
  exists
    (sf:GFin.finished)
    (e13 e14:CS.conn_event)
    (cf:GFin.finished)
    (model12:CS.connection_model)
    tail_sent
    tail_received.
    model12.CS.model_config.CS.config_role == CS.ClientEndpoint /\
    model12.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedReceived /\
    model12.CS.model_handshake.CS.hs_server_finished == Some sf /\
    Some? model12.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
    Some? model12.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
    model12.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
    model12.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
    PNTCAS.client_no_tail_application_install_cover e13 e14 /\
    TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      model12
      (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
       e13 ::
       e14 ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.Finished cf);
       }) ::
       [])
      tail_sent
      tail_received
      client.CS.cs_model

noextract
let paired_no_tail_client_finished_staged_milestone
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  client_finished_model12_replay_slice client /\
  client_finished_model12_exact_suffix_replay_slice client /\
  PNTCAS.client_no_tail_finished_sent_shape client /\
  PNTCSR.client_sent_cleartext_and_finished_raw_slices client /\
  PNTN.server_received_cleartext_and_client_finished_raw_slices server /\
  TLS13.Spec.StateMachine.Correspondence.paired_wire_logs client server

noextract
let client_finished_model12_exact_suffix_raw_record_slice
  (client:CS.connection_state)
  : prop =
  exists
    (sf:GFin.finished)
    (e13 e14:CS.conn_event)
    (cf:GFin.finished)
    (model12:CS.connection_model)
    tail_sent
    tail_received
    finished_raw.
    model12.CS.model_config.CS.config_role == CS.ClientEndpoint /\
    model12.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedReceived /\
    model12.CS.model_handshake.CS.hs_server_finished == Some sf /\
    Some? model12.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
    Some? model12.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
    model12.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
    model12.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
    PNTCAS.client_no_tail_application_install_cover e13 e14 /\
    TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      model12
      (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
       e13 ::
       e14 ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.Finished cf);
       }) ::
       [])
      tail_sent
      tail_received
      client.CS.cs_model /\
    Seq.equal tail_sent finished_raw /\
    CS.raw_records_exactly finished_raw T.Application_data 1

val lemma_client_finished_model12_exact_suffix_raw_record_slice
  (client:CS.connection_state)
  : Lemma
      (requires client_finished_model12_exact_suffix_replay_slice client)
      (ensures client_finished_model12_exact_suffix_raw_record_slice client)

val lemma_clean16_no_tail_valid_byte_traces_client_finished_staged_milestone
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
        paired_no_tail_client_finished_staged_milestone
          client
          server)

val lemma_clean16_no_tail_valid_byte_traces_client_finished_exact_suffix_raw_record_slice
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
      (ensures client_finished_model12_exact_suffix_raw_record_slice client)
