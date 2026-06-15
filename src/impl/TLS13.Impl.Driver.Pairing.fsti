module TLS13.Impl.Driver.Pairing

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties

noextract
let endpoint_transport_logs_exact
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  : prop =
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent /\
  Seq.equal received st.CS.cs_wire_log.CL.raw_received

noextract
let paired_transport_histories
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  Seq.equal client_sent server_received /\
  Seq.equal server_sent client_received

noextract
let paired_driver_transport_logs_exact
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  endpoint_transport_logs_exact client client_received client_sent /\
  endpoint_transport_logs_exact server server_received server_sent /\
  paired_transport_histories
    client_received
    client_sent
    server_received
    server_sent

noextract
let paired_driver_transport_logs_accounted
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  CD.client_driver_sent_log_exact client client_sent /\
  SD.server_driver_sent_log_exact server server_sent /\
  CD.client_driver_received_log_accounted client client_received /\
  SD.server_driver_received_log_accounted server server_received /\
  paired_transport_histories
    client_received
    client_sent
    server_received
    server_sent

noextract
let paired_protocol_received_logs_accounted
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  B.length client.CS.cs_wire_log.CL.raw_received <=
    B.length server.CS.cs_wire_log.CL.raw_sent /\
  (forall b.
    SeqP.count b client.CS.cs_wire_log.CL.raw_received <=
    SeqP.count b server.CS.cs_wire_log.CL.raw_sent) /\
  B.length server.CS.cs_wire_log.CL.raw_received <=
    B.length client.CS.cs_wire_log.CL.raw_sent /\
  (forall b.
    SeqP.count b server.CS.cs_wire_log.CL.raw_received <=
    SeqP.count b client.CS.cs_wire_log.CL.raw_sent)

noextract
let paired_protocol_received_logs_exact_prefix
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  (exists client_retained.
     Seq.equal server.CS.cs_wire_log.CL.raw_sent
       (B.append client.CS.cs_wire_log.CL.raw_received client_retained)) /\
  (exists server_retained.
     Seq.equal client.CS.cs_wire_log.CL.raw_sent
       (B.append server.CS.cs_wire_log.CL.raw_received server_retained))

val lemma_paired_protocol_received_logs_accounted
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        paired_driver_transport_logs_accounted
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures paired_protocol_received_logs_accounted client server)

val lemma_paired_protocol_received_logs_exact_prefix
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        CD.client_driver_sent_log_exact client client_sent /\
        SD.server_driver_sent_log_exact server server_sent /\
        CD.client_driver_received_log_exact_prefix client client_received /\
        SD.server_driver_received_log_exact_prefix server server_received /\
        paired_transport_histories
          client_received
          client_sent
          server_received
          server_sent)
      (ensures paired_protocol_received_logs_exact_prefix client server)

noextract
let client_server_driver_key_material_prefix_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  CD.client_driver_application_ready client /\
  SD.server_driver_application_ready server /\
  CD.client_driver_sent_log_exact client client_sent /\
  SD.server_driver_sent_log_exact server server_sent /\
  CD.client_driver_received_log_exact_prefix client client_received /\
  SD.server_driver_received_log_exact_prefix server server_received /\
  paired_transport_histories
    client_received
    client_sent
    server_received
    server_sent /\
  CS.supported_profile_client_server_key_material_inputs_agree client server

val lemma_client_server_driver_key_material_agrees_from_prefixes
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        client_server_driver_key_material_prefix_inputs
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_protocol_received_logs_exact_prefix client server /\
        CS.supported_profile_client_server_key_material_agrees client server)

val lemma_paired_wire_logs_from_exact_transport
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        paired_driver_transport_logs_exact
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures CS.paired_wire_logs client server)

noextract
let client_server_driver_key_material_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  CD.client_driver_application_ready client /\
  SD.server_driver_application_ready server /\
  paired_driver_transport_logs_exact
    client
    server
    client_received
    client_sent
    server_received
    server_sent /\
  CS.supported_profile_client_server_key_material_inputs_agree client server

val lemma_client_server_driver_key_material_agrees
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        client_server_driver_key_material_inputs
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        CS.paired_wire_logs client server /\
        CS.supported_profile_client_server_key_material_agrees client server)
