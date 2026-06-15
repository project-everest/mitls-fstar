module TLS13.Impl.Driver.Pairing

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties

let lemma_paired_protocol_received_logs_accounted
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
=
  Seq.lemma_eq_elim client_received server_sent;
  Seq.lemma_eq_elim server_sent server.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim server_received client_sent;
  Seq.lemma_eq_elim client_sent client.CS.cs_wire_log.CL.raw_sent

let lemma_paired_protocol_received_logs_exact_prefix
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
=
  let client_retained =
    FStar.IndefiniteDescription.indefinite_description_ghost
      B.bytes
      (fun retained ->
        Seq.equal client_received
          (B.append client.CS.cs_wire_log.CL.raw_received retained)) in
  let server_retained =
    FStar.IndefiniteDescription.indefinite_description_ghost
      B.bytes
      (fun retained ->
        Seq.equal server_received
          (B.append server.CS.cs_wire_log.CL.raw_received retained)) in
  assert (Seq.equal client_received
    (B.append client.CS.cs_wire_log.CL.raw_received client_retained));
  assert (Seq.equal server_received
    (B.append server.CS.cs_wire_log.CL.raw_received server_retained));
  Seq.lemma_eq_elim server_sent server.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim client_received server_sent;
  assert (Seq.equal server.CS.cs_wire_log.CL.raw_sent
    (B.append client.CS.cs_wire_log.CL.raw_received client_retained));
  Seq.lemma_eq_elim client_sent client.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim server_received client_sent;
  assert (Seq.equal client.CS.cs_wire_log.CL.raw_sent
    (B.append server.CS.cs_wire_log.CL.raw_received server_retained));
  FStar.Classical.exists_intro
    (fun retained ->
      Seq.equal client.CS.cs_wire_log.CL.raw_sent
        (B.append server.CS.cs_wire_log.CL.raw_received retained))
    server_retained;
  FStar.Classical.exists_intro
    (fun retained ->
      Seq.equal server.CS.cs_wire_log.CL.raw_sent
        (B.append client.CS.cs_wire_log.CL.raw_received retained))
    client_retained

let lemma_client_server_driver_key_material_agrees_from_prefixes
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
=
  lemma_paired_protocol_received_logs_exact_prefix
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  CSL.lemma_supported_profile_client_server_key_material_agrees client server

let lemma_paired_wire_logs_from_exact_transport
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
=
  Seq.lemma_eq_elim client_sent client.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim server_received server.CS.cs_wire_log.CL.raw_received;
  Seq.lemma_eq_elim server_sent server.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim client_received client.CS.cs_wire_log.CL.raw_received

let lemma_client_server_driver_key_material_agrees
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
=
  lemma_paired_wire_logs_from_exact_transport
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  CSL.lemma_supported_profile_client_server_key_material_agrees client server
