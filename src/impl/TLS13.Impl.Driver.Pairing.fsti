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
module WFL = TLS13.Spec.WireFormatLemmas

noextract
let endpoint_transport_logs_exact
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  : prop =
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent /\
  Seq.equal received st.CS.cs_wire_log.CL.raw_received

noextract
let endpoint_transport_received_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  : prop =
  B.length received == B.length st.CS.cs_wire_log.CL.raw_received

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

val lemma_endpoint_transport_received_exact_from_prefix_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  : Lemma
      (requires
        (exists retained.
          Seq.equal received
            (B.append st.CS.cs_wire_log.CL.raw_received retained)) /\
        endpoint_transport_received_no_read_ahead st received)
      (ensures Seq.equal received st.CS.cs_wire_log.CL.raw_received)

val lemma_paired_wire_logs_from_exact_prefix_no_read_ahead
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
        endpoint_transport_received_no_read_ahead client client_received /\
        endpoint_transport_received_no_read_ahead server server_received /\
        paired_transport_histories
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_driver_transport_logs_exact
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        CS.paired_wire_logs client server)

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

noextract
let client_server_driver_key_material_no_read_ahead_inputs
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
  CD.client_driver_received_no_read_ahead client client_received /\
  SD.server_driver_received_no_read_ahead server server_received /\
  paired_transport_histories
    client_received
    client_sent
    server_received
    server_sent /\
  CS.supported_profile_client_server_key_material_inputs_agree client server

noextract
let client_server_driver_supported_profile_derived_state_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  CS.paired_x25519_key_shares client server /\
  CS.paired_key_derivation_checkpoints client server

noextract
let client_x25519_key_share_projection
  (client:CS.connection_state)
  : prop =
  CS.client_x25519_key_share_projection client

noextract
let server_x25519_key_share_projection
  (server:CS.connection_state)
  : prop =
  CS.server_x25519_key_share_projection server

noextract
let paired_cleartext_hello_messages
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  CS.paired_cleartext_hello_messages client server

noextract
let paired_handshake_message_states
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  CS.paired_handshake_message_states client server

noextract
let paired_handshake_events
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  CS.paired_handshake_events client server

val lemma_paired_handshake_message_states_paired_cleartext_hello_messages
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_handshake_message_states client server)
      (ensures paired_cleartext_hello_messages client server)

noextract
let client_server_driver_x25519_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  CD.client_driver_application_ready client /\
  SD.server_driver_application_ready server /\
  paired_cleartext_hello_messages client server

noextract
let client_server_driver_application_derivation_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  CS.same_key_derivation_checkpoint CS.DeriveApplicationTraffic client server

val lemma_paired_handshake_message_states_application_derivation_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_handshake_message_states client server)
      (ensures
        client_server_driver_application_derivation_projection_inputs
          client
          server)

val lemma_paired_handshake_events_application_derivation_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_handshake_events client server)
      (ensures
        client_server_driver_application_derivation_projection_inputs
          client
          server)

noextract
let client_server_driver_supported_profile_derived_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  client_server_driver_x25519_projection_inputs client server /\
  client_server_driver_application_derivation_projection_inputs client server

val lemma_client_server_driver_paired_x25519_key_shares_from_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        client_server_driver_x25519_projection_inputs client server)
      (ensures CS.paired_x25519_key_shares client server)

val lemma_client_server_driver_paired_key_derivation_checkpoints_from_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        client_server_driver_supported_profile_derived_projection_inputs
          client
          server)
      (ensures CS.paired_key_derivation_checkpoints client server)

val lemma_client_server_driver_supported_profile_derived_state_inputs_from_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        client_server_driver_supported_profile_derived_projection_inputs
          client
          server)
      (ensures
        client_server_driver_supported_profile_derived_state_inputs
          client
          server)

val lemma_client_server_driver_supported_profile_derived_key_material_agrees
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        client_server_driver_supported_profile_derived_state_inputs client server)
      (ensures
        CS.connection_supported_profile_key_schedule_lineage client /\
        CS.connection_supported_profile_key_schedule_lineage server /\
        CS.supported_profile_all_derived_key_material_agrees client server)

val lemma_client_server_driver_application_record_epochs_installed
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server)
      (ensures
        CS.application_record_epochs_installed_for_role
          CS.ClientEndpoint
          client.CS.cs_model /\
        CS.application_record_epochs_installed_for_role
          CS.ServerEndpoint
          server.CS.cs_model)

noextract
let client_server_driver_supported_profile_application_record_state_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  CS.supported_profile_application_traffic_material_matches_expected client /\
  CS.supported_profile_application_traffic_material_matches_expected server

noextract
let client_server_driver_first_epoch_no_key_update_state_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  CS.first_epoch_application_traffic_material_no_key_update_invariant client /\
  CS.first_epoch_application_traffic_material_no_key_update_invariant server

val lemma_client_server_driver_supported_profile_application_record_state_inputs_from_first_epoch_no_key_update
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        client_server_driver_first_epoch_no_key_update_state_inputs
          client
          server)
      (ensures
        client_server_driver_supported_profile_application_record_state_inputs
          client
          server)

noextract
let client_server_driver_remaining_semantic_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  client_server_driver_supported_profile_derived_projection_inputs client server /\
  client_server_driver_supported_profile_application_record_state_inputs
    client
    server

noextract
let client_server_driver_supported_profile_projected_state_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  client_server_driver_remaining_semantic_projection_inputs client server

val lemma_client_server_driver_remaining_semantic_projection_inputs_from_cleartext_and_application_checkpoint
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        paired_cleartext_hello_messages client server /\
        client_server_driver_application_derivation_projection_inputs
          client
          server /\
        client_server_driver_supported_profile_application_record_state_inputs
          client
          server)
      (ensures
        client_server_driver_remaining_semantic_projection_inputs client server)

val lemma_client_server_driver_remaining_semantic_projection_inputs_from_cleartext_and_handshake_events
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        paired_cleartext_hello_messages client server /\
        paired_handshake_events client server /\
        client_server_driver_supported_profile_application_record_state_inputs
          client
          server)
      (ensures
        client_server_driver_remaining_semantic_projection_inputs client server)

noextract
let client_server_driver_supported_profile_state_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  client_server_driver_supported_profile_derived_state_inputs client server /\
  client_server_driver_supported_profile_application_record_state_inputs
    client
    server

val lemma_client_server_driver_remaining_semantic_projection_inputs_from_paired_handshake_message_states
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        paired_handshake_message_states client server /\
        client_server_driver_supported_profile_application_record_state_inputs
          client
          server)
      (ensures
        client_server_driver_remaining_semantic_projection_inputs client server)

val lemma_client_server_driver_supported_profile_state_inputs_from_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        client_server_driver_supported_profile_projected_state_inputs
          client
          server)
      (ensures
        client_server_driver_supported_profile_state_inputs
          client
          server)

val lemma_client_server_driver_supported_profile_key_material_inputs_agree
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        client_server_driver_supported_profile_state_inputs client server)
      (ensures
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server)

noextract
let client_server_driver_key_material_no_read_ahead_component_inputs
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
  CD.client_driver_received_no_read_ahead client client_received /\
  SD.server_driver_received_no_read_ahead server server_received /\
  paired_transport_histories
    client_received
    client_sent
    server_received
    server_sent /\
  client_server_driver_supported_profile_state_inputs client server

noextract
let client_server_driver_public_success_transport_inputs
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
  CD.client_driver_received_no_read_ahead client client_received /\
  SD.server_driver_received_no_read_ahead server server_received /\
  paired_transport_histories
    client_received
    client_sent
    server_received
    server_sent

noextract
let client_server_driver_key_material_no_read_ahead_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  client_server_driver_public_success_transport_inputs
    client
    server
    client_received
    client_sent
    server_received
    server_sent /\
  client_server_driver_remaining_semantic_projection_inputs client server

noextract
let client_server_driver_key_material_no_read_ahead_minimal_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  client_server_driver_public_success_transport_inputs
    client
    server
    client_received
    client_sent
    server_received
    server_sent /\
  paired_cleartext_hello_messages client server /\
  client_server_driver_application_derivation_projection_inputs client server /\
  client_server_driver_supported_profile_application_record_state_inputs
    client
    server

noextract
let client_server_driver_key_material_no_read_ahead_handshake_event_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  client_server_driver_public_success_transport_inputs
    client
    server
    client_received
    client_sent
    server_received
    server_sent /\
  paired_cleartext_hello_messages client server /\
  paired_handshake_events client server /\
  client_server_driver_supported_profile_application_record_state_inputs
    client
    server

noextract
let client_server_driver_key_material_no_read_ahead_paired_handshake_message_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  client_server_driver_public_success_transport_inputs
    client
    server
    client_received
    client_sent
    server_received
    server_sent /\
  paired_handshake_message_states client server /\
  client_server_driver_supported_profile_application_record_state_inputs
    client
    server

val lemma_client_server_driver_key_material_agrees_from_no_read_ahead
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        client_server_driver_key_material_no_read_ahead_inputs
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_driver_transport_logs_exact
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        CS.paired_wire_logs client server /\
        CS.supported_profile_client_server_key_material_agrees client server)

val lemma_client_server_driver_key_material_agrees_from_no_read_ahead_components
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        client_server_driver_key_material_no_read_ahead_component_inputs
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        paired_driver_transport_logs_exact
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        CS.paired_wire_logs client server /\
        CS.supported_profile_client_server_key_material_agrees client server)

val lemma_client_server_driver_key_material_agrees_from_public_success_components
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        client_server_driver_key_material_no_read_ahead_component_inputs
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        CS.supported_profile_all_derived_key_material_agrees client server /\
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        paired_driver_transport_logs_exact
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        CS.paired_wire_logs client server /\
        CS.supported_profile_client_server_key_material_agrees client server)

val lemma_client_server_driver_key_material_agrees_from_public_success_projections
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        client_server_driver_key_material_no_read_ahead_projection_inputs
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        client_server_driver_supported_profile_derived_state_inputs
          client
          server /\
        CS.supported_profile_all_derived_key_material_agrees client server /\
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        paired_driver_transport_logs_exact
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        CS.paired_wire_logs client server /\
        CS.supported_profile_client_server_key_material_agrees client server)

val lemma_client_server_driver_key_material_agrees_from_public_success_transport_and_semantics
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        client_server_driver_public_success_transport_inputs
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        client_server_driver_remaining_semantic_projection_inputs client server)
      (ensures
        client_server_driver_supported_profile_derived_state_inputs
          client
          server /\
        CS.supported_profile_all_derived_key_material_agrees client server /\
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        paired_driver_transport_logs_exact
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        CS.paired_wire_logs client server /\
        CS.supported_profile_client_server_key_material_agrees client server)

val lemma_client_server_driver_key_material_agrees_from_public_success_minimal_projections
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        client_server_driver_key_material_no_read_ahead_minimal_projection_inputs
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        client_server_driver_remaining_semantic_projection_inputs client server /\
        client_server_driver_supported_profile_derived_state_inputs
          client
          server /\
        CS.supported_profile_all_derived_key_material_agrees client server /\
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        paired_driver_transport_logs_exact
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        CS.paired_wire_logs client server /\
        CS.supported_profile_client_server_key_material_agrees client server)

val lemma_client_server_driver_key_material_agrees_from_public_success_cleartext_and_handshake_events
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        client_server_driver_key_material_no_read_ahead_handshake_event_inputs
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        client_server_driver_remaining_semantic_projection_inputs client server /\
        client_server_driver_supported_profile_derived_state_inputs
          client
          server /\
        CS.supported_profile_all_derived_key_material_agrees client server /\
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        paired_driver_transport_logs_exact
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        CS.paired_wire_logs client server /\
        CS.supported_profile_client_server_key_material_agrees client server)

val lemma_client_server_driver_key_material_agrees_from_public_success_paired_handshake_messages
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        client_server_driver_key_material_no_read_ahead_paired_handshake_message_inputs
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        client_server_driver_remaining_semantic_projection_inputs client server /\
        client_server_driver_supported_profile_derived_state_inputs
          client
          server /\
        CS.supported_profile_all_derived_key_material_agrees client server /\
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        paired_driver_transport_logs_exact
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        CS.paired_wire_logs client server /\
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

noextract
let client_server_driver_end_to_end_agreement_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  client_server_driver_key_material_no_read_ahead_component_inputs
    client
    server
    client_received
    client_sent
    server_received
    server_sent

val lemma_client_server_driver_end_to_end_key_material_agrees
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        client_server_driver_end_to_end_agreement_inputs
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        client_server_driver_supported_profile_derived_state_inputs
          client
          server /\
        CS.supported_profile_all_derived_key_material_agrees client server /\
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        paired_driver_transport_logs_exact
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        CS.paired_wire_logs client server /\
        CS.supported_profile_client_server_key_material_agrees client server)
