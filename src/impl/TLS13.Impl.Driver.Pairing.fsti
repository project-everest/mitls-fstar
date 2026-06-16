module TLS13.Impl.Driver.Pairing

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
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
  CS.paired_handshake_events client server

noextract
let client_x25519_key_share_projection
  (client:CS.connection_state)
  : prop =
  let hs = client.CS.cs_model.CS.model_handshake in
  match
    hs.CS.hs_start,
    hs.CS.hs_client_hello,
    hs.CS.hs_server_hello,
    hs.CS.hs_keys.CS.ks_shared_secret
  with
  | Some start, Some ch, Some sh, Some shared ->
    (match start.CS.start_client_key_share_private with
     | Some client_sk ->
       CS.client_hello_key_share ch == start.CS.start_client_key_share_public /\
       C.x25519_public_from_private client_sk ==
         start.CS.start_client_key_share_public /\
       C.x25519_shared client_sk (CS.server_hello_key_share sh) == Some shared
     | None ->
       False)
  | _, _, _, _ ->
    False

noextract
let server_x25519_key_share_projection
  (server:CS.connection_state)
  : prop =
  let hs = server.CS.cs_model.CS.model_handshake in
  match
    hs.CS.hs_server_selection,
    hs.CS.hs_client_hello,
    hs.CS.hs_server_hello,
    hs.CS.hs_keys.CS.ks_shared_secret
  with
  | Some selection, Some ch, Some sh, Some shared ->
    (match selection.CS.server_key_share_private with
     | Some server_sk ->
       CS.server_hello_key_share sh == selection.CS.server_key_share_public /\
       C.x25519_public_from_private server_sk ==
         selection.CS.server_key_share_public /\
       C.x25519_shared server_sk (CS.client_hello_key_share ch) == Some shared
     | None ->
       False)
  | _, _, _, _ ->
    False

noextract
let paired_cleartext_hello_messages
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  let client_hs = client.CS.cs_model.CS.model_handshake in
  let server_hs = server.CS.cs_model.CS.model_handshake in
  match
    client_hs.CS.hs_client_hello,
    server_hs.CS.hs_client_hello,
    client_hs.CS.hs_server_hello,
    server_hs.CS.hs_server_hello
  with
  | Some client_ch, Some server_ch, Some client_sh, Some server_sh ->
    client_ch == server_ch /\
    client_sh == server_sh
  | _, _, _, _ ->
    False

noextract
let paired_handshake_message_states
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  let client_hs = client.CS.cs_model.CS.model_handshake in
  let server_hs = server.CS.cs_model.CS.model_handshake in
  match
    client_hs.CS.hs_client_hello,
    server_hs.CS.hs_client_hello,
    client_hs.CS.hs_server_hello,
    server_hs.CS.hs_server_hello,
    client_hs.CS.hs_encrypted_extensions,
    server_hs.CS.hs_encrypted_extensions,
    client_hs.CS.hs_certificate,
    server_hs.CS.hs_certificate,
    client_hs.CS.hs_certificate_verify,
    server_hs.CS.hs_certificate_verify,
    client_hs.CS.hs_server_finished,
    server_hs.CS.hs_server_finished,
    client_hs.CS.hs_client_finished,
    server_hs.CS.hs_client_finished
  with
  | Some client_ch, Some server_ch,
    Some client_sh, Some server_sh,
    Some client_ee, Some server_ee,
    Some client_cert, Some server_cert,
    Some client_cv, Some server_cv,
    Some client_sf, Some server_sf,
    Some client_cf, Some server_cf ->
    client_ch == server_ch /\
    client_sh == server_sh /\
    client_ee == server_ee /\
    client_cert == server_cert /\
    client_cv == server_cv /\
    client_sf == server_sf /\
    client_cf == server_cf
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _ ->
    False

noextract
let client_server_driver_x25519_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  client_x25519_key_share_projection client /\
  server_x25519_key_share_projection server /\
  paired_cleartext_hello_messages client server

noextract
let client_server_driver_handshake_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  paired_handshake_message_states client server

noextract
let client_server_driver_supported_profile_derived_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  client_server_driver_x25519_projection_inputs client server /\
  client_server_driver_handshake_projection_inputs client server

val lemma_client_server_driver_paired_x25519_key_shares_from_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        client_server_driver_x25519_projection_inputs client server)
      (ensures CS.paired_x25519_key_shares client server)

val lemma_client_server_driver_paired_handshake_events_from_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        client_server_driver_handshake_projection_inputs client server)
      (ensures CS.paired_handshake_events client server)

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

noextract
let client_server_driver_supported_profile_application_record_state_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  CS.supported_profile_application_traffic_material_matches_expected client /\
  CS.supported_profile_application_traffic_material_matches_expected server /\
  CS.application_record_epochs_installed_for_role
    CS.ClientEndpoint
    client.CS.cs_model /\
  CS.application_record_epochs_installed_for_role
    CS.ServerEndpoint
    server.CS.cs_model

noextract
let client_server_driver_supported_profile_projected_state_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  client_server_driver_supported_profile_derived_projection_inputs client server /\
  client_server_driver_supported_profile_application_record_state_inputs
    client
    server

noextract
let client_server_driver_supported_profile_state_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  client_server_driver_supported_profile_derived_state_inputs client server /\
  client_server_driver_supported_profile_application_record_state_inputs
    client
    server

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
let client_server_driver_key_material_no_read_ahead_projection_inputs
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
  client_server_driver_supported_profile_projected_state_inputs client server

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
