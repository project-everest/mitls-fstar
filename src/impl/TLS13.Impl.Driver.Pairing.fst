module TLS13.Impl.Driver.Pairing

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
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

let lemma_endpoint_transport_received_exact_from_prefix_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  : Lemma
      (requires
        (exists retained.
          Seq.equal received
            (B.append st.CS.cs_wire_log.CL.raw_received retained)) /\
        endpoint_transport_received_no_read_ahead st received)
      (ensures Seq.equal received st.CS.cs_wire_log.CL.raw_received)
=
  let retained =
    FStar.IndefiniteDescription.indefinite_description_ghost
      B.bytes
      (fun retained ->
        Seq.equal received
          (B.append st.CS.cs_wire_log.CL.raw_received retained)) in
  assert (Seq.equal received
    (B.append st.CS.cs_wire_log.CL.raw_received retained));
  Seq.lemma_len_append st.CS.cs_wire_log.CL.raw_received retained;
  Seq.lemma_eq_elim received (B.append st.CS.cs_wire_log.CL.raw_received retained);
  assert (B.length retained == 0);
  assert (B.length retained == B.length B.empty);
  assert (forall (i:nat{i < B.length retained}).
    Seq.index retained i == Seq.index B.empty i);
  Seq.lemma_eq_intro retained B.empty;
  Seq.lemma_eq_elim retained B.empty;
  Seq.append_empty_r st.CS.cs_wire_log.CL.raw_received;
  assert (Seq.equal
    (B.append st.CS.cs_wire_log.CL.raw_received B.empty)
    st.CS.cs_wire_log.CL.raw_received)

let lemma_paired_wire_logs_from_exact_prefix_no_read_ahead
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
=
  lemma_endpoint_transport_received_exact_from_prefix_no_read_ahead
    client
    client_received;
  lemma_endpoint_transport_received_exact_from_prefix_no_read_ahead
    server
    server_received;
  assert (paired_driver_transport_logs_exact
    client
    server
    client_received
    client_sent
    server_received
    server_sent);
  Seq.lemma_eq_elim client_sent client.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim server_received server.CS.cs_wire_log.CL.raw_received;
  Seq.lemma_eq_elim server_sent server.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim client_received client.CS.cs_wire_log.CL.raw_received

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

let lemma_client_server_driver_paired_x25519_key_shares_from_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        client_server_driver_x25519_projection_inputs client server)
      (ensures CS.paired_x25519_key_shares client server)
=
  assert (CS.stable_client_x25519_key_share_projection client);
  assert (CS.client_x25519_key_share_projection client);
  assert (CS.stable_server_x25519_key_share_projection server);
  assert (CS.server_x25519_key_share_projection server);
  let client_hs = client.CS.cs_model.CS.model_handshake in
  let server_hs = server.CS.cs_model.CS.model_handshake in
  match
    client_hs.CS.hs_start,
    client_hs.CS.hs_client_hello,
    client_hs.CS.hs_server_hello,
    client_hs.CS.hs_keys.CS.ks_shared_secret,
    server_hs.CS.hs_server_selection,
    server_hs.CS.hs_client_hello,
    server_hs.CS.hs_server_hello,
    server_hs.CS.hs_keys.CS.ks_shared_secret
  with
  | Some start, Some client_ch, Some client_sh, Some client_shared,
    Some selection, Some server_ch, Some server_sh, Some server_shared ->
    (match
      start.CS.start_client_key_share_private,
      selection.CS.server_key_share_private
     with
     | Some client_sk, Some server_sk ->
       assert (client_ch == server_ch);
       assert (client_sh == server_sh);
       assert (CS.client_hello_key_share client_ch ==
         start.CS.start_client_key_share_public);
       assert (CS.client_hello_key_share server_ch ==
         start.CS.start_client_key_share_public);
       assert (CS.server_hello_key_share server_sh ==
         selection.CS.server_key_share_public);
       assert (CS.server_hello_key_share client_sh ==
         selection.CS.server_key_share_public);
       assert (C.x25519_public_from_private client_sk ==
         start.CS.start_client_key_share_public);
       assert (C.x25519_public_from_private server_sk ==
         selection.CS.server_key_share_public);
       assert (C.x25519_shared client_sk (CS.server_hello_key_share client_sh) ==
         Some client_shared);
       assert (C.x25519_shared server_sk (CS.client_hello_key_share server_ch) ==
         Some server_shared)
     | _, _ ->
       assert False)
  | _, _, _, _, _, _, _, _ ->
    assert False

let lemma_client_server_driver_paired_handshake_events_from_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        client_server_driver_handshake_projection_inputs client server)
      (ensures CS.paired_handshake_events client server)
=
  ()

let lemma_client_server_driver_supported_profile_derived_state_inputs_from_projection_inputs
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
=
  lemma_client_server_driver_paired_x25519_key_shares_from_projection_inputs
    client
    server;
  lemma_client_server_driver_paired_handshake_events_from_projection_inputs
    client
    server

let lemma_client_server_driver_supported_profile_derived_key_material_agrees
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
=
  assert (CS.connection_state_consistent client);
  assert (CS.application_record_keys_installed_for_role
    CS.ClientEndpoint
    client.CS.cs_model);
  CSL.lemma_connection_application_keys_supported_profile_key_schedule_lineage
    CS.ClientEndpoint
    client;
  assert (CS.connection_state_consistent server);
  assert (CS.application_record_keys_installed_for_role
    CS.ServerEndpoint
    server.CS.cs_model);
  CSL.lemma_connection_application_keys_supported_profile_key_schedule_lineage
    CS.ServerEndpoint
    server;
  assert (CS.connection_supported_profile_key_schedule_lineage client);
  assert (CS.connection_supported_profile_key_schedule_lineage server);
  CSL.lemma_paired_supported_profile_all_derived_key_material_agrees
    client
    server

let lemma_client_server_driver_application_record_epochs_installed
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
=
  assert (CS.connection_state_consistent client);
  assert (client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
  assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
  assert (CS.application_record_keys_installed_for_role
    CS.ClientEndpoint
    client.CS.cs_model);
  CSL.lemma_connection_application_ready_record_epochs_installed
    CS.ClientEndpoint
    client;
  assert (CS.connection_state_consistent server);
  assert (server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
  assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
  assert (CS.application_record_keys_installed_for_role
    CS.ServerEndpoint
    server.CS.cs_model);
  CSL.lemma_connection_application_ready_record_epochs_installed
    CS.ServerEndpoint
    server

let lemma_client_server_driver_supported_profile_state_inputs_from_projection_inputs
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
=
  lemma_client_server_driver_supported_profile_derived_state_inputs_from_projection_inputs
    client
    server

let lemma_client_server_driver_supported_profile_key_material_inputs_agree
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
=
  lemma_client_server_driver_supported_profile_derived_key_material_agrees
    client
    server;
  assert (CS.connection_supported_profile_key_schedule_lineage client);
  assert (CS.connection_supported_profile_key_schedule_lineage server);
  assert (CS.supported_profile_all_derived_key_material_agrees client server);
  assert (CS.application_record_keys_installed_for_role
    CS.ClientEndpoint
    client.CS.cs_model);
  assert (CS.application_record_keys_installed_for_role
    CS.ServerEndpoint
    server.CS.cs_model);
  lemma_client_server_driver_application_record_epochs_installed
    client
    server;
  assert (CS.application_record_epochs_installed_for_role
    CS.ClientEndpoint
    client.CS.cs_model);
  assert (CS.application_record_epochs_installed_for_role
    CS.ServerEndpoint
    server.CS.cs_model);
  CSL.lemma_supported_profile_application_record_material_inputs_agree_from_expected
    client
    server;
  assert (CS.supported_profile_application_record_material_inputs_agree
    client
    server);
  assert (CS.supported_profile_client_server_key_material_inputs_agree
    client
    server)

let lemma_client_server_driver_key_material_agrees_from_no_read_ahead
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
=
  lemma_paired_wire_logs_from_exact_prefix_no_read_ahead
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  CSL.lemma_supported_profile_client_server_key_material_agrees client server

let lemma_client_server_driver_key_material_agrees_from_no_read_ahead_components
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
=
  lemma_client_server_driver_supported_profile_key_material_inputs_agree
    client
    server;
  lemma_client_server_driver_key_material_agrees_from_no_read_ahead
    client
    server
    client_received
    client_sent
    server_received
    server_sent

let lemma_client_server_driver_key_material_agrees_from_public_success_components
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
=
  lemma_client_server_driver_supported_profile_derived_key_material_agrees
    client
    server;
  lemma_client_server_driver_key_material_agrees_from_no_read_ahead_components
    client
    server
    client_received
    client_sent
    server_received
    server_sent

let lemma_client_server_driver_key_material_agrees_from_public_success_projections
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
=
  lemma_client_server_driver_supported_profile_state_inputs_from_projection_inputs
    client
    server;
  assert (client_server_driver_key_material_no_read_ahead_component_inputs
    client
    server
    client_received
    client_sent
    server_received
    server_sent);
  lemma_client_server_driver_key_material_agrees_from_public_success_components
    client
    server
    client_received
    client_sent
    server_received
    server_sent

let lemma_client_server_driver_key_material_agrees_from_public_success_transport_and_semantics
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
=
  assert (client_server_driver_key_material_no_read_ahead_projection_inputs
    client
    server
    client_received
    client_sent
    server_received
    server_sent);
  lemma_client_server_driver_key_material_agrees_from_public_success_projections
    client
    server
    client_received
    client_sent
    server_received
    server_sent

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
