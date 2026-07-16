module TLS13.Impl.Driver.Pairing

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWP = TLS13.ConnectionState.ProtectedWireProjection
module R = TLS13.Record.Spec
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module ST = TLS13.Impl.Server.Types
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

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

let lemma_paired_handshake_message_states_paired_cleartext_hello_messages
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_handshake_message_states client server)
      (ensures paired_cleartext_hello_messages client server)
=
  match
    client.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
    server.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
    client.CS.cs_model.CS.model_handshake.CS.hs_server_hello,
    server.CS.cs_model.CS.model_handshake.CS.hs_server_hello,
    client.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
    server.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
    client.CS.cs_model.CS.model_handshake.CS.hs_certificate,
    server.CS.cs_model.CS.model_handshake.CS.hs_certificate,
    client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
    server.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
    client.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
    server.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
    client.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
    server.CS.cs_model.CS.model_handshake.CS.hs_client_finished
  with
  | Some client_ch, Some server_ch,
    Some client_sh, Some server_sh,
    Some _, Some _,
    Some _, Some _,
    Some _, Some _,
    Some _, Some _,
    Some _, Some _ ->
    assert (CS.handshake_msg_corresponds
      (M.ClientHello client_ch)
      (M.ClientHello server_ch));
    assert (CS.handshake_msg_corresponds
      (M.ServerHello client_sh)
      (M.ServerHello server_sh));
    assert (CS.client_hello_corresponds client_ch server_ch);
    assert (CS.server_hello_corresponds client_sh server_sh)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _ ->
    assert False

let lemma_paired_handshake_message_states_paired_handshake_events
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_handshake_events client server)
      (ensures paired_handshake_events client server)
=
  ()

let lemma_paired_handshake_event_trace_paired_handshake_message_states
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_handshake_event_trace client server)
      (ensures paired_handshake_message_states client server /\
               paired_handshake_events client server)
=
  match
    client.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
    server.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
    client.CS.cs_model.CS.model_handshake.CS.hs_server_hello,
    server.CS.cs_model.CS.model_handshake.CS.hs_server_hello,
    client.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
    server.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
    client.CS.cs_model.CS.model_handshake.CS.hs_certificate,
    server.CS.cs_model.CS.model_handshake.CS.hs_certificate,
    client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
    server.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
    client.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
    server.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
    client.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
    server.CS.cs_model.CS.model_handshake.CS.hs_client_finished
  with
  | Some client_ch, Some server_ch,
    Some client_sh, Some server_sh,
    Some client_ee, Some server_ee,
    Some client_cert, Some server_cert,
    Some client_cv, Some server_cv,
    Some client_sf, Some server_sf,
    Some client_cf, Some server_cf ->
    assert (CS.handshake_msg_corresponds
      (M.ClientHello client_ch)
      (M.ClientHello server_ch));
    assert (CS.handshake_msg_corresponds
      (M.ServerHello client_sh)
      (M.ServerHello server_sh));
    assert (CS.handshake_msg_corresponds
      (M.EncryptedExtensions client_ee)
      (M.EncryptedExtensions server_ee));
    assert (CS.handshake_msg_corresponds
      (M.Certificate client_cert)
      (M.Certificate server_cert));
    assert (CS.handshake_msg_corresponds
      (M.CertificateVerify client_cv)
      (M.CertificateVerify server_cv));
    assert (CS.handshake_msg_corresponds
      (M.Finished client_sf)
      (M.Finished server_sf));
    assert (CS.handshake_msg_corresponds
      (M.Finished client_cf)
      (M.Finished server_cf));
    assert (CS.client_hello_corresponds client_ch server_ch);
    assert (CS.server_hello_corresponds client_sh server_sh);
    assert (CS.encrypted_extensions_corresponds client_ee server_ee);
    assert (CS.certificate_msg_corresponds client_cert server_cert);
    assert (CS.certificate_verify_corresponds client_cv server_cv);
    assert (client_sf == server_sf);
    assert (client_cf == server_cf);
    assert (CS.same_transcript_checkpoint CS.TH_CH client server);
    assert (CS.same_transcript_checkpoint CS.TH_SH client server);
    assert (CS.same_transcript_checkpoint CS.TH_before_CV client server);
    assert (CS.same_transcript_checkpoint CS.TH_before_SF client server);
    assert (CS.same_transcript_checkpoint CS.TH_SF client server);
    assert (CS.same_transcript_checkpoint CS.TH_CF client server);
    assert (CS.paired_handshake_events client server)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _ ->
    assert False

let lemma_paired_handshake_event_trace_paired_handshake_events
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_handshake_event_trace client server)
      (ensures
        paired_handshake_message_states client server /\
        paired_handshake_events client server)
=
  lemma_paired_handshake_event_trace_paired_handshake_message_states
    client
    server;
  assert (CS.same_transcript_checkpoint CS.TH_CH client server);
  assert (CS.same_transcript_checkpoint CS.TH_SH client server);
  assert (CS.same_transcript_checkpoint CS.TH_before_CV client server);
  assert (CS.same_transcript_checkpoint CS.TH_before_SF client server);
  assert (CS.same_transcript_checkpoint CS.TH_SF client server);
  assert (CS.same_transcript_checkpoint CS.TH_CF client server);
  assert (CS.paired_handshake_events client server)

let lemma_paired_handshake_message_states_application_derivation_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        paired_handshake_message_states client server /\
        paired_handshake_events client server)
      (ensures
        client_server_driver_application_derivation_projection_inputs
          client
          server)
=
  match
    client.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
    server.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
    client.CS.cs_model.CS.model_handshake.CS.hs_server_hello,
    server.CS.cs_model.CS.model_handshake.CS.hs_server_hello,
    client.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
    server.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
    client.CS.cs_model.CS.model_handshake.CS.hs_certificate,
    server.CS.cs_model.CS.model_handshake.CS.hs_certificate,
    client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
    server.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
    client.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
    server.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
    client.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
    server.CS.cs_model.CS.model_handshake.CS.hs_client_finished
  with
  | Some client_ch, Some server_ch,
    Some client_sh, Some server_sh,
    Some client_ee, Some server_ee,
    Some client_cert, Some server_cert,
    Some client_cv, Some server_cv,
    Some client_sf, Some server_sf,
    Some _, Some _ ->
    lemma_paired_handshake_message_states_paired_handshake_events
      client
      server;
    assert (CS.same_transcript_checkpoint CS.TH_SF client server);
    assert (CS.same_key_derivation_checkpoint CS.DeriveApplicationTraffic client server)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _ ->
    assert False

let lemma_paired_handshake_events_application_derivation_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_handshake_events client server)
      (ensures
        client_server_driver_application_derivation_projection_inputs
          client
          server)
=
  assert (CS.paired_handshake_events client server);
  CSL.lemma_paired_handshake_events_same_key_derivation_checkpoint
    CS.DeriveApplicationTraffic
    client
    server

let lemma_client_server_driver_paired_x25519_key_shares_from_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        client_server_driver_x25519_projection_inputs client server)
      (ensures CS.paired_x25519_key_shares client server)
=
  CSL.lemma_client_application_ready_stable_x25519_key_share_projection client;
  CSL.lemma_server_application_ready_stable_x25519_key_share_projection server;
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
       assert (CS.handshake_msg_corresponds
         (M.ClientHello client_ch) (M.ClientHello server_ch));
       assert (CS.handshake_msg_corresponds
         (M.ServerHello client_sh) (M.ServerHello server_sh));
       assert (CS.client_hello_key_share client_ch ==
         CS.client_hello_key_share server_ch);
       assert (CS.server_hello_key_share client_sh ==
         CS.server_hello_key_share server_sh);
       (match
          CS.client_hello_key_share server_ch,
          CS.server_hello_key_share client_sh
        with
        | Some ch_ks, Some sh_ks ->
          assert (ch_ks == start.CS.start_client_key_share_public);
          assert (sh_ks == selection.CS.server_key_share_public);
          assert (C.x25519_public_from_private client_sk ==
            start.CS.start_client_key_share_public);
          assert (C.x25519_public_from_private server_sk ==
            selection.CS.server_key_share_public);
          assert (C.x25519_shared client_sk sh_ks == Some client_shared);
          assert (C.x25519_shared server_sk ch_ks == Some server_shared)
        | _, _ -> assert False)
     | _, _ ->
       assert False)
  | _, _, _, _, _, _, _, _ ->
    assert False

let lemma_client_server_driver_paired_x25519_key_shares_from_key_share_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
     (requires
       client_server_driver_x25519_key_share_projection_inputs client server)
     (ensures CS.paired_x25519_key_shares client server)
=
  CSL.lemma_client_application_ready_stable_x25519_key_share_projection client;
  CSL.lemma_server_application_ready_stable_x25519_key_share_projection server;
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
      assert (WFL.paired_cleartext_hello_key_shares client server);
      assert (CS.client_hello_key_share client_ch ==
        CS.client_hello_key_share server_ch);
      assert (CS.server_hello_key_share client_sh ==
        CS.server_hello_key_share server_sh);
      (match
         CS.client_hello_key_share server_ch,
         CS.server_hello_key_share client_sh
       with
       | Some ch_ks, Some sh_ks ->
         assert (ch_ks == start.CS.start_client_key_share_public);
         assert (sh_ks == selection.CS.server_key_share_public);
         assert (C.x25519_public_from_private client_sk ==
           start.CS.start_client_key_share_public);
         assert (C.x25519_public_from_private server_sk ==
           selection.CS.server_key_share_public);
         assert (C.x25519_shared client_sk sh_ks == Some client_shared);
         assert (C.x25519_shared server_sk ch_ks == Some server_shared)
       | _, _ -> assert False)
     | _, _ ->
      assert False)
  | _, _, _, _, _, _, _, _ ->
    assert False

#push-options "--z3refresh --split_queries always"
let lemma_client_server_driver_paired_key_derivation_checkpoints_from_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        client_server_driver_supported_profile_derived_projection_inputs
          client
          server)
      (ensures CS.paired_key_derivation_checkpoints client server)
=
  assert (CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server);
  assert (CS.same_key_derivation_checkpoint CS.DeriveApplicationTraffic client server)
#pop-options

let lemma_client_server_driver_paired_key_derivation_checkpoints_from_key_share_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        client_server_driver_supported_profile_derived_key_share_projection_inputs
          client
          server)
      (ensures CS.paired_key_derivation_checkpoints client server)
=
  assert (CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server);
  assert (CS.same_key_derivation_checkpoint CS.DeriveApplicationTraffic client server)

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
  lemma_client_server_driver_paired_key_derivation_checkpoints_from_projection_inputs
    client
    server

let lemma_client_server_driver_supported_profile_derived_state_inputs_from_key_share_projection_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        client_server_driver_supported_profile_derived_key_share_projection_inputs
          client
          server)
      (ensures
        client_server_driver_supported_profile_derived_state_inputs
          client
          server)
=
  lemma_client_server_driver_paired_x25519_key_shares_from_key_share_projection_inputs
    client
    server;
  lemma_client_server_driver_paired_key_derivation_checkpoints_from_key_share_projection_inputs
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

let lemma_client_server_driver_supported_profile_application_record_state_inputs_from_first_epoch_no_key_update
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
=
  assert (client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
  assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
  assert (CS.application_record_keys_installed_for_role
    CS.ClientEndpoint
    client.CS.cs_model);
  assert (CS.connection_state_raw_event_replay_consistent client);
  CSL.lemma_connection_state_no_key_update_trace_first_epoch_application_traffic_material_slots_match_expected
    client;
  assert (CS.first_epoch_application_traffic_material_no_key_update_invariant
    client);
  CSL.lemma_no_key_update_application_traffic_material_matches_expected
    CS.ClientEndpoint
    client;
  assert (server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
  assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
  assert (CS.application_record_keys_installed_for_role
    CS.ServerEndpoint
    server.CS.cs_model);
  assert (CS.connection_state_raw_event_replay_consistent server);
  CSL.lemma_connection_state_no_key_update_trace_first_epoch_application_traffic_material_slots_match_expected
    server;
  assert (CS.first_epoch_application_traffic_material_no_key_update_invariant
    server);
  CSL.lemma_no_key_update_application_traffic_material_matches_expected
    CS.ServerEndpoint
    server

let lemma_client_server_driver_remaining_semantic_projection_inputs_from_cleartext_and_application_checkpoint
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        paired_cleartext_hello_messages client server /\
        CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server /\
        client_server_driver_application_derivation_projection_inputs
          client
          server /\
        client_server_driver_supported_profile_application_record_state_inputs
          client
          server)
      (ensures
        client_server_driver_remaining_semantic_projection_inputs client server)
=
  assert (client_server_driver_x25519_projection_inputs client server);
  assert (client_server_driver_supported_profile_derived_projection_inputs
    client
    server)

let lemma_client_server_driver_remaining_semantic_projection_inputs_from_cleartext_and_handshake_events
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
=
  lemma_paired_handshake_events_application_derivation_projection_inputs
    client
    server;
  assert (CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server);
  lemma_client_server_driver_remaining_semantic_projection_inputs_from_cleartext_and_application_checkpoint
    client
    server

let lemma_client_server_driver_remaining_semantic_projection_inputs_from_paired_handshake_message_states
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        paired_handshake_message_states client server /\
        paired_handshake_events client server /\
        client_server_driver_supported_profile_application_record_state_inputs
          client
          server)
      (ensures
        client_server_driver_remaining_semantic_projection_inputs client server)
=
  lemma_paired_handshake_message_states_paired_cleartext_hello_messages
    client
    server;
  lemma_paired_handshake_message_states_application_derivation_projection_inputs
    client
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

let lemma_client_server_driver_key_material_agrees_from_public_success_minimal_projections
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
=
  lemma_client_server_driver_remaining_semantic_projection_inputs_from_cleartext_and_application_checkpoint
    client
    server;
  assert (client_server_driver_key_material_no_read_ahead_projection_inputs
    client
    server
    client_received
    client_sent
    server_received
    server_sent);
  lemma_client_server_driver_key_material_agrees_from_public_success_transport_and_semantics
    client
    server
    client_received
    client_sent
    server_received
    server_sent

let lemma_client_server_driver_key_material_agrees_from_public_success_cleartext_and_handshake_events
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
=
  lemma_client_server_driver_remaining_semantic_projection_inputs_from_cleartext_and_handshake_events
    client
    server;
  assert (client_server_driver_key_material_no_read_ahead_minimal_projection_inputs
    client
    server
    client_received
    client_sent
    server_received
    server_sent);
  assert (client_server_driver_key_material_no_read_ahead_projection_inputs
    client
    server
    client_received
    client_sent
    server_received
    server_sent);
  lemma_client_server_driver_key_material_agrees_from_public_success_minimal_projections
    client
    server
    client_received
    client_sent
    server_received
    server_sent

let lemma_client_server_driver_key_material_agrees_from_public_success_paired_handshake_messages
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
=
  lemma_client_server_driver_remaining_semantic_projection_inputs_from_paired_handshake_message_states
    client
    server;
  lemma_client_server_driver_key_material_agrees_from_public_success_transport_and_semantics
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

let lemma_client_server_application_record_material_client_to_server_agrees
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CS.supported_profile_client_server_key_material_agrees client server)
      (ensures
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server)
=
  assert (CS.supported_profile_application_record_material_agrees client server);
  assert (CS.peer_record_material_agrees
    (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
    client
    server)

let lemma_client_server_application_record_material_server_to_client_agrees
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CS.supported_profile_client_server_key_material_agrees client server)
      (ensures
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  assert (CS.supported_profile_application_record_material_agrees client server);
  assert (CS.peer_record_material_agrees
    (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
    client
    server)

(** ─────────────────────────────────────────────────────────────────────────
    STAGE 2b: handshake-epoch record-material extractors.

    Unlike the application-epoch extractors above (which are trivial because
    [supported_profile_application_record_material_agrees] is bundled inside
    [supported_profile_client_server_key_material_agrees]), there is no
    handshake counterpart predicate.  We CONSTRUCT the handshake
    [peer_record_material_agrees] from the two [peer_record_material_inputs_agree]
    ingredients:

      (1) [key_schedule_traffic_record_material_agrees] — the CROSS-endpoint
          handshake key/iv agreement (taken as a hypothesis; it is a pure
          key-schedule fact that the pairing key-schedule lemmas establish), and

      (2) [record_direction_material_matches_key_schedule_for_role] on the
          sender's write slot and the receiver's read slot — the INSTALL-STATUS
          fact, obtained from [connection_state_consistent] (per-role record-key
          consistency) plus the record slot being at the [R.Handshake] epoch.

    The two directions differ only in which slots must be at the handshake epoch:
    server→client uses server.record_write + client.record_read; the reverse uses
    client.record_write + server.record_read.  Both hold during the protected
    handshake flight (EE/Cert/CV/SF send for server→client, CF send for the
    reverse).
    ───────────────────────────────────────────────────────────────────────── *)

let lemma_client_server_handshake_record_material_server_to_client_agrees
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CS.key_schedule_traffic_record_material_agrees
          (CS.traffic_id CS.TrafficHandshake CS.ServerTraffic) client server /\
        CS.connection_state_consistent client /\
        CS.connection_state_consistent server /\
        client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        ~(CS.ControlFailed? client.CS.cs_model.CS.model_control) /\
        ~(CS.ControlFailed? server.CS.cs_model.CS.model_control) /\
        server.CS.cs_model.CS.model_record.CS.record_write.R.epoch ==
          R.Handshake /\
        client.CS.cs_model.CS.model_record.CS.record_read.R.epoch ==
          R.Handshake)
      (ensures
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficHandshake CS.ServerTraffic)
          client
          server)
=
  CSL.lemma_connection_state_consistent_record_keys_consistent_for_config_role
    client;
  CSL.lemma_connection_state_consistent_record_keys_consistent_for_config_role
    server;
  assert (CS.model_record_keys_consistent_for_role
    CS.ServerEndpoint server.CS.cs_model);
  assert (CS.model_record_keys_consistent_for_role
    CS.ClientEndpoint client.CS.cs_model);
  CSL.lemma_handshake_record_direction_material_matches_key_schedule_for_role
    CS.ServerEndpoint CS.TrafficWrite server.CS.cs_model;
  CSL.lemma_handshake_record_direction_material_matches_key_schedule_for_role
    CS.ClientEndpoint CS.TrafficRead client.CS.cs_model;
  assert (CS.peer_record_material_inputs_agree
    (CS.traffic_id CS.TrafficHandshake CS.ServerTraffic) client server);
  CSL.lemma_peer_record_material_agrees
    (CS.traffic_id CS.TrafficHandshake CS.ServerTraffic) client server

let lemma_client_server_handshake_record_material_client_to_server_agrees
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CS.key_schedule_traffic_record_material_agrees
          (CS.traffic_id CS.TrafficHandshake CS.ClientTraffic) client server /\
        CS.connection_state_consistent client /\
        CS.connection_state_consistent server /\
        client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        ~(CS.ControlFailed? client.CS.cs_model.CS.model_control) /\
        ~(CS.ControlFailed? server.CS.cs_model.CS.model_control) /\
        client.CS.cs_model.CS.model_record.CS.record_write.R.epoch ==
          R.Handshake /\
        server.CS.cs_model.CS.model_record.CS.record_read.R.epoch ==
          R.Handshake)
      (ensures
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficHandshake CS.ClientTraffic)
          client
          server)
=
  CSL.lemma_connection_state_consistent_record_keys_consistent_for_config_role
    client;
  CSL.lemma_connection_state_consistent_record_keys_consistent_for_config_role
    server;
  assert (CS.model_record_keys_consistent_for_role
    CS.ClientEndpoint client.CS.cs_model);
  assert (CS.model_record_keys_consistent_for_role
    CS.ServerEndpoint server.CS.cs_model);
  CSL.lemma_handshake_record_direction_material_matches_key_schedule_for_role
    CS.ClientEndpoint CS.TrafficWrite client.CS.cs_model;
  CSL.lemma_handshake_record_direction_material_matches_key_schedule_for_role
    CS.ServerEndpoint CS.TrafficRead server.CS.cs_model;
  assert (CS.peer_record_material_inputs_agree
    (CS.traffic_id CS.TrafficHandshake CS.ClientTraffic) client server);
  CSL.lemma_peer_record_material_agrees
    (CS.traffic_id CS.TrafficHandshake CS.ClientTraffic) client server

(** STAGE 2c-i: H_mat directly from [tls_system_inv]-available facts.  See the
    .fsti for the construction outline.  The key/iv [key_schedule_...] input to
    the STAGE 2b extractor is built from the derived-material agreement bundle
    and the two per-endpoint [matches_expected] facts via the generic bridge. *)
let lemma_handshake_peer_record_material_server_to_client_agrees_from_hello
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CS.supported_profile_all_derived_key_material_agrees client server /\
        CS.connection_state_consistent client /\
        CS.connection_state_consistent server /\
        client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        ~(CS.ControlFailed? client.CS.cs_model.CS.model_control) /\
        ~(CS.ControlFailed? server.CS.cs_model.CS.model_control) /\
        server.CS.cs_model.CS.model_record.CS.record_write.R.epoch ==
          R.Handshake /\
        client.CS.cs_model.CS.model_record.CS.record_read.R.epoch ==
          R.Handshake)
      (ensures
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficHandshake CS.ServerTraffic)
          client
          server)
=
  (* Establish the installed handshake slot (label ServerTraffic) at both
     endpoints from the record slot being at the handshake epoch. *)
  CSL.lemma_connection_state_consistent_record_keys_consistent_for_config_role
    client;
  CSL.lemma_connection_state_consistent_record_keys_consistent_for_config_role
    server;
  CSL.lemma_handshake_record_direction_material_matches_key_schedule_for_role
    CS.ServerEndpoint CS.TrafficWrite server.CS.cs_model;
  CSL.lemma_handshake_record_direction_material_matches_key_schedule_for_role
    CS.ClientEndpoint CS.TrafficRead client.CS.cs_model;
  assert (Some? (CS.traffic_material_for_label
    server.CS.cs_model.CS.model_handshake.CS.hs_keys
    CS.TrafficHandshake CS.ServerTraffic));
  assert (Some? (CS.traffic_material_for_label
    client.CS.cs_model.CS.model_handshake.CS.hs_keys
    CS.TrafficHandshake CS.ServerTraffic));
  (* Each installed handshake slot equals its schedule-expected material. *)
  CSL.lemma_connection_state_consistent_handshake_traffic_material_matches_expected
    client CS.ServerTraffic;
  CSL.lemma_connection_state_consistent_handshake_traffic_material_matches_expected
    server CS.ServerTraffic;
  (* Compose with the derived-material agreement bundle via the generic bridge. *)
  CSL.lemma_key_schedule_traffic_record_material_agrees_from_expected_material
    (CS.traffic_id CS.TrafficHandshake CS.ServerTraffic) client server;
  lemma_client_server_handshake_record_material_server_to_client_agrees
    client server

let lemma_handshake_peer_record_material_client_to_server_agrees_from_hello
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CS.supported_profile_all_derived_key_material_agrees client server /\
        CS.connection_state_consistent client /\
        CS.connection_state_consistent server /\
        client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        ~(CS.ControlFailed? client.CS.cs_model.CS.model_control) /\
        ~(CS.ControlFailed? server.CS.cs_model.CS.model_control) /\
        client.CS.cs_model.CS.model_record.CS.record_write.R.epoch ==
          R.Handshake /\
        server.CS.cs_model.CS.model_record.CS.record_read.R.epoch ==
          R.Handshake)
      (ensures
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficHandshake CS.ClientTraffic)
          client
          server)
=
  CSL.lemma_connection_state_consistent_record_keys_consistent_for_config_role
    client;
  CSL.lemma_connection_state_consistent_record_keys_consistent_for_config_role
    server;
  CSL.lemma_handshake_record_direction_material_matches_key_schedule_for_role
    CS.ClientEndpoint CS.TrafficWrite client.CS.cs_model;
  CSL.lemma_handshake_record_direction_material_matches_key_schedule_for_role
    CS.ServerEndpoint CS.TrafficRead server.CS.cs_model;
  assert (Some? (CS.traffic_material_for_label
    client.CS.cs_model.CS.model_handshake.CS.hs_keys
    CS.TrafficHandshake CS.ClientTraffic));
  assert (Some? (CS.traffic_material_for_label
    server.CS.cs_model.CS.model_handshake.CS.hs_keys
    CS.TrafficHandshake CS.ClientTraffic));
  CSL.lemma_connection_state_consistent_handshake_traffic_material_matches_expected
    client CS.ClientTraffic;
  CSL.lemma_connection_state_consistent_handshake_traffic_material_matches_expected
    server CS.ClientTraffic;
  CSL.lemma_key_schedule_traffic_record_material_agrees_from_expected_material
    (CS.traffic_id CS.TrafficHandshake CS.ClientTraffic) client server;
  lemma_client_server_handshake_record_material_client_to_server_agrees
    client server

let lemma_client_to_server_protected_message_decode_from_peer_record_material
  (epoch:CS.traffic_epoch)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (msg:M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        CS.peer_record_material_agrees
          (CS.traffic_id epoch CS.ClientTraffic)
          client
          server /\
        client.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
          server.CS.cs_model.CS.model_record.CS.record_read.R.seq /\
        CS.sent_single_protected_message_seal client.CS.cs_model msg raw /\
        (let (content_type, fragment) = W.serialize_tls_message msg in
         W.parse_tls_message content_type fragment == Some msg))
      (ensures
        CS.received_single_protected_message_decode
          server.CS.cs_model
          msg
          raw)
=
  assert (match
    CS.record_direction_material
      client.CS.cs_model.CS.model_record.CS.record_write,
    CS.record_direction_material
      server.CS.cs_model.CS.model_record.CS.record_read
  with
  | Some sender_write, Some receiver_read ->
    CS.record_key_iv_material_agrees sender_write receiver_read
  | _, _ ->
    False);
  CSL.lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer
    client.CS.cs_model
    server.CS.cs_model
    msg
    raw

let lemma_server_to_client_protected_message_decode_from_peer_record_material
  (epoch:CS.traffic_epoch)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (msg:M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        CS.peer_record_material_agrees
          (CS.traffic_id epoch CS.ServerTraffic)
          client
          server /\
        server.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
          client.CS.cs_model.CS.model_record.CS.record_read.R.seq /\
        CS.sent_single_protected_message_seal server.CS.cs_model msg raw /\
        (let (content_type, fragment) = W.serialize_tls_message msg in
         W.parse_tls_message content_type fragment == Some msg))
      (ensures
        CS.received_single_protected_message_decode
          client.CS.cs_model
          msg
          raw)
=
  assert (match
    CS.record_direction_material
      server.CS.cs_model.CS.model_record.CS.record_write,
    CS.record_direction_material
      client.CS.cs_model.CS.model_record.CS.record_read
  with
  | Some sender_write, Some receiver_read ->
    CS.record_key_iv_material_agrees sender_write receiver_read
  | _, _ ->
    False);
  CSL.lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer
    server.CS.cs_model
    client.CS.cs_model
    msg
    raw

let lemma_client_server_application_record_material_agrees_from_paired_handshake_message_states
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        paired_handshake_message_states client server /\
        paired_handshake_events client server /\
        client_server_driver_first_epoch_no_key_update_state_inputs
          client
          server)
      (ensures
        client_server_driver_remaining_semantic_projection_inputs client server /\
        client_server_driver_supported_profile_state_inputs client server /\
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  lemma_client_server_driver_supported_profile_application_record_state_inputs_from_first_epoch_no_key_update
    client
    server;
  lemma_client_server_driver_remaining_semantic_projection_inputs_from_paired_handshake_message_states
    client
    server;
  lemma_client_server_driver_supported_profile_state_inputs_from_projection_inputs
    client
    server;
  lemma_client_server_driver_supported_profile_key_material_inputs_agree
    client
    server;
  CSL.lemma_supported_profile_client_server_key_material_agrees
    client
    server;
  lemma_client_server_application_record_material_client_to_server_agrees
    client
    server;
  lemma_client_server_application_record_material_server_to_client_agrees
    client
    server

let lemma_client_server_application_record_material_agrees_from_cleartext_and_handshake_events
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        paired_cleartext_hello_messages client server /\
        paired_handshake_events client server /\
        client_server_driver_first_epoch_no_key_update_state_inputs
          client
          server)
      (ensures
        client_server_driver_remaining_semantic_projection_inputs client server /\
        client_server_driver_supported_profile_state_inputs client server /\
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  lemma_client_server_driver_supported_profile_application_record_state_inputs_from_first_epoch_no_key_update
    client
    server;
  lemma_client_server_driver_remaining_semantic_projection_inputs_from_cleartext_and_handshake_events
    client
    server;
  lemma_client_server_driver_supported_profile_state_inputs_from_projection_inputs
    client
    server;
  lemma_client_server_driver_supported_profile_key_material_inputs_agree
    client
    server;
  CSL.lemma_supported_profile_client_server_key_material_agrees
    client
    server;
  lemma_client_server_application_record_material_client_to_server_agrees
    client
    server;
  lemma_client_server_application_record_material_server_to_client_agrees
    client
    server

let lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_handshake_events
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_ch:GCH.clientHello)
  (server_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (server_sh:GSH.serverHello)
  (client_ch_raw:B.bytes)
  (server_ch_raw:B.bytes)
  (client_sh_raw:B.bytes)
  (server_sh_raw:B.bytes)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh /\
        WFL.supported_client_hello_wire_profile client_ch /\
        Seq.equal client_ch_raw server_ch_raw /\
        Seq.equal server_sh_raw client_sh_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello client_ch))
          client_ch_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          server_ch_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello server_sh))
          server_sh_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello client_sh))
          client_sh_raw /\
        paired_handshake_events client server /\
        client_server_driver_first_epoch_no_key_update_state_inputs
          client
          server)
      (ensures
        WFL.paired_cleartext_hello_wire_equivalent client server /\
        WFL.paired_cleartext_hello_key_shares client server /\
        CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server /\
        client_server_driver_supported_profile_derived_key_share_projection_inputs
          client
          server /\
        client_server_driver_supported_profile_derived_state_inputs
          client
          server /\
        client_server_driver_supported_profile_state_inputs client server /\
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  WFL.lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw
    client
    server
    client_ch
    server_ch
    client_sh
    server_sh
    client_ch_raw
    server_ch_raw
    client_sh_raw
    server_sh_raw;
  WFL.lemma_paired_cleartext_hello_key_shares_from_cleartext_raw_and_supported_server_hello_parse
    client
    server
    client_ch
    server_ch
    client_sh
    server_sh
    client_ch_raw
    server_ch_raw
    client_sh_raw
    server_sh_raw;
  lemma_paired_handshake_events_application_derivation_projection_inputs
    client
    server;
  assert (client_server_driver_supported_profile_derived_key_share_projection_inputs
    client
    server);
  lemma_client_server_driver_supported_profile_derived_state_inputs_from_key_share_projection_inputs
    client
    server;
  lemma_client_server_driver_supported_profile_application_record_state_inputs_from_first_epoch_no_key_update
    client
    server;
  assert (client_server_driver_supported_profile_state_inputs client server);
  lemma_client_server_driver_supported_profile_key_material_inputs_agree
    client
    server;
  CSL.lemma_supported_profile_client_server_key_material_agrees
    client
    server;
  lemma_client_server_application_record_material_client_to_server_agrees
    client
    server;
  lemma_client_server_application_record_material_server_to_client_agrees
    client
    server

let lemma_client_server_application_record_material_agrees_from_cleartext_raw_key_shares_and_handshake_events
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_ch:GCH.clientHello)
  (server_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (server_sh:GSH.serverHello)
  (client_ch_raw:B.bytes)
  (server_ch_raw:B.bytes)
  (client_sh_raw:B.bytes)
  (server_sh_raw:B.bytes)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh /\
        WFL.supported_client_hello_wire_profile client_ch /\
        Seq.equal client_ch_raw server_ch_raw /\
        Seq.equal server_sh_raw client_sh_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello client_ch))
          client_ch_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          server_ch_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello server_sh))
          server_sh_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello client_sh))
          client_sh_raw /\
        WFL.paired_cleartext_hello_key_shares client server /\
        paired_handshake_events client server /\
        client_server_driver_first_epoch_no_key_update_state_inputs
          client
          server)
      (ensures
        WFL.paired_cleartext_hello_wire_equivalent client server /\
        WFL.paired_cleartext_hello_key_shares client server /\
        CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server /\
        client_server_driver_supported_profile_derived_key_share_projection_inputs
          client
          server /\
        client_server_driver_supported_profile_derived_state_inputs
          client
          server /\
        client_server_driver_supported_profile_state_inputs client server /\
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  WFL.lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw
    client
    server
    client_ch
    server_ch
    client_sh
    server_sh
    client_ch_raw
    server_ch_raw
    client_sh_raw
    server_sh_raw;
  assert (WFL.paired_cleartext_hello_wire_equivalent client server);
  assert (WFL.paired_cleartext_hello_key_shares client server);
  lemma_paired_handshake_events_application_derivation_projection_inputs
    client
    server;
  assert (client_server_driver_supported_profile_derived_key_share_projection_inputs
    client
    server);
  lemma_client_server_driver_supported_profile_derived_state_inputs_from_key_share_projection_inputs
    client
    server;
  lemma_client_server_driver_supported_profile_application_record_state_inputs_from_first_epoch_no_key_update
    client
    server;
  assert (client_server_driver_supported_profile_state_inputs client server);
  lemma_client_server_driver_supported_profile_key_material_inputs_agree
    client
    server;
  CSL.lemma_supported_profile_client_server_key_material_agrees
    client
    server;
  lemma_client_server_application_record_material_client_to_server_agrees
    client
    server;
  lemma_client_server_application_record_material_server_to_client_agrees
    client
    server

let lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_protected_event_projections
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_ch:GCH.clientHello)
  (server_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (server_sh:GSH.serverHello)
  (client_ch_raw:B.bytes)
  (server_ch_raw:B.bytes)
  (client_sh_raw:B.bytes)
  (server_sh_raw:B.bytes)
  (server_ee:PWL.protected_message_replay)
  (server_cert:PWL.protected_message_replay)
  (server_cv:PWL.protected_message_replay)
  (server_finished:PWL.protected_message_replay)
  (client_finished:PWL.protected_message_replay)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh /\
        WFL.supported_client_hello_wire_profile client_ch /\
        Seq.equal client_ch_raw server_ch_raw /\
        Seq.equal server_sh_raw client_sh_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello client_ch))
          client_ch_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          server_ch_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello server_sh))
          server_sh_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello client_sh))
          client_sh_raw /\
        PWL.paired_protected_handshake_event_projection_pairs
          client
          server
          server_ee
          server_cert
          server_cv
          server_finished
          client_finished /\
        client_server_driver_first_epoch_no_key_update_state_inputs
          client
          server)
      (ensures
        WFL.paired_cleartext_hello_wire_equivalent client server /\
        WFL.paired_cleartext_hello_key_shares client server /\
        WFL.paired_protected_handshake_wire_equivalent client server /\
        paired_handshake_events client server /\
        CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server /\
        CS.same_key_derivation_checkpoint CS.DeriveApplicationTraffic client server /\
        client_server_driver_supported_profile_derived_key_share_projection_inputs
          client
          server /\
        client_server_driver_supported_profile_derived_state_inputs
          client
          server /\
        client_server_driver_supported_profile_state_inputs client server /\
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  PWP.lemma_paired_protected_handshake_wire_equivalent_from_event_projection_pairs
    client
    server
    server_ee
    server_cert
    server_cv
    server_finished
    client_finished;
  WFL.lemma_paired_handshake_events_from_cleartext_raw_and_protected_wire
    client
    server
    client_ch
    server_ch
    client_sh
    server_sh
    client_ch_raw
    server_ch_raw
    client_sh_raw
    server_sh_raw;
  lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_handshake_events
    client
    server
    client_ch
    server_ch
    client_sh
    server_sh
    client_ch_raw
    server_ch_raw
    client_sh_raw
    server_sh_raw

let lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_protected_event_projection_witnesses
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_ch:GCH.clientHello)
  (server_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (server_sh:GSH.serverHello)
  (client_ch_raw:B.bytes)
  (server_ch_raw:B.bytes)
  (client_sh_raw:B.bytes)
  (server_sh_raw:B.bytes)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh /\
        WFL.supported_client_hello_wire_profile client_ch /\
        Seq.equal client_ch_raw server_ch_raw /\
        Seq.equal server_sh_raw client_sh_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello client_ch))
          client_ch_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          server_ch_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello server_sh))
          server_sh_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello client_sh))
          client_sh_raw /\
        paired_protected_handshake_event_projection_pair_witnesses
          client
          server /\
        client_server_driver_first_epoch_no_key_update_state_inputs
          client
          server)
      (ensures
        WFL.paired_cleartext_hello_wire_equivalent client server /\
        WFL.paired_cleartext_hello_key_shares client server /\
        WFL.paired_protected_handshake_wire_equivalent client server /\
        paired_handshake_events client server /\
        CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server /\
        CS.same_key_derivation_checkpoint CS.DeriveApplicationTraffic client server /\
        client_server_driver_supported_profile_derived_key_share_projection_inputs
          client
          server /\
        client_server_driver_supported_profile_derived_state_inputs
          client
          server /\
        client_server_driver_supported_profile_state_inputs client server /\
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  eliminate exists
    (server_ee:PWL.protected_message_replay)
    (server_cert:PWL.protected_message_replay)
    (server_cv:PWL.protected_message_replay)
    (server_finished:PWL.protected_message_replay)
    (client_finished:PWL.protected_message_replay).
    PWL.paired_protected_handshake_event_projection_pairs
      client
      server
      server_ee
      server_cert
      server_cv
      server_finished
      client_finished
  returns
    WFL.paired_cleartext_hello_wire_equivalent client server /\
    WFL.paired_cleartext_hello_key_shares client server /\
    WFL.paired_protected_handshake_wire_equivalent client server /\
    paired_handshake_events client server /\
    CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server /\
    CS.same_key_derivation_checkpoint CS.DeriveApplicationTraffic client server /\
    client_server_driver_supported_profile_derived_key_share_projection_inputs
      client
      server /\
    client_server_driver_supported_profile_derived_state_inputs
      client
      server /\
    client_server_driver_supported_profile_state_inputs client server /\
    CS.supported_profile_client_server_key_material_inputs_agree
      client
      server /\
    CS.supported_profile_client_server_key_material_agrees client server /\
    CS.peer_record_material_agrees
      (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
      client
      server /\
    CS.peer_record_material_agrees
      (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
      client
      server
  with _.
  ( lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_protected_event_projections
      client
      server
      client_ch
      server_ch
      client_sh
      server_sh
      client_ch_raw
      server_ch_raw
      client_sh_raw
      server_sh_raw
      server_ee
      server_cert
      server_cv
      server_finished
      client_finished )

let lemma_client_server_application_record_material_agrees_from_cleartext_raw_key_shares_and_protected_event_projection_witnesses
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_ch:GCH.clientHello)
  (server_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (server_sh:GSH.serverHello)
  (client_ch_raw:B.bytes)
  (server_ch_raw:B.bytes)
  (client_sh_raw:B.bytes)
  (server_sh_raw:B.bytes)
  : Lemma
      (requires
       CD.client_driver_application_ready client /\
       SD.server_driver_application_ready server /\
       client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
       server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
       client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
       server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh /\
       WFL.supported_client_hello_wire_profile client_ch /\
       Seq.equal client_ch_raw server_ch_raw /\
       Seq.equal server_sh_raw client_sh_raw /\
       CS.cleartext_tls_message_raw
         (M.TlsHandshake (M.ClientHello client_ch))
         client_ch_raw /\
       CS.received_cleartext_tls_message_raw
         (M.TlsHandshake (M.ClientHello server_ch))
         server_ch_raw /\
       CS.cleartext_tls_message_raw
         (M.TlsHandshake (M.ServerHello server_sh))
         server_sh_raw /\
       CS.received_cleartext_tls_message_raw
         (M.TlsHandshake (M.ServerHello client_sh))
         client_sh_raw /\
       WFL.paired_cleartext_hello_key_shares client server /\
       paired_protected_handshake_event_projection_pair_witnesses
         client
         server /\
       client_server_driver_first_epoch_no_key_update_state_inputs
         client
         server)
      (ensures
       WFL.paired_cleartext_hello_wire_equivalent client server /\
       WFL.paired_cleartext_hello_key_shares client server /\
       WFL.paired_protected_handshake_wire_equivalent client server /\
       paired_handshake_events client server /\
       CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server /\
       CS.same_key_derivation_checkpoint CS.DeriveApplicationTraffic client server /\
       client_server_driver_supported_profile_derived_key_share_projection_inputs
         client
         server /\
       client_server_driver_supported_profile_derived_state_inputs
         client
         server /\
       client_server_driver_supported_profile_state_inputs client server /\
       CS.supported_profile_client_server_key_material_inputs_agree
         client
         server /\
       CS.supported_profile_client_server_key_material_agrees client server /\
       CS.peer_record_material_agrees
         (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
         client
         server /\
       CS.peer_record_material_agrees
         (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
         client
         server)
=
  eliminate exists
    (server_ee:PWL.protected_message_replay)
    (server_cert:PWL.protected_message_replay)
    (server_cv:PWL.protected_message_replay)
    (server_finished:PWL.protected_message_replay)
    (client_finished:PWL.protected_message_replay).
    PWL.paired_protected_handshake_event_projection_pairs
      client
      server
      server_ee
      server_cert
      server_cv
      server_finished
      client_finished
  returns
    WFL.paired_cleartext_hello_wire_equivalent client server /\
    WFL.paired_cleartext_hello_key_shares client server /\
    WFL.paired_protected_handshake_wire_equivalent client server /\
    paired_handshake_events client server /\
    CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server /\
    CS.same_key_derivation_checkpoint CS.DeriveApplicationTraffic client server /\
    client_server_driver_supported_profile_derived_key_share_projection_inputs
      client
      server /\
    client_server_driver_supported_profile_derived_state_inputs
      client
      server /\
    client_server_driver_supported_profile_state_inputs client server /\
    CS.supported_profile_client_server_key_material_inputs_agree
      client
      server /\
    CS.supported_profile_client_server_key_material_agrees client server /\
    CS.peer_record_material_agrees
      (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
      client
      server /\
    CS.peer_record_material_agrees
      (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
      client
      server
  with _.
  (
    PWP.lemma_paired_protected_handshake_wire_equivalent_from_event_projection_pairs
      client
      server
      server_ee
      server_cert
      server_cv
      server_finished
      client_finished;
    WFL.lemma_paired_handshake_events_from_cleartext_raw_and_protected_wire
      client
      server
      client_ch
      server_ch
      client_sh
      server_sh
      client_ch_raw
      server_ch_raw
      client_sh_raw
      server_sh_raw;
    lemma_client_server_application_record_material_agrees_from_cleartext_raw_key_shares_and_handshake_events
      client
      server
      client_ch
      server_ch
      client_sh
      server_sh
      client_ch_raw
      server_ch_raw
      client_sh_raw
      server_sh_raw
  )

let lemma_client_server_application_record_material_agrees_from_paired_handshake_event_trace
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        paired_handshake_event_trace client server /\
        client_server_driver_first_epoch_no_key_update_state_inputs
          client
          server)
      (ensures
        paired_handshake_message_states client server /\
        paired_handshake_events client server /\
        client_server_driver_remaining_semantic_projection_inputs client server /\
        client_server_driver_supported_profile_state_inputs client server /\
        CS.supported_profile_client_server_key_material_inputs_agree
          client
          server /\
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  lemma_paired_handshake_event_trace_paired_handshake_events
    client
    server;
  lemma_client_server_application_record_material_agrees_from_paired_handshake_message_states
    client
    server

let lemma_client_server_driver_end_to_end_key_material_agrees
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
=
  lemma_client_server_driver_key_material_agrees_from_public_success_components
    client
    server
    client_received
    client_sent
    server_received
    server_sent
