module TLS13.ConnectionState.Lemmas

(**
  Proof support for TLS13.Spec.ConnectionState.

  The core module is the audit surface. This module contains preservation,
  projection, segmentation, and replay lemmas used by the implementation proofs.
**)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module H = TLS13.Handshake.Spec
module ID = FStar.IndefiniteDescription
module K = TLS13.Keys
module M = TLS13.Messages
module R = TLS13.Record.Spec
module RTC = FStar.ReflexiveTransitiveClosure
module S = TLS13.StateMachine
module Seq = FStar.Seq
module T = TLS13.Types
module Tr = TLS13.Transcript
module W = TLS13.Wire.Spec
module X = TLS13.X509.Spec

open FStar.List.Tot
open TLS13.Spec.ConnectionState

let lemma_endpoint_direction_traffic_labels
  ()
  : Lemma
      (ensures
        traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic /\
        traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic /\
        traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic /\
        traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic)
=
  ()

let lemma_legal_connection_delta_local_fail_control_failed
  (st0:connection_state)
  (st1:connection_state)
  (err:T.tls_error)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires
        legal_connection_delta
          st0
          {
            delta_event = ConnLocalEvent (LocalFail err);
            delta_raw_sent = raw_sent;
            delta_raw_received = raw_received;
          }
          st1)
      (ensures st1.cs_model.model_control == ControlFailed err)
=
  assert (step_model st0.cs_model (ConnLocalEvent (LocalFail err)) ==
    Some st1.cs_model);
  assert (step_local_event st0.cs_model (LocalFail err) ==
    Some (fail_model st0.cs_model err));
  assert (st1.cs_model == fail_model st0.cs_model err)

let lemma_expected_traffic_secret_client_projection
  (hs:handshake_state)
  (epoch:traffic_epoch)
  (dir:traffic_direction)
  : Lemma
      (ensures
        expected_traffic_secret hs epoch dir ==
        expected_traffic_secret_for_role ClientEndpoint hs epoch dir)
=
  ()

let lemma_update_key_schedule_with_install_client_projection
  (keys:key_schedule_state)
  (install:traffic_key_install)
  : Lemma
      (ensures
        update_key_schedule_with_install keys install ==
        update_key_schedule_with_install_for_role ClientEndpoint keys install)
=
  ()

let lemma_record_read_key_schedule_projection_client_projection
  (model:connection_model)
  : Lemma
      (ensures
        record_read_key_schedule_projection model ==
        record_read_key_schedule_projection_for_role ClientEndpoint model)
=
  ()

let lemma_record_write_key_schedule_projection_client_projection
  (model:connection_model)
  : Lemma
      (ensures
        record_write_key_schedule_projection model ==
        record_write_key_schedule_projection_for_role ClientEndpoint model)
=
  ()

let lemma_expected_traffic_secret_for_state_agrees
  (traffic_id:labeled_traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires traffic_secret_inputs_agree traffic_id client server)
      (ensures
        (match
          expected_traffic_secret_for_state traffic_id client,
          expected_traffic_secret_for_state traffic_id server
        with
        | Some client_secret, Some server_secret -> Seq.equal client_secret server_secret
        | _, _ -> False))
=
  let base_id =
    match traffic_id.traffic_id_epoch with
    | TrafficHandshake -> HandshakeSecret
    | TrafficApplication -> MasterSecret in
  let checkpoint = key_checkpoint_for_epoch traffic_id.traffic_id_epoch in
  match
    base_secret_material base_id client.cs_model.model_handshake.hs_keys,
    base_secret_material base_id server.cs_model.model_handshake.hs_keys,
    transcript_bytes_for_key_checkpoint checkpoint client,
    transcript_bytes_for_key_checkpoint checkpoint server
  with
  | Some client_base, Some server_base, Some client_transcript, Some server_transcript ->
    assert (Seq.equal client_base server_base);
    assert (Seq.equal client_transcript server_transcript);
    Seq.lemma_eq_elim client_base server_base;
    Seq.lemma_eq_elim client_transcript server_transcript;
    assert (expected_traffic_secret_for_state traffic_id client ==
            expected_traffic_secret_for_state traffic_id server)
  | _, _, _, _ ->
    assert False

let lemma_paired_endpoints_derived_key_agrees
  (key_id:derived_key_id)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        first_milestone_derived_key_id key_id /\
        derivation_inputs_agree key_id client server)
      (ensures peer_derived_key_material_agrees key_id client server)
=
  match key_id with
  | BaseSecret base_id ->
    (match
      base_secret_material base_id client.cs_model.model_handshake.hs_keys,
      base_secret_material base_id server.cs_model.model_handshake.hs_keys
     with
     | Some client_secret, Some server_secret ->
       assert (Seq.equal client_secret server_secret)
     | _, _ -> assert False)
  | TrafficSecret traffic_id ->
    lemma_expected_traffic_secret_for_state_agrees traffic_id client server
  | TrafficKey traffic_id ->
    lemma_expected_traffic_secret_for_state_agrees traffic_id client server;
    (match
      expected_traffic_secret_for_state traffic_id client,
      expected_traffic_secret_for_state traffic_id server
     with
     | Some client_secret, Some server_secret ->
       assert (Seq.equal client_secret server_secret);
       Seq.lemma_eq_elim client_secret server_secret
     | _, _ -> assert False)
  | TrafficIV traffic_id ->
    lemma_expected_traffic_secret_for_state_agrees traffic_id client server;
    (match
      expected_traffic_secret_for_state traffic_id client,
      expected_traffic_secret_for_state traffic_id server
     with
     | Some client_secret, Some server_secret ->
       assert (Seq.equal client_secret server_secret);
       Seq.lemma_eq_elim client_secret server_secret
     | _, _ -> assert False)
  | FinishedKey label ->
    let traffic_id = { traffic_id_epoch = TrafficHandshake; traffic_id_label = label } in
    lemma_expected_traffic_secret_for_state_agrees traffic_id client server;
    (match
      expected_traffic_secret_for_state traffic_id client,
      expected_traffic_secret_for_state traffic_id server
     with
     | Some client_secret, Some server_secret ->
       assert (Seq.equal client_secret server_secret);
       Seq.lemma_eq_elim client_secret server_secret
     | _, _ -> assert False)
  | TrafficUpdateSecret _
  | ExporterMasterSecret
  | ResumptionMasterSecret ->
    assert False

let lemma_paired_x25519_key_shares_shared_secret_agree
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires paired_x25519_key_shares client server)
      (ensures shared_secret_material_agrees client server)
=
  let client_hs = client.cs_model.model_handshake in
  let server_hs = server.cs_model.model_handshake in
  match
    client_hs.hs_start,
    client_hs.hs_server_hello,
    server_hs.hs_server_selection,
    server_hs.hs_client_hello
  with
  | Some start, Some (sh:M.server_hello), Some selection, Some (ch:M.client_hello) ->
    (match
      start.start_client_key_share_private,
      selection.server_key_share_private,
      client_hs.hs_keys.ks_shared_secret,
      server_hs.hs_keys.ks_shared_secret
     with
     | Some client_sk, Some server_sk, Some client_shared, Some server_shared ->
       C.lemma_x25519_shared_agreement
         client_sk
         server_sk
         start.start_client_key_share_public
         selection.server_key_share_public;
       assert (client_hello_key_share ch == start.start_client_key_share_public);
       assert (server_hello_key_share sh == selection.server_key_share_public);
       assert (C.x25519_shared client_sk (server_hello_key_share sh) == Some client_shared);
       assert (C.x25519_shared server_sk (client_hello_key_share ch) == Some server_shared);
       assert (C.x25519_shared client_sk (server_hello_key_share sh) ==
               C.x25519_shared server_sk (client_hello_key_share ch));
       assert (Some client_shared == Some server_shared);
       assert (client_shared == server_shared);
       Seq.lemma_eq_intro client_shared server_shared
     | _, _, _, _ -> assert False)
  | _, _, _, _ -> assert False

let lemma_shared_secret_lineage_base_secret_agree
  (base_id:base_secret_id)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        shared_secret_material_agrees client server /\
        connection_supported_profile_key_schedule_lineage client /\
        connection_supported_profile_key_schedule_lineage server)
      (ensures base_secret_inputs_agree base_id client server)
=
  let client_keys = client.cs_model.model_handshake.hs_keys in
  let server_keys = server.cs_model.model_handshake.hs_keys in
  match
    client_keys.ks_shared_secret,
    server_keys.ks_shared_secret,
    client_keys.ks_early_secret,
    server_keys.ks_early_secret,
    client_keys.ks_handshake_secret,
    server_keys.ks_handshake_secret,
    client_keys.ks_master_secret,
    server_keys.ks_master_secret
  with
  | Some client_shared, Some server_shared,
    Some client_early, Some server_early,
    Some client_handshake, Some server_handshake,
    Some client_master, Some server_master ->
    assert (Seq.equal client_shared server_shared);
    assert (Seq.equal client_early (K.early_secret B.empty));
    assert (Seq.equal server_early (K.early_secret B.empty));
    Seq.lemma_eq_elim client_shared server_shared;
    Seq.lemma_eq_elim client_early (K.early_secret B.empty);
    Seq.lemma_eq_elim server_early (K.early_secret B.empty);
    assert (Seq.equal client_early server_early);
    assert (Seq.equal client_handshake (K.handshake_secret client_early client_shared));
    assert (Seq.equal server_handshake (K.handshake_secret server_early server_shared));
    Seq.lemma_eq_elim client_handshake (K.handshake_secret client_early client_shared);
    Seq.lemma_eq_elim server_handshake (K.handshake_secret server_early server_shared);
    assert (Seq.equal client_handshake server_handshake);
    assert (Seq.equal client_master (K.master_secret client_handshake));
    assert (Seq.equal server_master (K.master_secret server_handshake));
    Seq.lemma_eq_elim client_handshake server_handshake;
    Seq.lemma_eq_elim client_master (K.master_secret client_handshake);
    Seq.lemma_eq_elim server_master (K.master_secret server_handshake);
    assert (Seq.equal client_master server_master);
    (match base_id with
     | EarlySecret -> assert (Seq.equal client_early server_early)
     | HandshakeSecret -> assert (Seq.equal client_handshake server_handshake)
     | MasterSecret -> assert (Seq.equal client_master server_master))
  | _, _, _, _, _, _, _, _ ->
    assert False

let lemma_paired_x25519_key_shares_base_secret_agree
  (base_id:base_secret_id)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        paired_x25519_key_shares client server /\
        connection_supported_profile_key_schedule_lineage client /\
        connection_supported_profile_key_schedule_lineage server)
      (ensures base_secret_inputs_agree base_id client server)
=
  lemma_paired_x25519_key_shares_shared_secret_agree client server;
  lemma_shared_secret_lineage_base_secret_agree base_id client server

let lemma_paired_x25519_key_shares_derived_key_agrees
  (key_id:derived_key_id)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        first_milestone_derived_key_id key_id /\
        paired_x25519_key_shares client server /\
        connection_supported_profile_key_schedule_lineage client /\
        connection_supported_profile_key_schedule_lineage server /\
        derivation_checkpoint_inputs_agree key_id client server)
      (ensures peer_derived_key_material_agrees key_id client server)
=
  (match key_id with
   | BaseSecret base_id ->
     lemma_paired_x25519_key_shares_base_secret_agree base_id client server;
     assert (derivation_inputs_agree key_id client server)
   | TrafficSecret traffic_id
   | TrafficKey traffic_id
   | TrafficIV traffic_id ->
     let base_id =
       match traffic_id.traffic_id_epoch with
       | TrafficHandshake -> HandshakeSecret
       | TrafficApplication -> MasterSecret in
     lemma_paired_x25519_key_shares_base_secret_agree base_id client server;
     assert (traffic_secret_inputs_agree traffic_id client server);
     assert (derivation_inputs_agree key_id client server)
   | FinishedKey label ->
     lemma_paired_x25519_key_shares_base_secret_agree HandshakeSecret client server;
     assert (traffic_secret_inputs_agree
       { traffic_id_epoch = TrafficHandshake; traffic_id_label = label }
       client
       server);
     assert (derivation_inputs_agree key_id client server)
   | TrafficUpdateSecret _
   | ExporterMasterSecret
   | ResumptionMasterSecret ->
     assert False);
  lemma_paired_endpoints_derived_key_agrees key_id client server

let lemma_paired_handshake_events_same_transcript_checkpoint
  (checkpoint:transcript_checkpoint)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires paired_handshake_events client server)
      (ensures same_transcript_checkpoint checkpoint client server)
=
  match checkpoint with
  | TH_CH -> ()
  | TH_SH -> ()
  | TH_before_CV -> ()
  | TH_before_SF -> ()
  | TH_SF -> ()
  | TH_CF -> ()

let lemma_paired_handshake_events_same_key_derivation_checkpoint
  (checkpoint:key_derivation_checkpoint)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        paired_handshake_events client server /\
        (checkpoint == DeriveHandshakeTraffic \/
         checkpoint == DeriveApplicationTraffic))
      (ensures same_key_derivation_checkpoint checkpoint client server)
=
  match checkpoint with
  | DeriveHandshakeTraffic ->
    lemma_paired_handshake_events_same_transcript_checkpoint TH_SH client server
  | DeriveApplicationTraffic ->
    lemma_paired_handshake_events_same_transcript_checkpoint TH_SF client server
  | DeriveTrafficUpdate _ ->
    assert False

let lemma_paired_supported_profile_all_derived_key_material_agrees
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        paired_x25519_key_shares client server /\
        connection_supported_profile_key_schedule_lineage client /\
        connection_supported_profile_key_schedule_lineage server /\
        paired_handshake_events client server)
      (ensures
        supported_profile_all_derived_key_material_agrees client server)
=
  lemma_paired_handshake_events_same_key_derivation_checkpoint
    DeriveHandshakeTraffic client server;
  lemma_paired_handshake_events_same_key_derivation_checkpoint
    DeriveApplicationTraffic client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (BaseSecret EarlySecret) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (BaseSecret HandshakeSecret) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (BaseSecret MasterSecret) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficSecret (traffic_id TrafficHandshake ClientTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficSecret (traffic_id TrafficHandshake ServerTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficSecret (traffic_id TrafficApplication ClientTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficSecret (traffic_id TrafficApplication ServerTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficKey (traffic_id TrafficHandshake ClientTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficKey (traffic_id TrafficHandshake ServerTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficKey (traffic_id TrafficApplication ClientTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficKey (traffic_id TrafficApplication ServerTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficIV (traffic_id TrafficHandshake ClientTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficIV (traffic_id TrafficHandshake ServerTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficIV (traffic_id TrafficApplication ClientTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficIV (traffic_id TrafficApplication ServerTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (FinishedKey ClientTraffic) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (FinishedKey ServerTraffic) client server

let lemma_peer_record_material_agrees
  (traffic_id:labeled_traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires peer_record_material_inputs_agree traffic_id client server)
      (ensures peer_record_material_agrees traffic_id client server)
=
  match traffic_id.traffic_id_label with
  | ClientTraffic ->
    let client_st = client.cs_model.model_record.record_write in
    let server_st = server.cs_model.model_record.record_read in
    (match
      traffic_material_for_label
        client.cs_model.model_handshake.hs_keys
        traffic_id.traffic_id_epoch
        ClientTraffic,
      traffic_material_for_label
        server.cs_model.model_handshake.hs_keys
        traffic_id.traffic_id_epoch
        ClientTraffic,
      record_direction_material client_st,
      record_direction_material server_st
     with
     | Some client_material, Some server_material,
       Some client_record, Some server_record ->
       assert (record_key_iv_material_agrees
         (record_material_of_traffic_material client_material)
         (record_material_of_traffic_material server_material));
       assert (record_key_iv_material_agrees
         (record_material_of_traffic_material client_material)
         client_record);
       assert (record_key_iv_material_agrees
         (record_material_of_traffic_material server_material)
         server_record);
       assert (Seq.equal client_material.traffic_key server_material.traffic_key);
       assert (Seq.equal client_material.traffic_iv server_material.traffic_iv);
       assert (Seq.equal client_material.traffic_key client_record.record_material_key);
       assert (Seq.equal client_material.traffic_iv client_record.record_material_iv);
       assert (Seq.equal server_material.traffic_key server_record.record_material_key);
       assert (Seq.equal server_material.traffic_iv server_record.record_material_iv);
       Seq.lemma_eq_elim client_material.traffic_key client_record.record_material_key;
       Seq.lemma_eq_elim client_material.traffic_iv client_record.record_material_iv;
       Seq.lemma_eq_elim client_material.traffic_key server_material.traffic_key;
       Seq.lemma_eq_elim client_material.traffic_iv server_material.traffic_iv;
       Seq.lemma_eq_elim server_material.traffic_key server_record.record_material_key;
       Seq.lemma_eq_elim server_material.traffic_iv server_record.record_material_iv;
       assert (Seq.equal client_record.record_material_key server_record.record_material_key);
       assert (Seq.equal client_record.record_material_iv server_record.record_material_iv)
     | _, _, _, _ ->
       assert False)
  | ServerTraffic ->
    let server_st = server.cs_model.model_record.record_write in
    let client_st = client.cs_model.model_record.record_read in
    (match
      traffic_material_for_label
        client.cs_model.model_handshake.hs_keys
        traffic_id.traffic_id_epoch
        ServerTraffic,
      traffic_material_for_label
        server.cs_model.model_handshake.hs_keys
        traffic_id.traffic_id_epoch
        ServerTraffic,
      record_direction_material client_st,
      record_direction_material server_st
     with
     | Some client_material, Some server_material,
       Some client_record, Some server_record ->
       assert (record_key_iv_material_agrees
         (record_material_of_traffic_material client_material)
         (record_material_of_traffic_material server_material));
       assert (record_key_iv_material_agrees
         (record_material_of_traffic_material client_material)
         client_record);
       assert (record_key_iv_material_agrees
         (record_material_of_traffic_material server_material)
         server_record);
       assert (Seq.equal client_material.traffic_key server_material.traffic_key);
       assert (Seq.equal client_material.traffic_iv server_material.traffic_iv);
       assert (Seq.equal client_material.traffic_key client_record.record_material_key);
       assert (Seq.equal client_material.traffic_iv client_record.record_material_iv);
       assert (Seq.equal server_material.traffic_key server_record.record_material_key);
       assert (Seq.equal server_material.traffic_iv server_record.record_material_iv);
       Seq.lemma_eq_elim client_material.traffic_key client_record.record_material_key;
       Seq.lemma_eq_elim client_material.traffic_iv client_record.record_material_iv;
       Seq.lemma_eq_elim client_material.traffic_key server_material.traffic_key;
       Seq.lemma_eq_elim client_material.traffic_iv server_material.traffic_iv;
       Seq.lemma_eq_elim server_material.traffic_key server_record.record_material_key;
       Seq.lemma_eq_elim server_material.traffic_iv server_record.record_material_iv;
       assert (Seq.equal server_record.record_material_key client_record.record_material_key);
       assert (Seq.equal server_record.record_material_iv client_record.record_material_iv)
     | _, _, _, _ ->
       assert False)

let lemma_paired_supported_profile_all_record_material_agrees
  (client:connection_state)
  (server:connection_state)
  : Lemma
     (requires
       supported_profile_all_record_material_inputs_agree client server)
     (ensures
       supported_profile_all_record_material_agrees client server)
=
  lemma_peer_record_material_agrees
    (traffic_id TrafficHandshake ClientTraffic) client server;
  lemma_peer_record_material_agrees
    (traffic_id TrafficHandshake ServerTraffic) client server;
  lemma_peer_record_material_agrees
    (traffic_id TrafficApplication ClientTraffic) client server;
  lemma_peer_record_material_agrees
    (traffic_id TrafficApplication ServerTraffic) client server

let lemma_supported_profile_client_server_key_material_agrees
  (client:connection_state)
  (server:connection_state)
  : Lemma
     (requires
       supported_profile_client_server_key_material_inputs_agree client server)
     (ensures
       supported_profile_client_server_key_material_agrees client server)
=
  lemma_paired_supported_profile_all_derived_key_material_agrees client server;
  lemma_paired_supported_profile_all_record_material_agrees client server

let lemma_step_role_install_record_keys_consistent_for_role
  (role:endpoint_role)
  (model0:connection_model)
  (install:traffic_key_install)
  (model1:connection_model)
  : Lemma
      (requires
        model_record_keys_consistent_for_role role model0 /\
        traffic_install_allowed_at_stage_for_role
          role
          (match model0.model_control with
           | ControlHandshaking stage -> stage
           | _ -> HsNotStarted)
          install /\
        traffic_install_matches_key_schedule_for_role
          role
          model0.model_handshake
          install /\
        step_local_event
          model0
          (LocalInstallTrafficKeysForRole
            { install_role = role; install_payload = install }) == Some model1)
      (ensures model_record_keys_consistent_for_role role model1)
=
  ()

let lemma_initial_record_keys_consistent_for_role
  (role:endpoint_role)
  (cfg:connection_config)
  : Lemma (connection_state_record_keys_consistent_for_role role (initial cfg))
=
  ()

let lemma_initial_layered_log_consistent_for_role
  (role:endpoint_role)
  (cfg:connection_config)
  : Lemma (connection_state_layered_log_consistent_for_role role (initial cfg))
=
  ()

let lemma_model_record_keys_consistent_record_read_key_schedule_projection
  (model:connection_model)
  : Lemma
      (requires model_record_keys_consistent model)
      (ensures record_read_key_schedule_projection model)
=
  match model.model_control with
  | ControlFailed _ -> ()
  | _ ->
    let keys = model.model_handshake.hs_keys in
    let st = model.model_record.record_read in
    assert (record_read_keys_match_key_schedule keys st);
    (match st.R.epoch with
     | R.Initial -> ()
     | R.Handshake ->
       assert (traffic_material_option_matches_record_direction
         keys.ks_server_handshake_traffic
         st);
       (match keys.ks_server_handshake_traffic with
        | Some material ->
          assert (traffic_material_matches_record_direction material st);
          assert (exists material'.
            keys.ks_server_handshake_traffic == Some material' /\
            traffic_material_matches_record_direction material' st)
        | None -> assert False)
     | R.Application ->
       assert (traffic_material_option_matches_record_direction
         keys.ks_server_application_traffic
         st);
       (match keys.ks_server_application_traffic with
        | Some material ->
          assert (traffic_material_matches_record_direction material st);
          assert (exists material'.
            keys.ks_server_application_traffic == Some material' /\
            traffic_material_matches_record_direction material' st)
        | None -> assert False))

let lemma_model_record_keys_consistent_record_write_key_schedule_projection
  (model:connection_model)
  : Lemma
      (requires model_record_keys_consistent model)
      (ensures record_write_key_schedule_projection model)
=
  match model.model_control with
  | ControlFailed _ -> ()
  | _ ->
    let keys = model.model_handshake.hs_keys in
    let st = model.model_record.record_write in
    assert (record_write_keys_match_key_schedule model.model_control keys st);
    (match st.R.epoch with
     | R.Initial -> ()
     | R.Handshake ->
       assert (traffic_material_option_matches_record_direction
         keys.ks_client_handshake_traffic
         st);
       (match keys.ks_client_handshake_traffic with
        | Some material ->
          assert (traffic_material_matches_record_direction material st);
          assert (exists material'.
            keys.ks_client_handshake_traffic == Some material' /\
            traffic_material_matches_record_direction material' st)
        | None -> assert False)
     | R.Application ->
       (match model.model_control with
        | ControlHandshaking _ -> ()
        | _ ->
          assert (traffic_material_option_matches_record_direction
            keys.ks_client_application_traffic
            st);
          (match keys.ks_client_application_traffic with
           | Some material ->
             assert (traffic_material_matches_record_direction material st);
             assert (exists material'.
               keys.ks_client_application_traffic == Some material' /\
               traffic_material_matches_record_direction material' st)
           | None -> assert False)))

let lemma_record_read_keys_next_seq
  (keys:key_schedule_state)
  (st:R.direction_state)
  : Lemma
      (requires record_read_keys_match_key_schedule keys st)
      (ensures record_read_keys_match_key_schedule keys (R.next_seq st))
=
  ()

let lemma_record_write_keys_next_seq
  (control:connection_control_state)
  (keys:key_schedule_state)
  (st:R.direction_state)
  : Lemma
      (requires record_write_keys_match_key_schedule control keys st)
      (ensures record_write_keys_match_key_schedule control keys (R.next_seq st))
=
  ()

let lemma_record_keys_next_seq_for_role
  (role:endpoint_role)
  (dir:traffic_direction)
  (control:connection_control_state)
  (keys:key_schedule_state)
  (st:R.direction_state)
  : Lemma
      (requires record_keys_match_key_schedule_for_role role dir control keys st)
      (ensures record_keys_match_key_schedule_for_role role dir control keys (R.next_seq st))
=
  ()

let rec lemma_record_write_keys_advance
  (control:connection_control_state)
  (keys:key_schedule_state)
  (st:R.direction_state)
  (n:nat)
  : Lemma
      (requires record_write_keys_match_key_schedule control keys st)
      (ensures
        record_write_keys_match_key_schedule
          control
          keys
          (advance_direction_records st n))
      (decreases n)
=
  if n = 0 then ()
  else lemma_record_write_keys_advance control keys st (n - 1)

let rec lemma_record_keys_advance_for_role
  (role:endpoint_role)
  (dir:traffic_direction)
  (control:connection_control_state)
  (keys:key_schedule_state)
  (st:R.direction_state)
  (n:nat)
  : Lemma
      (requires record_keys_match_key_schedule_for_role role dir control keys st)
      (ensures
        record_keys_match_key_schedule_for_role
          role
          dir
          control
          keys
          (advance_direction_records st n))
      (decreases n)
=
  if n = 0 then ()
  else lemma_record_keys_advance_for_role role dir control keys st (n - 1)

let lemma_initial_app_log_consistent
  (cfg:connection_config)
  : Lemma (connection_state_app_log_consistent (initial cfg))
=
  ()

let lemma_initial_pending_application_consistent
  (cfg:connection_config)
  : Lemma (connection_state_pending_application_consistent (initial cfg))
=
  ()

let lemma_initial_transcript_consistent
  (cfg:connection_config)
  : Lemma (connection_state_transcript_consistent (initial cfg))
=
  ()

let lemma_initial_event_log_consistent
  (cfg:connection_config)
  : Lemma
      (connection_state_event_log_consistent_with cfg (initial cfg) /\
       connection_state_event_log_consistent (initial cfg))
=
  ()

let lemma_initial_key_update_pending_consistent
  (cfg:connection_config)
  : Lemma (connection_state_key_update_pending_consistent (initial cfg))
=
  ()

let lemma_initial_record_layer_consistent
  (cfg:connection_config)
  : Lemma (connection_state_record_layer_consistent (initial cfg))
=
  ()

let lemma_initial_record_keys_consistent
  (cfg:connection_config)
  : Lemma
      (requires cfg.config_role == ClientEndpoint)
      (ensures connection_state_record_keys_consistent (initial cfg))
=
  ()

let lemma_initial_layered_log_consistent
  (cfg:connection_config)
  : Lemma
      (requires cfg.config_role == ClientEndpoint)
      (ensures connection_state_layered_log_consistent (initial cfg))
=
  lemma_initial_layered_log_consistent_for_role ClientEndpoint cfg

let rec lemma_app_sent_messages_snoc
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        app_sent_messages (events @ [ev]) ==
          app_sent_messages events @ conn_event_app_sent_delta ev)
      (decreases events)
=
  match events with
  | [] -> ()
  | hd :: tl ->
    lemma_app_sent_messages_snoc tl ev;
    append_assoc
      (conn_event_app_sent_delta hd)
      (app_sent_messages tl)
      (conn_event_app_sent_delta ev)

let rec lemma_app_received_messages_snoc
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        app_received_messages (events @ [ev]) ==
          app_received_messages events @ conn_event_app_received_delta ev)
      (decreases events)
=
  match events with
  | [] -> ()
  | hd :: tl ->
    lemma_app_received_messages_snoc tl ev;
    append_assoc
      (conn_event_app_received_delta hd)
      (app_received_messages tl)
      (conn_event_app_received_delta ev)

let rec lemma_transcript_bytes_snoc
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        B.append
          (transcript_bytes_of_conn_events events)
          (conn_event_transcript_delta ev) ==
        transcript_bytes_of_conn_events (events @ [ev]))
      (decreases events)
=
  match events with
  | [] ->
    CL.lemma_append_empty_left (conn_event_transcript_delta ev);
    CL.lemma_append_empty_right (conn_event_transcript_delta ev)
  | hd :: tl ->
    lemma_transcript_bytes_snoc tl ev;
    Seq.append_assoc
      (conn_event_transcript_delta hd)
      (transcript_bytes_of_conn_events tl)
      (conn_event_transcript_delta ev)

let rec lemma_key_update_response_pending_after_events_snoc
  (pending:bool)
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        key_update_response_pending_after_events_from pending (events @ [ev]) ==
          key_update_response_pending_step
            (key_update_response_pending_after_events_from pending events)
            ev)
      (decreases events)
=
  match events with
  | [] -> ()
  | hd :: tl ->
    lemma_key_update_response_pending_after_events_snoc
      (key_update_response_pending_step pending hd)
      tl
      ev

let lemma_key_update_response_pending_snoc
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        key_update_response_pending_of_conn_events (events @ [ev]) ==
          key_update_response_pending_step
            (key_update_response_pending_of_conn_events events)
            ev)
=
  lemma_key_update_response_pending_after_events_snoc false events ev

let rec lemma_projected_record_layer_after_events_snoc_for_role
  (role:endpoint_role)
  (record:projected_record_layer_state)
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        projected_record_layer_after_events_from_for_role role record (events @ [ev]) ==
          projected_record_layer_step_for_role
            role
            (projected_record_layer_after_events_from_for_role role record events)
            ev)
      (decreases events)
=
  match events with
  | [] -> ()
  | hd :: tl ->
    lemma_projected_record_layer_after_events_snoc_for_role
      role
      (projected_record_layer_step_for_role role record hd)
      tl
      ev

let lemma_projected_record_layer_after_events_snoc
  (record:projected_record_layer_state)
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        projected_record_layer_after_events_from record (events @ [ev]) ==
          projected_record_layer_step
            (projected_record_layer_after_events_from record events)
            ev)
=
  lemma_projected_record_layer_after_events_snoc_for_role
    ClientEndpoint
    record
    events
    ev

let lemma_projected_record_layer_snoc_for_role
  (role:endpoint_role)
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        projected_record_layer_of_conn_events_for_role role (events @ [ev]) ==
          projected_record_layer_step_for_role
            role
            (projected_record_layer_of_conn_events_for_role role events)
            ev)
=
  lemma_projected_record_layer_after_events_snoc_for_role
    role
    initial_projected_record_layer_state
    events
    ev

let lemma_projected_record_layer_snoc
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        projected_record_layer_of_conn_events (events @ [ev]) ==
          projected_record_layer_step
            (projected_record_layer_of_conn_events events)
            ev)
=
  lemma_projected_record_layer_snoc_for_role ClientEndpoint events ev

let rec lemma_projected_advance_records_of_record
  (st:R.direction_state)
  (n:nat)
  : Lemma
      (ensures
        projected_direction_state_of_record (advance_direction_records st n) ==
          projected_advance_records (projected_direction_state_of_record st) n)
      (decreases n)
=
  if n = 0 then ()
  else lemma_projected_advance_records_of_record st (n - 1)

let lemma_projected_next_seq_of_record
  (st:R.direction_state)
  : Lemma
      (projected_direction_state_of_record (R.next_seq st) ==
        projected_next_seq (projected_direction_state_of_record st))
=
  ()

let lemma_projected_install_keys_of_record
  (st:R.direction_state)
  (epoch:R.epoch)
  (key:C.aead_key)
  (iv:C.aead_nonce)
  : Lemma
      (projected_direction_state_of_record (R.install_keys st epoch key iv) ==
        projected_install_keys epoch)
=
  ()

let lemma_projected_install_record_keys_of_record
  (record:record_layer_state)
  (install:traffic_key_install)
  : Lemma
      (projected_record_layer_state_of_record (install_record_keys record install) ==
        projected_install_record_keys
          (projected_record_layer_state_of_record record)
          install)
=
  match install.install_epoch, install.install_direction with
  | TrafficApplication, TrafficWrite -> ()
  | _, TrafficWrite ->
    lemma_projected_install_keys_of_record
      record.record_write
      (traffic_record_epoch install.install_epoch)
      install.install_material.traffic_key
      install.install_material.traffic_iv
  | _, TrafficRead ->
    lemma_projected_install_keys_of_record
      record.record_read
      (traffic_record_epoch install.install_epoch)
      install.install_material.traffic_key
      install.install_material.traffic_iv

let lemma_projected_install_record_keys_of_record_for_role
  (role:endpoint_role)
  (record:record_layer_state)
  (install:traffic_key_install)
  : Lemma
      (projected_record_layer_state_of_record
        (install_record_keys_for_role role record install) ==
       projected_install_record_keys_for_role
        role
        (projected_record_layer_state_of_record record)
        install)
=
  match role, install.install_epoch, install.install_direction with
  | ServerEndpoint, TrafficApplication, TrafficWrite ->
    lemma_projected_install_keys_of_record
      record.record_write
      R.Application
      install.install_material.traffic_key
      install.install_material.traffic_iv
  | _, _, _ ->
    lemma_projected_install_record_keys_of_record record install

let lemma_projected_client_application_write_after_finished
  (record:record_layer_state)
  (keys:key_schedule_state)
  : Lemma
      (requires Some? keys.ks_client_application_traffic)
      (ensures
        projected_record_layer_state_of_record
          (install_client_application_write_after_finished record keys) ==
        projected_client_application_write_after_finished
          (projected_record_layer_state_of_record record))
=
  match keys.ks_client_application_traffic with
  | Some material ->
    lemma_projected_install_keys_of_record
      (R.next_seq record.record_write)
      R.Application
      material.traffic_key
      material.traffic_iv
  | None -> assert False

let lemma_projected_record_next_read
  (record:record_layer_state)
  : Lemma
      (ensures
       projected_record_layer_state_of_record
         { record with record_read = R.next_seq record.record_read } ==
       { projected_record_layer_state_of_record record with
           projected_read =
             projected_next_seq
               (projected_record_layer_state_of_record record).projected_read })
=
  lemma_projected_next_seq_of_record record.record_read

let lemma_projected_record_next_write
  (record:record_layer_state)
  : Lemma
      (ensures
       projected_record_layer_state_of_record
         { record with record_write = R.next_seq record.record_write } ==
       { projected_record_layer_state_of_record record with
           projected_write =
             projected_next_seq
               (projected_record_layer_state_of_record record).projected_write })
=
  lemma_projected_next_seq_of_record record.record_write

let lemma_projected_record_advance_write
  (record:record_layer_state)
  (n:nat)
  : Lemma
      (ensures
       projected_record_layer_state_of_record
         { record with record_write = advance_direction_records record.record_write n } ==
       { projected_record_layer_state_of_record record with
           projected_write =
             projected_advance_records
               (projected_record_layer_state_of_record record).projected_write
               n })
=
  lemma_projected_advance_records_of_record record.record_write n

let rec lemma_step_model_many_snoc
  (model0:connection_model)
  (events:list conn_event)
  (ev:conn_event)
  (model1:connection_model)
  (model2:connection_model)
  : Lemma
      (requires
        step_model_many model0 events == Some model1 /\
        step_model model1 ev == Some model2)
      (ensures
        step_model_many model0 (events @ [ev]) == Some model2)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev0 :: rest ->
    (match step_model model0 ev0 with
     | Some mid -> lemma_step_model_many_snoc mid rest ev model1 model2
     | None -> assert False)

let lemma_step_model_preserves_config
  (model:connection_model)
  (ev:conn_event)
  (model':connection_model)
  : Lemma
      (requires step_model model ev == Some model')
      (ensures model'.model_config == model.model_config)
=
  ()

let lemma_step_model_key_update_pending_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires step_model model0 ev == Some model1)
      (ensures model_key_update_pending_delta model0 ev model1)
=
  match ev with
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Received, M.TlsKeyUpdate req ->
       (match model0.model_control with
        | ControlApplicationData ->
          (match model0.model_handshake.hs_keys.ks_server_application_traffic with
           | Some _ -> ()
           | None -> assert False)
        | _ -> assert False)
     | CL.Sent, M.TlsKeyUpdate req ->
       (match req with
        | M.UpdateNotRequested ->
          (match model0.model_control with
           | ControlApplicationData ->
             (match model0.model_handshake.hs_keys.ks_client_application_traffic with
              | Some _ ->
                if model0.model_application.app_key_update_response_pending then ()
                else assert False
              | None -> assert False)
           | _ -> assert False)
        | M.UpdateRequested -> assert False)
     | _, _ -> ())
  | ConnLocalEvent _ -> ()

let lemma_step_model_record_keys_consistent
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires
        legal_event model0 ev /\
        step_model model0 ev == Some model1 /\
        model0.model_config.config_role == ClientEndpoint /\
        model_record_keys_consistent model0)
      (ensures model_record_keys_consistent model1)
=
  assert (model1.model_config == model0.model_config);
  match ev with
  | ConnLocalEvent local ->
    (match local with
     | LocalDeriveSharedSecret _ ->
       assert (model1.model_record == model0.model_record);
       assert (model1.model_handshake.hs_keys.ks_client_handshake_traffic ==
         model0.model_handshake.hs_keys.ks_client_handshake_traffic);
       assert (model1.model_handshake.hs_keys.ks_server_handshake_traffic ==
         model0.model_handshake.hs_keys.ks_server_handshake_traffic);
       assert (model1.model_handshake.hs_keys.ks_client_application_traffic ==
         model0.model_handshake.hs_keys.ks_client_application_traffic);
       assert (model1.model_handshake.hs_keys.ks_server_application_traffic ==
         model0.model_handshake.hs_keys.ks_server_application_traffic)
     | LocalInstallTrafficKeys install ->
       (match install.install_epoch, install.install_direction with
        | TrafficHandshake, TrafficWrite ->
          assert (model1.model_record.record_write ==
            R.install_keys
              model0.model_record.record_write
              R.Handshake
              install.install_material.traffic_key
              install.install_material.traffic_iv);
          assert (model1.model_handshake.hs_keys.ks_client_handshake_traffic ==
            Some install.install_material)
        | TrafficHandshake, TrafficRead ->
          assert (model1.model_record.record_read ==
            R.install_keys
              model0.model_record.record_read
              R.Handshake
              install.install_material.traffic_key
              install.install_material.traffic_iv);
          assert (model1.model_handshake.hs_keys.ks_server_handshake_traffic ==
            Some install.install_material)
        | TrafficApplication, TrafficWrite ->
          assert (model1.model_record == model0.model_record);
          assert (model1.model_control == model0.model_control);
          assert (model0.model_control == ControlHandshaking HsServerFinishedVerified)
        | TrafficApplication, TrafficRead ->
          assert (model1.model_record.record_read ==
            R.install_keys
              model0.model_record.record_read
              R.Application
              install.install_material.traffic_key
              install.install_material.traffic_iv);
          assert (model1.model_handshake.hs_keys.ks_server_application_traffic ==
            Some install.install_material))
     | LocalInstallTrafficKeysForRole role_install ->
       assert (role_install.install_role == ClientEndpoint);
       let install = role_install.install_payload in
       (match install.install_epoch, install.install_direction with
        | TrafficHandshake, TrafficWrite ->
          assert (model1.model_record.record_write ==
            R.install_keys
              model0.model_record.record_write
              R.Handshake
              install.install_material.traffic_key
              install.install_material.traffic_iv);
          assert (model1.model_handshake.hs_keys.ks_client_handshake_traffic ==
            Some install.install_material)
        | TrafficHandshake, TrafficRead ->
          assert (model1.model_record.record_read ==
            R.install_keys
              model0.model_record.record_read
              R.Handshake
              install.install_material.traffic_key
              install.install_material.traffic_iv);
          assert (model1.model_handshake.hs_keys.ks_server_handshake_traffic ==
            Some install.install_material)
        | TrafficApplication, TrafficWrite ->
          assert (model1.model_record == model0.model_record);
          assert (model1.model_control == model0.model_control);
          assert (model0.model_control == ControlHandshaking HsServerFinishedVerified)
        | TrafficApplication, TrafficRead ->
          assert (model1.model_record.record_read ==
            R.install_keys
              model0.model_record.record_read
              R.Application
              install.install_material.traffic_key
              install.install_material.traffic_iv);
          assert (model1.model_handshake.hs_keys.ks_server_application_traffic ==
            Some install.install_material))
     | LocalFail _ -> ()
     | _ ->
       assert (model1.model_record == model0.model_record);
       assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys))
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Sent, M.TlsHandshake (M.Finished _) ->
       (match model0.model_control with
        | ControlHandshaking HsServerFinishedVerified ->
          assert (Some? model0.model_handshake.hs_keys.ks_client_application_traffic);
          (match model0.model_handshake.hs_keys.ks_client_application_traffic with
           | Some material ->
             assert (model1.model_record.record_write ==
               R.install_keys
                 (R.next_seq model0.model_record.record_write)
                 R.Application
                 material.traffic_key
                 material.traffic_iv);
             assert (model1.model_handshake.hs_keys.ks_client_application_traffic ==
               Some material)
           | None -> assert False)
        | _ -> assert False)
     | CL.Received, M.TlsKeyUpdate _ ->
       (match model0.model_control with
        | ControlApplicationData ->
          assert (Some? model0.model_handshake.hs_keys.ks_server_application_traffic);
          (match model0.model_handshake.hs_keys.ks_server_application_traffic with
           | Some old_server_app ->
             let new_server_app = updated_traffic_key_material old_server_app in
             assert (model1.model_record.record_read ==
               R.install_keys
                 (R.next_seq model0.model_record.record_read)
                 R.Application
                 new_server_app.traffic_key
                 new_server_app.traffic_iv);
             assert (model1.model_handshake.hs_keys.ks_server_application_traffic ==
               Some new_server_app)
           | None -> assert False)
        | _ -> assert False)
     | CL.Sent, M.TlsKeyUpdate M.UpdateNotRequested ->
       (match model0.model_control with
        | ControlApplicationData ->
          assert (Some? model0.model_handshake.hs_keys.ks_client_application_traffic);
          assert (model0.model_application.app_key_update_response_pending);
          (match model0.model_handshake.hs_keys.ks_client_application_traffic with
           | Some old_client_app ->
             let new_client_app = updated_traffic_key_material old_client_app in
             assert (model1.model_record.record_write ==
               R.install_keys
                 (R.next_seq model0.model_record.record_write)
                 R.Application
                 new_client_app.traffic_key
                 new_client_app.traffic_iv);
             assert (model1.model_handshake.hs_keys.ks_client_application_traffic ==
               Some new_client_app)
           | None -> assert False)
        | _ -> assert False)
     | CL.Sent, M.TlsApplicationData bytes ->
       assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
       assert (model1.model_record.record_write ==
         advance_direction_records
           model0.model_record.record_write
           (S.application_data_record_count bytes));
       lemma_record_write_keys_advance
         model0.model_control
         model0.model_handshake.hs_keys
         model0.model_record.record_write
         (S.application_data_record_count bytes)
     | CL.Received, M.TlsHandshake (M.EncryptedExtensions _)
     | CL.Received, M.TlsHandshake (M.Certificate _)
     | CL.Received, M.TlsHandshake (M.CertificateVerify _)
     | CL.Received, M.TlsHandshake (M.Finished _)
     | CL.Received, M.TlsApplicationData _
     | CL.Received, M.TlsIgnoredPostHandshake _ ->
       assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
       assert (model1.model_record.record_read ==
         R.next_seq model0.model_record.record_read);
       lemma_record_read_keys_next_seq
         model0.model_handshake.hs_keys
         model0.model_record.record_read
     | CL.Received, M.TlsAlert T.CloseNotify ->
       (match model1.model_control with
        | ControlFailed _ -> ()
        | _ ->
          assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
          assert (model1.model_record.record_read ==
            R.next_seq model0.model_record.record_read);
          lemma_record_read_keys_next_seq
            model0.model_handshake.hs_keys
            model0.model_record.record_read)
     | CL.Sent, M.TlsAlert T.CloseNotify ->
       (match model1.model_control with
        | ControlFailed _ -> ()
        | _ ->
          assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
          assert (model1.model_record.record_write ==
            R.next_seq model0.model_record.record_write);
          lemma_record_write_keys_next_seq
            model0.model_control
            model0.model_handshake.hs_keys
            model0.model_record.record_write)
     | _, M.TlsAlert alert ->
       (match model1.model_control with
        | ControlFailed _ -> ()
        | _ ->
          assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys))
     | _ ->
       (match model1.model_control with
        | ControlFailed _ -> ()
        | _ ->
          assert (model1.model_record == model0.model_record);
          assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys)))

let lemma_step_model_record_keys_consistent_for_role
  (role:endpoint_role)
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
     (requires
       legal_event model0 ev /\
       step_model model0 ev == Some model1 /\
       role == model0.model_config.config_role /\
       model_record_keys_consistent_for_role role model0)
     (ensures model_record_keys_consistent_for_role role model1)
=
  match role with
  | ClientEndpoint ->
    assert (model0.model_config.config_role == ClientEndpoint);
    assert (model_record_keys_consistent model0);
    lemma_step_model_record_keys_consistent model0 ev model1
  | ServerEndpoint ->
    (match ev with
     | ConnLocalEvent local ->
      (match local with
       | LocalInstallTrafficKeysForRole role_install ->
         assert (role_install.install_role == model0.model_config.config_role);
         assert (role_install.install_role == ServerEndpoint);
         let install = role_install.install_payload in
         lemma_step_role_install_record_keys_consistent_for_role
           ServerEndpoint
           model0
           install
           model1
       | LocalInstallTrafficKeys _ ->
         assert False
       | LocalDeriveSharedSecret _ ->
         assert (model1.model_record == model0.model_record);
         assert (model1.model_handshake.hs_keys.ks_client_handshake_traffic ==
           model0.model_handshake.hs_keys.ks_client_handshake_traffic);
         assert (model1.model_handshake.hs_keys.ks_server_handshake_traffic ==
           model0.model_handshake.hs_keys.ks_server_handshake_traffic);
         assert (model1.model_handshake.hs_keys.ks_client_application_traffic ==
           model0.model_handshake.hs_keys.ks_client_application_traffic);
         assert (model1.model_handshake.hs_keys.ks_server_application_traffic ==
           model0.model_handshake.hs_keys.ks_server_application_traffic)
       | LocalVerifyClientFinished _ ->
         assert (model1.model_record == model0.model_record);
         assert (model1.model_control == ControlApplicationData);
         assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
         assert (application_record_keys_installed_for_role ServerEndpoint model0);
         assert (application_record_keys_installed_for_role ServerEndpoint model1)
       | LocalFail _ ->
         ()
       | _ ->
         assert (model1.model_record == model0.model_record);
         assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys))
     | ConnNetworkEvent msg ->
      (match msg.CL.message_value with
       | M.TlsApplicationData bytes ->
         assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
         (match msg.CL.message_direction with
          | CL.Sent ->
            assert (model1.model_record.record_write ==
              advance_direction_records
                model0.model_record.record_write
                (S.application_data_record_count bytes));
            assert (model1.model_record.record_read ==
              model0.model_record.record_read);
            lemma_record_keys_advance_for_role
              ServerEndpoint
              TrafficWrite
              model0.model_control
              model0.model_handshake.hs_keys
              model0.model_record.record_write
              (S.application_data_record_count bytes)
          | CL.Received ->
            assert (model1.model_record.record_read ==
              R.next_seq model0.model_record.record_read);
            assert (model1.model_record.record_write ==
              model0.model_record.record_write);
            lemma_record_keys_next_seq_for_role
              ServerEndpoint
              TrafficRead
              model0.model_control
              model0.model_handshake.hs_keys
              model0.model_record.record_read)
       | M.TlsHandshake (M.ClientHello _)
       | M.TlsHandshake (M.ServerHello _) ->
         assert (model1.model_record == model0.model_record);
         assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys)
       | M.TlsHandshake (M.Finished _) ->
         assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
         (match msg.CL.message_direction with
          | CL.Sent ->
            assert (model1.model_record.record_write ==
              R.next_seq model0.model_record.record_write);
            assert (model1.model_record.record_read ==
              model0.model_record.record_read);
            lemma_record_keys_next_seq_for_role
              ServerEndpoint
              TrafficWrite
              model0.model_control
              model0.model_handshake.hs_keys
              model0.model_record.record_write
          | CL.Received ->
            assert (model1.model_record.record_read ==
              R.next_seq model0.model_record.record_read);
            assert (model1.model_record.record_write ==
              model0.model_record.record_write);
            lemma_record_keys_next_seq_for_role
              ServerEndpoint
              TrafficRead
              model0.model_control
              model0.model_handshake.hs_keys
              model0.model_record.record_read)
       | M.TlsHandshake (M.EncryptedExtensions _)
       | M.TlsHandshake (M.Certificate _)
       | M.TlsHandshake (M.CertificateVerify _) ->
         assert (msg.CL.message_direction == CL.Sent);
         assert (model1.model_record.record_write ==
           R.next_seq model0.model_record.record_write);
         assert (model1.model_record.record_read ==
           model0.model_record.record_read);
         assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
         lemma_record_keys_next_seq_for_role
           ServerEndpoint
           TrafficWrite
           model0.model_control
           model0.model_handshake.hs_keys
           model0.model_record.record_write
       | M.TlsAlert T.CloseNotify ->
         (match model0.model_control with
          | ControlApplicationData ->
            assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
            (match msg.CL.message_direction with
             | CL.Sent ->
               assert (model1.model_record.record_write ==
                 R.next_seq model0.model_record.record_write);
               assert (model1.model_record.record_read ==
                 model0.model_record.record_read);
               lemma_record_keys_next_seq_for_role
                 ServerEndpoint
                 TrafficWrite
                 model0.model_control
                 model0.model_handshake.hs_keys
                 model0.model_record.record_write
             | CL.Received ->
               assert (model1.model_record.record_read ==
                 R.next_seq model0.model_record.record_read);
               assert (model1.model_record.record_write ==
                 model0.model_record.record_write);
               lemma_record_keys_next_seq_for_role
                 ServerEndpoint
                 TrafficRead
                 model0.model_control
                 model0.model_handshake.hs_keys
                 model0.model_record.record_read)
          | ControlClosing ->
            assert (msg.CL.message_direction == CL.Received);
            assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
            assert (model1.model_record.record_read ==
              R.next_seq model0.model_record.record_read);
            assert (model1.model_record.record_write ==
              model0.model_record.record_write);
            lemma_record_keys_next_seq_for_role
              ServerEndpoint
              TrafficRead
              model0.model_control
              model0.model_handshake.hs_keys
              model0.model_record.record_read
          | _ ->
            assert (ControlFailed? model1.model_control))
       | M.TlsAlert _ ->
         assert (ControlFailed? model1.model_control)
       | M.TlsChangeCipherSpec ->
         assert (model1 == model0)
       | _ ->
         assert False))

let lemma_step_model_record_layer_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires
        legal_event model0 ev /\
        step_model model0 ev == Some model1)
      (ensures model_record_layer_delta model0 ev model1)
=
  (match ev with
  | ConnLocalEvent local ->
    assert (ev == ConnLocalEvent local);
    (match local with
     | LocalInstallTrafficKeys install ->
       assert (model1.model_record == install_record_keys model0.model_record install);
       lemma_projected_install_record_keys_of_record model0.model_record install;
       assert (model_record_layer_delta model0 ev model1)
     | LocalInstallTrafficKeysForRole role_install ->
      let install = role_install.install_payload in
      assert (role_install.install_role == model0.model_config.config_role);
      assert (model1.model_record ==
        install_record_keys_for_role
          role_install.install_role
          model0.model_record
          install);
      lemma_projected_install_record_keys_of_record_for_role
        role_install.install_role
        model0.model_record
        install;
      assert (model_record_layer_delta model0 ev model1)
     | _ ->
       assert (model1.model_record == model0.model_record);
       assert (model_record_layer_delta model0 ev model1))
  | ConnNetworkEvent msg ->
    assert (ev == ConnNetworkEvent msg);
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Sent, M.TlsApplicationData bytes ->
       assert (model1.model_record == {
         model0.model_record with
           record_write =
             advance_direction_records
               model0.model_record.record_write
               (S.application_data_record_count bytes)
       });
       lemma_projected_record_advance_write
         model0.model_record
         (S.application_data_record_count bytes);
       assert (model_record_layer_delta model0 ev model1)
     | CL.Sent, M.TlsHandshake (M.Finished _) ->
       (match model0.model_config.config_role with
        | ClientEndpoint ->
          (match model0.model_control with
           | ControlHandshaking HsServerFinishedVerified ->
             assert (Some? model0.model_handshake.hs_keys.ks_client_application_traffic);
             (match model0.model_handshake.hs_keys.ks_client_application_traffic with
              | Some _ ->
                assert (model1.model_record ==
                  install_client_application_write_after_finished
                    model0.model_record
                    model0.model_handshake.hs_keys);
                lemma_projected_client_application_write_after_finished
                  model0.model_record
                  model0.model_handshake.hs_keys;
                assert (model_record_layer_delta model0 ev model1)
              | None -> assert False)
           | _ -> assert False)
        | ServerEndpoint ->
          (match model0.model_control with
           | ControlHandshaking HsServerEncryptedFlightSent ->
             assert (model1.model_record == {
               model0.model_record with
                 record_write = R.next_seq model0.model_record.record_write
             });
             lemma_projected_record_next_write model0.model_record;
             assert (model_record_layer_delta model0 ev model1)
           | _ -> assert False))
     | CL.Received, M.TlsKeyUpdate _ ->
       (match model0.model_control with
        | ControlApplicationData ->
          assert (Some? model0.model_handshake.hs_keys.ks_server_application_traffic);
          (match model0.model_handshake.hs_keys.ks_server_application_traffic with
           | Some old_server_app ->
             let new_server_app = updated_traffic_key_material old_server_app in
             assert (model1.model_record == {
               model0.model_record with
                 record_read =
                   R.install_keys
                     (R.next_seq model0.model_record.record_read)
                     R.Application
                     new_server_app.traffic_key
                     new_server_app.traffic_iv
             });
             lemma_projected_install_keys_of_record
               (R.next_seq model0.model_record.record_read)
               R.Application
               new_server_app.traffic_key
               new_server_app.traffic_iv;
             assert (model_record_layer_delta model0 ev model1)
           | None -> assert False)
        | _ -> assert False)
     | CL.Sent, M.TlsKeyUpdate req ->
       (match req with
        | M.UpdateNotRequested ->
          (match model0.model_control with
           | ControlApplicationData ->
             assert (Some? model0.model_handshake.hs_keys.ks_client_application_traffic);
             (match model0.model_handshake.hs_keys.ks_client_application_traffic with
              | Some _ ->
                assert (model0.model_application.app_key_update_response_pending);
                (match model0.model_handshake.hs_keys.ks_client_application_traffic with
                 | Some old_client_app ->
                   let new_client_app = updated_traffic_key_material old_client_app in
                   assert (model1.model_record == {
                     model0.model_record with
                       record_write =
                         R.install_keys
                           (R.next_seq model0.model_record.record_write)
                           R.Application
                           new_client_app.traffic_key
                           new_client_app.traffic_iv
                   });
                   lemma_projected_install_keys_of_record
                     (R.next_seq model0.model_record.record_write)
                     R.Application
                     new_client_app.traffic_key
                     new_client_app.traffic_iv;
                   assert (model_record_layer_delta model0 ev model1)
                 | None -> assert False)
              | None -> assert False)
           | _ -> assert False)
        | M.UpdateRequested -> assert False)
     | CL.Received, M.TlsHandshake (M.EncryptedExtensions _)
     | CL.Received, M.TlsHandshake (M.Certificate _)
     | CL.Received, M.TlsHandshake (M.CertificateVerify _)
     | CL.Received, M.TlsHandshake (M.Finished _) ->
       assert (model1.model_record == {
         model0.model_record with
           record_read = R.next_seq model0.model_record.record_read
       });
       lemma_projected_record_next_read model0.model_record;
       assert (
         projected_record_layer_step_for_role
           model0.model_config.config_role
           (projected_record_layer_state_of_record model0.model_record)
           ev ==
         { projected_record_layer_state_of_record model0.model_record with
             projected_read =
               projected_next_seq
                 (projected_record_layer_state_of_record model0.model_record).projected_read });
       assert (model_record_layer_delta model0 ev model1)
     | CL.Sent, M.TlsHandshake (M.EncryptedExtensions _)
     | CL.Sent, M.TlsHandshake (M.Certificate _)
     | CL.Sent, M.TlsHandshake (M.CertificateVerify _) ->
       assert (model1.model_record == {
         model0.model_record with
           record_write = R.next_seq model0.model_record.record_write
       });
       lemma_projected_record_next_write model0.model_record;
       assert (
         projected_record_layer_step_for_role
           model0.model_config.config_role
           (projected_record_layer_state_of_record model0.model_record)
           ev ==
         { projected_record_layer_state_of_record model0.model_record with
             projected_write =
               projected_next_seq
                 (projected_record_layer_state_of_record model0.model_record).projected_write });
       assert (model_record_layer_delta model0 ev model1)
     | CL.Received, M.TlsApplicationData _ ->
       assert (model1.model_record == {
         model0.model_record with
           record_read = R.next_seq model0.model_record.record_read
       });
       lemma_projected_record_next_read model0.model_record;
       assert (
         projected_record_layer_step_for_role
           model0.model_config.config_role
           (projected_record_layer_state_of_record model0.model_record)
           ev ==
         { projected_record_layer_state_of_record model0.model_record with
             projected_read =
               projected_next_seq
                 (projected_record_layer_state_of_record model0.model_record).projected_read });
       assert (model_record_layer_delta model0 ev model1)
     | CL.Received, M.TlsIgnoredPostHandshake _ ->
       assert (model1.model_record == {
         model0.model_record with
           record_read = R.next_seq model0.model_record.record_read
       });
       lemma_projected_record_next_read model0.model_record;
       assert (
         projected_record_layer_step_for_role
           model0.model_config.config_role
           (projected_record_layer_state_of_record model0.model_record)
           ev ==
         { projected_record_layer_state_of_record model0.model_record with
             projected_read =
               projected_next_seq
                 (projected_record_layer_state_of_record model0.model_record).projected_read });
       assert (model_record_layer_delta model0 ev model1)
     | CL.Received, M.TlsAlert T.CloseNotify ->
       (match model0.model_control with
        | ControlApplicationData
        | ControlClosing ->
          assert (model1.model_record == {
            model0.model_record with
              record_read = R.next_seq model0.model_record.record_read
          });
          lemma_projected_record_next_read model0.model_record;
          assert (
            projected_record_layer_step_for_role
              model0.model_config.config_role
              (projected_record_layer_state_of_record model0.model_record)
              ev ==
            { projected_record_layer_state_of_record model0.model_record with
                projected_read =
                  projected_next_seq
                    (projected_record_layer_state_of_record model0.model_record).projected_read });
          assert (model_record_layer_delta model0 ev model1)
        | _ ->
          assert (model1.model_control == ControlFailed (T.AlertError T.CloseNotify));
          assert (model_record_layer_delta model0 ev model1))
     | CL.Sent, M.TlsAlert T.CloseNotify ->
       (match model0.model_control with
        | ControlApplicationData ->
          assert (model1.model_record == {
            model0.model_record with
              record_write = R.next_seq model0.model_record.record_write
          });
          lemma_projected_record_next_write model0.model_record;
          assert (
            projected_record_layer_step_for_role
              model0.model_config.config_role
              (projected_record_layer_state_of_record model0.model_record)
              ev ==
            { projected_record_layer_state_of_record model0.model_record with
                projected_write =
                  projected_next_seq
                    (projected_record_layer_state_of_record model0.model_record).projected_write });
          assert (model_record_layer_delta model0 ev model1)
        | _ ->
          assert (model1.model_control == ControlFailed (T.AlertError T.CloseNotify));
          assert (model_record_layer_delta model0 ev model1))
     | _, _ ->
       assert (model1.model_record == model0.model_record);
       assert (model_record_layer_delta model0 ev model1)))

let lemma_step_model_pending_application_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires step_model model0 ev == Some model1)
      (ensures model_pending_application_delta model0 ev model1)
=
  match ev with
  | ConnLocalEvent local ->
    (match local with
     | LocalDeliverApplicationData _
     | LocalFail _ -> ()
     | _ ->
       assert (model1.model_application == model0.model_application))
  | ConnNetworkEvent msg ->
    (match msg.CL.message_value with
     | M.TlsApplicationData _ ->
       assert (model1.model_application.app_pending_plaintext ==
         model0.model_application.app_pending_plaintext);
       assert (model1.model_application.app_pending_source_record ==
         model0.model_application.app_pending_source_record);
       assert (model1.model_application.app_pending_source_offset ==
         model0.model_application.app_pending_source_offset);
       assert (model1.model_application.app_pending_received_raw ==
         model0.model_application.app_pending_received_raw)
     | M.TlsKeyUpdate _ ->
       assert (model1.model_application.app_pending_plaintext ==
         model0.model_application.app_pending_plaintext);
       assert (model1.model_application.app_pending_source_record ==
         model0.model_application.app_pending_source_record);
       assert (model1.model_application.app_pending_source_offset ==
         model0.model_application.app_pending_source_offset);
       assert (model1.model_application.app_pending_received_raw ==
         model0.model_application.app_pending_received_raw)
     | _ ->
       assert (model1.model_application == model0.model_application))

let lemma_step_model_transcript_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires step_model model0 ev == Some model1)
      (ensures model_transcript_delta model0 ev model1)
=
  let t0 = model0.model_handshake.hs_transcript in
  match ev with
  | ConnLocalEvent local ->
    (match local with
     | LocalVerifyFinished _ -> ()
     | LocalVerifyClientFinished _ -> ()
     | _ ->
       CL.lemma_append_empty_right t0;
       Seq.lemma_eq_refl model1.model_handshake.hs_transcript t0)
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Sent, M.TlsHandshake (M.ClientHello _) -> ()
     | CL.Received, M.TlsHandshake (M.ClientHello _) -> ()
     | CL.Received, M.TlsHandshake (M.ServerHello _) -> ()
     | CL.Sent, M.TlsHandshake (M.ServerHello _) -> ()
     | CL.Sent, M.TlsHandshake (M.EncryptedExtensions _) -> ()
     | CL.Received, M.TlsHandshake (M.EncryptedExtensions _) -> ()
     | CL.Sent, M.TlsHandshake (M.Certificate _) -> ()
     | CL.Received, M.TlsHandshake (M.Certificate _) -> ()
     | CL.Sent, M.TlsHandshake (M.CertificateVerify _) -> ()
     | CL.Received, M.TlsHandshake (M.CertificateVerify _) -> ()
     | CL.Sent, M.TlsHandshake (M.Finished _) -> ()
     | _, _ ->
       CL.lemma_append_empty_right t0;
       Seq.lemma_eq_refl model1.model_handshake.hs_transcript t0)

let lemma_step_model_app_log_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires step_model model0 ev == Some model1)
      (ensures model_app_log_delta model0 ev model1)
=
  let app = model0.model_application.app_log in
  match ev with
  | ConnLocalEvent local ->
    (match local with
     | LocalDeliverApplicationData bytes ->
       (match model0.model_control with
        | ControlApplicationData -> ()
        | _ -> assert False)
     | _ ->
       append_l_nil app.CL.app_sent;
       append_l_nil app.CL.app_received)
  | ConnNetworkEvent msg ->
    (match msg.CL.message_value with
     | M.TlsApplicationData bytes ->
       (match model0.model_control with
        | ControlApplicationData ->
          (match msg.CL.message_direction with
           | CL.Sent -> append_l_nil app.CL.app_received
           | CL.Received -> append_l_nil app.CL.app_sent)
        | _ -> assert False)
     | _ ->
       append_l_nil app.CL.app_sent;
       append_l_nil app.CL.app_received)

let rec lemma_connection_log_trace_sent_tls
  (events:list conn_event)
  : Lemma
      (ensures
        CL.sent_tls_of_host_trace (connection_log_trace_of_conn_events events) ==
          sent_tls_messages events)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev :: rest ->
    lemma_connection_log_trace_sent_tls rest;
    match ev with
    | ConnNetworkEvent _ -> ()
    | ConnLocalEvent local ->
      (match local with
       | LocalValidateCertificate _
       | LocalDeliverApplicationData _
       | LocalFail _ -> ()
       | _ -> ())

let rec lemma_connection_log_trace_received_tls
  (events:list conn_event)
  : Lemma
      (ensures
        CL.received_tls_of_host_trace (connection_log_trace_of_conn_events events) ==
          received_tls_messages events)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev :: rest ->
    lemma_connection_log_trace_received_tls rest;
    match ev with
    | ConnNetworkEvent _ -> ()
    | ConnLocalEvent local ->
      (match local with
       | LocalValidateCertificate _
       | LocalDeliverApplicationData _
       | LocalFail _ -> ()
       | _ -> ())

let rec lemma_connection_log_trace_state_events
  (events:list conn_event)
  : Lemma
      (ensures
        CL.state_events_of_host_trace (connection_log_trace_of_conn_events events) ==
          state_machine_events events)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev :: rest ->
    lemma_connection_log_trace_state_events rest;
    match ev with
    | ConnNetworkEvent _ -> ()
    | ConnLocalEvent local ->
      (match local with
       | LocalValidateCertificate _
       | LocalDeliverApplicationData _
       | LocalFail _ -> ()
       | _ -> ())

let rec lemma_connection_log_trace_app_sent
  (events:list conn_event)
  : Lemma
      (ensures
        CL.app_sent_of_host_trace (connection_log_trace_of_conn_events events) ==
          app_sent_messages events)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev :: rest ->
    lemma_connection_log_trace_app_sent rest;
    match ev with
    | ConnNetworkEvent _ -> ()
    | ConnLocalEvent local ->
      (match local with
       | LocalValidateCertificate _
       | LocalDeliverApplicationData _
       | LocalFail _ -> ()
       | _ -> ())

let rec lemma_connection_log_trace_app_received
  (events:list conn_event)
  : Lemma
      (ensures
        CL.app_received_of_host_trace (connection_log_trace_of_conn_events events) ==
          app_received_messages events)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev :: rest ->
    lemma_connection_log_trace_app_received rest;
    match ev with
    | ConnNetworkEvent _ -> ()
    | ConnLocalEvent local ->
      (match local with
       | LocalValidateCertificate _
       | LocalDeliverApplicationData _
       | LocalFail _ -> ()
       | _ -> ())

let lemma_connection_state_connection_log_view_consistent
  (st:connection_state)
  : Lemma
      (requires
        connection_state_app_log_consistent st /\
        connection_state_pending_application_consistent st)
      (ensures connection_state_connection_log_view_consistent st)
=
  let view = connection_log_view_of_state st in
  CL.lemma_raw_stream_view_shape
    #M.tls_message
    st.cs_wire_log.CL.raw_sent
    (sent_tls_messages st.cs_event_log);
  CL.lemma_raw_stream_view_shape
    #M.tls_message
    st.cs_wire_log.CL.raw_received
    (received_tls_messages st.cs_event_log);
  CL.lemma_parse_record_prefix_serializes st.cs_wire_log.CL.raw_sent;
  CL.lemma_parse_record_prefix_serializes st.cs_wire_log.CL.raw_received;
  lemma_connection_log_trace_sent_tls st.cs_event_log;
  lemma_connection_log_trace_received_tls st.cs_event_log;
  lemma_connection_log_trace_state_events st.cs_event_log;
  lemma_connection_log_trace_app_sent st.cs_event_log;
  lemma_connection_log_trace_app_received st.cs_event_log;
  assert (view.CL.sent_tls.CL.values == sent_tls_messages st.cs_event_log);
  assert (view.CL.received_tls.CL.values == received_tls_messages st.cs_event_log);
  assert (CL.app_log_of_host_trace view.CL.host_trace == {
    CL.app_sent = app_sent_messages st.cs_event_log;
    CL.app_received = app_received_messages st.cs_event_log;
  });
  assert (CL.app_log_of_host_trace view.CL.host_trace == view.CL.app_view);
  assert (CL.pending_app_source_consistent view)

let lemma_raw_records_exactly_one_parse_record
  (raw:B.bytes)
  (outer:T.content_type)
  : Lemma
      (requires raw_records_exactly raw outer 1)
      (ensures exists fragment.
        W.parse_record raw == Some (outer, fragment, B.length raw))
=
  let parsed = CL.parse_record_prefix raw in
  assert (CL.record_stream_serializes raw parsed);
  assert (Seq.equal parsed.CL.residual B.empty);
  assert (length parsed.CL.values == 1);
  assert (all_records_outer_type outer parsed.CL.values);
  assert (parsed.CL.consumed <= B.length raw);
  assert (Seq.equal parsed.CL.residual
                    (Seq.slice raw parsed.CL.consumed (B.length raw)));
  Seq.lemma_eq_elim parsed.CL.residual B.empty;
  Seq.lemma_eq_elim
    parsed.CL.residual
    (Seq.slice raw parsed.CL.consumed (B.length raw));
  Seq.lemma_len_slice raw parsed.CL.consumed (B.length raw);
  assert (B.length (Seq.slice raw parsed.CL.consumed (B.length raw)) == 0);
  assert (parsed.CL.consumed == B.length raw);
  match W.parse_record raw with
  | None ->
    assert (B.length raw + 1 > 0);
    assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
    assert (parsed.CL.values == []);
    assert False
  | Some (content_type, fragment, consumed) ->
    W.lemma_parse_record_serializes raw;
    if consumed == 0 || consumed > B.length raw then (
      assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
      assert (parsed.CL.values == []);
      assert False
    ) else (
      let rest = Seq.slice raw consumed (B.length raw) in
      let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
      let record =
        { M.record_outer_type = content_type;
          M.record_fragment = fragment } in
      assert (CL.parse_record_prefix raw ==
        {
          CL.values = record :: tail.CL.values;
          CL.consumed = consumed + tail.CL.consumed;
          CL.residual = tail.CL.residual;
        });
      assert (parsed.CL.values == record :: tail.CL.values);
      assert (length tail.CL.values == 0);
      assert (all_records_outer_type outer (record :: tail.CL.values));
      assert (content_type == outer);
      CL.lemma_parse_record_prefix_fuel_serializes (B.length raw) rest;
      assert (CL.record_stream_serializes rest tail);
      assert (tail.CL.consumed == B.length (CL.serialize_tls_records tail.CL.values));
      match tail.CL.values with
      | [] ->
        assert (CL.serialize_tls_records tail.CL.values == B.empty);
        assert (tail.CL.consumed == 0);
        assert (parsed.CL.consumed == consumed + tail.CL.consumed);
        assert (consumed == parsed.CL.consumed);
        assert (consumed == B.length raw);
        assert (W.parse_record raw == Some (outer, fragment, B.length raw));
        assert (exists fragment'. W.parse_record raw == Some (outer, fragment', B.length raw))
      | _ :: _ ->
        assert False
    )

let lemma_raw_records_exactly_nonempty_parse_record
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : Lemma
      (requires raw_records_exactly raw outer count /\ count > 0)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (outer, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw)
=
  let parsed = CL.parse_record_prefix raw in
  assert (length parsed.CL.values == count);
  assert (all_records_outer_type outer parsed.CL.values);
  match W.parse_record raw with
  | None ->
    assert (B.length raw + 1 > 0);
    assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
    assert (parsed.CL.values == []);
    assert False
  | Some (content_type, fragment, consumed) ->
    W.lemma_parse_record_serializes raw;
    if consumed == 0 || consumed > B.length raw then (
      assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
      assert (parsed.CL.values == []);
      assert False
    ) else (
      let rest = Seq.slice raw consumed (B.length raw) in
      let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
      let record =
        { M.record_outer_type = content_type;
          M.record_fragment = fragment } in
      assert (CL.parse_record_prefix raw ==
        {
          CL.values = record :: tail.CL.values;
          CL.consumed = consumed + tail.CL.consumed;
          CL.residual = tail.CL.residual;
        });
      assert (parsed.CL.values == record :: tail.CL.values);
      assert (all_records_outer_type outer (record :: tail.CL.values));
      assert (content_type == outer);
      assert (W.parse_record raw == Some (outer, fragment, consumed));
      assert (exists fragment'. exists (consumed':nat).
        W.parse_record raw == Some (outer, fragment', consumed') /\
        consumed' > 0 /\
        consumed' <= B.length raw)
    )

let lemma_raw_records_exactly_nonempty_decompose
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : Lemma
      (requires raw_records_exactly raw outer count /\ count > 0)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (outer, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw /\
        (let rest = Seq.slice raw consumed (B.length raw) in
         let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
         CL.record_stream_serializes rest tail /\
         Seq.equal tail.CL.residual B.empty /\
         length tail.CL.values == count - 1 /\
         all_records_outer_type outer tail.CL.values))
=
  let parsed = CL.parse_record_prefix raw in
  assert (CL.record_stream_serializes raw parsed);
  assert (Seq.equal parsed.CL.residual B.empty);
  assert (length parsed.CL.values == count);
  assert (all_records_outer_type outer parsed.CL.values);
  match W.parse_record raw with
  | None ->
    assert (B.length raw + 1 > 0);
    assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
    assert (parsed.CL.values == []);
    assert False
  | Some (content_type, fragment, consumed) ->
    W.lemma_parse_record_serializes raw;
    if consumed == 0 || consumed > B.length raw then (
      assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
      assert (parsed.CL.values == []);
      assert False
    ) else (
      let rest = Seq.slice raw consumed (B.length raw) in
      let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
      let record =
        { M.record_outer_type = content_type;
          M.record_fragment = fragment } in
      assert (CL.parse_record_prefix raw ==
        {
          CL.values = record :: tail.CL.values;
          CL.consumed = consumed + tail.CL.consumed;
          CL.residual = tail.CL.residual;
        });
      assert (parsed.CL.values == record :: tail.CL.values);
      assert (parsed.CL.residual == tail.CL.residual);
      assert (all_records_outer_type outer (record :: tail.CL.values));
      assert (content_type == outer);
      assert (all_records_outer_type outer tail.CL.values);
      CL.lemma_parse_record_prefix_fuel_serializes (B.length raw) rest;
      assert (CL.record_stream_serializes rest tail);
      assert (Seq.equal tail.CL.residual B.empty);
      assert (length tail.CL.values == count - 1);
      assert (W.parse_record raw == Some (outer, fragment, consumed));
      assert (exists fragment'. exists (consumed':nat).
        W.parse_record raw == Some (outer, fragment', consumed') /\
        consumed' > 0 /\
        consumed' <= B.length raw /\
        (let rest' = Seq.slice raw consumed' (B.length raw) in
         let tail' = CL.parse_record_prefix_fuel (B.length raw) rest' in
         CL.record_stream_serializes rest' tail' /\
         Seq.equal tail'.CL.residual B.empty /\
         length tail'.CL.values == count - 1 /\
         all_records_outer_type outer tail'.CL.values))
    )

let lemma_raw_records_exactly_nonempty_decompose_prefix
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : Lemma
      (requires raw_records_exactly raw outer count /\ count > 0)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (outer, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw /\
        raw_records_exactly
          (Seq.slice raw consumed (B.length raw))
          outer
          (count - 1))
=
  lemma_raw_records_exactly_nonempty_decompose raw outer count;
  match W.parse_record raw with
  | None ->
    assert False
  | Some (content_type, fragment, consumed) ->
    assert (W.parse_record raw == Some (content_type, fragment, consumed));
    assert (content_type == outer);
    assert (W.parse_record raw == Some (outer, fragment, consumed));
    assert (consumed > 0);
    assert (consumed <= B.length raw);
    let rest = Seq.slice raw consumed (B.length raw) in
    let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
    assert (CL.record_stream_serializes rest tail);
    assert (Seq.equal tail.CL.residual B.empty);
    assert (length tail.CL.values == count - 1);
    assert (all_records_outer_type outer tail.CL.values);
    Seq.lemma_len_slice raw consumed (B.length raw);
    assert (consumed + B.length rest == B.length raw);
    assert (B.length rest + 1 <= B.length raw);
    CL.lemma_parse_record_prefix_fuel_eq_parse_record_prefix (B.length raw) rest;
    assert (tail == CL.parse_record_prefix rest);
    let parsed_rest = CL.parse_record_prefix rest in
    assert (CL.record_stream_serializes rest parsed_rest);
    assert (Seq.equal parsed_rest.CL.residual B.empty);
    assert (length parsed_rest.CL.values == count - 1);
    assert (all_records_outer_type outer parsed_rest.CL.values);
    assert (raw_records_exactly rest outer (count - 1));
    assert (exists fragment'. exists (consumed':nat).
      W.parse_record raw == Some (outer, fragment', consumed') /\
      consumed' > 0 /\
      consumed' <= B.length raw /\
      raw_records_exactly
        (Seq.slice raw consumed' (B.length raw))
        outer
        (count - 1))

let rec lemma_raw_records_exactly_segmented
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : Lemma
      (requires raw_records_exactly raw outer count)
      (ensures raw_records_segmented raw outer count)
      (decreases count)
=
  if count == 0 then (
    let parsed = CL.parse_record_prefix raw in
    assert (CL.record_stream_serializes raw parsed);
    assert (Seq.equal parsed.CL.residual B.empty);
    assert (length parsed.CL.values == 0);
    match parsed.CL.values with
    | [] ->
      assert (CL.serialize_tls_records parsed.CL.values == B.empty);
      assert (parsed.CL.consumed == 0);
      assert (Seq.equal parsed.CL.residual
                        (Seq.slice raw parsed.CL.consumed (B.length raw)));
      Seq.lemma_eq_elim parsed.CL.residual B.empty;
      Seq.lemma_eq_elim
        parsed.CL.residual
        (Seq.slice raw parsed.CL.consumed (B.length raw));
      Seq.lemma_len_slice raw parsed.CL.consumed (B.length raw);
      assert (B.length (Seq.slice raw parsed.CL.consumed (B.length raw)) == 0);
      assert (parsed.CL.consumed == 0);
      assert (B.length raw == 0);
      assert (forall (i:nat{i < B.length raw}).
        Seq.index raw i == Seq.index B.empty i);
      Seq.lemma_eq_intro raw B.empty
    | _ :: _ ->
      assert False
  ) else (
    lemma_raw_records_exactly_nonempty_decompose_prefix raw outer count;
    match W.parse_record raw with
    | None -> assert False
    | Some (content_type, fragment, consumed) ->
      assert (content_type == outer);
      assert (W.parse_record raw == Some (outer, fragment, consumed));
      assert (consumed > 0);
      assert (consumed <= B.length raw);
      let rest = Seq.slice raw consumed (B.length raw) in
      assert (raw_records_exactly rest outer (count - 1));
      lemma_raw_records_exactly_segmented rest outer (count - 1);
      assert (raw_records_segmented rest outer (count - 1));
      assert (exists fragment'. exists (consumed':nat).
        W.parse_record raw == Some (outer, fragment', consumed') /\
        consumed' > 0 /\
        consumed' <= B.length raw /\
        raw_records_segmented
          (Seq.slice raw consumed' (B.length raw))
          outer
          (count - 1))
  )

let lemma_raw_records_exactly_single_serialized
  (outer:T.content_type)
  (fragment:B.bytes{B.length fragment <= 16640})
  : Lemma
      (raw_records_exactly (W.serialize_record outer fragment) outer 1)
=
  let raw = W.serialize_record outer fragment in
  W.lemma_parse_record_serialize_record outer fragment;
  CL.lemma_parse_record_prefix_serializes raw;
  assert (B.length raw > 0);
  assert (W.parse_record raw == Some (outer, fragment, B.length raw));
  let rest = Seq.slice raw (B.length raw) (B.length raw) in
  Seq.lemma_len_slice raw (B.length raw) (B.length raw);
  assert (B.length rest == 0);
  Seq.lemma_eq_intro rest B.empty;
  assert (rest == B.empty);
  assert (CL.parse_record_prefix_fuel (B.length raw) rest ==
    CL.raw_record_stream_view rest);
  assert (CL.raw_record_stream_view rest ==
    { CL.values = []; CL.consumed = 0; CL.residual = rest });
  assert (CL.record_stream_serializes raw (CL.parse_record_prefix raw));
  assert (CL.parse_record_prefix raw ==
    {
      CL.values = [{ M.record_outer_type = outer; M.record_fragment = fragment }];
      CL.consumed = B.length raw;
      CL.residual = B.empty;
    });
  assert (length (CL.parse_record_prefix raw).CL.values == 1);
  assert (all_records_outer_type outer (CL.parse_record_prefix raw).CL.values)

let lemma_raw_application_data_record_exactly
  (fragment:B.bytes{B.length fragment <= 16640})
  : Lemma
      (raw_records_exactly (W.serialize_record T.ApplicationData fragment) T.ApplicationData 1)
=
  lemma_raw_records_exactly_single_serialized T.ApplicationData fragment

let lemma_parse_record_full_raw_records_exactly
  (raw:B.bytes)
  (outer:T.content_type)
  (fragment:B.bytes)
  : Lemma
      (requires W.parse_record raw == Some (outer, fragment, B.length raw))
      (ensures raw_records_exactly raw outer 1 /\
               raw_records_segmented raw outer 1)
=
  W.lemma_parse_record_serializes raw;
  W.lemma_parse_record_fragment_bound raw;
  assert (B.length fragment <= 16640);
  let serialized = W.serialize_record outer fragment in
  assert (B.length raw == B.length serialized);
  assert (Seq.equal serialized (Seq.slice raw 0 (B.length raw)));
  Seq.lemma_len_slice raw 0 (B.length raw);
  assert (B.length (Seq.slice raw 0 (B.length raw)) == B.length raw);
  assert (forall (i:nat{i < B.length raw}).
    Seq.index raw i == Seq.index (Seq.slice raw 0 (B.length raw)) i);
  Seq.lemma_eq_intro raw (Seq.slice raw 0 (B.length raw));
  assert (Seq.equal raw serialized);
  lemma_raw_records_exactly_single_serialized outer fragment;
  Seq.lemma_eq_elim raw serialized;
  assert (raw_records_exactly raw outer 1);
  lemma_raw_records_exactly_segmented raw outer 1

let lemma_sent_single_protected_message_seal_intro
  (model:connection_model)
  (msg:M.tls_message)
  (raw:B.bytes)
  (aad:B.bytes)
  (ciphertext:B.bytes)
  : Lemma
      (requires
        W.parse_record raw == Some (T.ApplicationData, ciphertext, B.length raw) /\
        Seq.equal aad (record_header_aad raw) /\
        R.seal
          model.model_record.record_write
          aad
          {
            R.content_type = T.ApplicationData;
            R.fragment = sent_tls_inner_plaintext_fragment msg;
          } ==
          Some (ciphertext, R.next_seq model.model_record.record_write))
      (ensures sent_single_protected_message_seal model msg raw)
=
  Seq.lemma_eq_elim aad (record_header_aad raw);
  assert (exists ciphertext'.
    W.parse_record raw == Some (T.ApplicationData, ciphertext', B.length raw) /\
    R.seal
      model.model_record.record_write
      (record_header_aad raw)
      {
        R.content_type = T.ApplicationData;
        R.fragment = sent_tls_inner_plaintext_fragment msg;
      } ==
      Some (ciphertext', R.next_seq model.model_record.record_write))

let lemma_protected_record_count_positive
  (dir:direction)
  (msg:M.tls_message)
  : Lemma (protected_record_count dir msg > 0)
=
  match dir, msg with
  | CL.Sent, M.TlsApplicationData bytes ->
    S.lemma_application_data_record_count_len_positive (B.length bytes)
  | _, _ -> ()

let lemma_sent_event_seal_projection_intro
  (model:connection_model)
  (msg:M.tls_message)
  (raw:B.bytes)
  (aad:B.bytes)
  (plaintext:B.bytes)
  (ciphertext:B.bytes)
  : Lemma
      (requires
        network_message_is_cleartext CL.Sent msg == false /\
        protected_record_count CL.Sent msg == 1 /\
        W.parse_record raw == Some (T.ApplicationData, ciphertext, B.length raw) /\
        Seq.equal aad (record_header_aad raw) /\
        Seq.equal plaintext (sent_tls_inner_plaintext_fragment msg) /\
        R.seal
          model.model_record.record_write
          aad
          {
            R.content_type = T.ApplicationData;
            R.fragment = plaintext;
          } ==
          Some (ciphertext, R.next_seq model.model_record.record_write))
      (ensures sent_event_seal_projection
        model
        (ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = msg;
        })
        raw)
=
  Seq.lemma_eq_elim plaintext (sent_tls_inner_plaintext_fragment msg);
  lemma_sent_single_protected_message_seal_intro model msg raw aad ciphertext

let lemma_network_message_raw_delta_legal_protected_single_parse_record
  (model:connection_model)
  (msg:directed_message M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        network_message_raw_delta_legal model msg raw /\
        network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false /\
        protected_record_count msg.CL.message_direction msg.CL.message_value == 1)
      (ensures exists fragment.
        W.parse_record raw == Some (T.ApplicationData, fragment, B.length raw))
=
  assert (raw_records_exactly raw T.ApplicationData 1);
  lemma_raw_records_exactly_one_parse_record raw T.ApplicationData

let lemma_network_message_raw_delta_legal_protected_parse_prefix
  (model:connection_model)
  (msg:directed_message M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        network_message_raw_delta_legal model msg raw /\
        network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (T.ApplicationData, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw)
=
  lemma_protected_record_count_positive msg.CL.message_direction msg.CL.message_value;
  lemma_raw_records_exactly_nonempty_parse_record
    raw
    T.ApplicationData
    (protected_record_count msg.CL.message_direction msg.CL.message_value)

let lemma_network_message_raw_delta_legal_protected_decompose
  (model:connection_model)
  (msg:directed_message M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        network_message_raw_delta_legal model msg raw /\
        network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (T.ApplicationData, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw /\
        (let rest = Seq.slice raw consumed (B.length raw) in
         let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
         CL.record_stream_serializes rest tail /\
         Seq.equal tail.CL.residual B.empty /\
         length tail.CL.values ==
           protected_record_count msg.CL.message_direction msg.CL.message_value - 1 /\
         all_records_outer_type T.ApplicationData tail.CL.values))
=
  lemma_protected_record_count_positive msg.CL.message_direction msg.CL.message_value;
  lemma_raw_records_exactly_nonempty_decompose
    raw
    T.ApplicationData
    (protected_record_count msg.CL.message_direction msg.CL.message_value)

let lemma_network_message_raw_delta_legal_protected_decompose_prefix
  (model:connection_model)
  (msg:directed_message M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        network_message_raw_delta_legal model msg raw /\
        network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (T.ApplicationData, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw /\
        raw_records_exactly
          (Seq.slice raw consumed (B.length raw))
          T.ApplicationData
          (protected_record_count msg.CL.message_direction msg.CL.message_value - 1))
=
  lemma_protected_record_count_positive msg.CL.message_direction msg.CL.message_value;
  lemma_raw_records_exactly_nonempty_decompose_prefix
    raw
    T.ApplicationData
    (protected_record_count msg.CL.message_direction msg.CL.message_value)

let lemma_network_message_raw_delta_legal_protected_segmented
  (model:connection_model)
  (msg:directed_message M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        network_message_raw_delta_legal model msg raw /\
        network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false)
      (ensures raw_records_segmented
        raw
        T.ApplicationData
        (protected_record_count msg.CL.message_direction msg.CL.message_value))
=
  lemma_raw_records_exactly_segmented
    raw
    T.ApplicationData
    (protected_record_count msg.CL.message_direction msg.CL.message_value)

let lemma_event_raw_delta_legal_protected_single_parse_record
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires event_raw_delta_legal model ev raw_sent raw_received)
      (ensures event_protected_single_raw_parse_success ev raw_sent raw_received)
=
  match ev with
  | ConnLocalEvent _ -> ()
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then ()
    else if protected_record_count msg.CL.message_direction msg.CL.message_value == 1
    then
      match msg.CL.message_direction with
      | CL.Sent ->
        lemma_network_message_raw_delta_legal_protected_single_parse_record model msg raw_sent
      | CL.Received ->
        lemma_network_message_raw_delta_legal_protected_single_parse_record model msg raw_received;
        assert (exists fragment.
          W.parse_record raw_received ==
            Some (T.ApplicationData, fragment, B.length raw_received));
        W.lemma_parse_record_implies_parse_record_wire raw_received
    else ()

let lemma_event_raw_delta_legal_protected_parse_prefix
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires event_raw_delta_legal model ev raw_sent raw_received)
      (ensures event_protected_raw_parse_prefix_success ev raw_sent raw_received)
=
  match ev with
  | ConnLocalEvent _ -> ()
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then ()
    else
      match msg.CL.message_direction with
      | CL.Sent ->
        lemma_network_message_raw_delta_legal_protected_parse_prefix model msg raw_sent
      | CL.Received ->
        lemma_network_message_raw_delta_legal_protected_parse_prefix model msg raw_received;
        assert (exists fragment. exists (consumed:nat).
          W.parse_record raw_received ==
            Some (T.ApplicationData, fragment, consumed) /\
          consumed > 0 /\
          consumed <= B.length raw_received);
        W.lemma_parse_record_implies_parse_record_wire raw_received

let lemma_event_raw_delta_legal_protected_decompose_prefix
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires event_raw_delta_legal model ev raw_sent raw_received)
      (ensures event_protected_raw_decompose_prefix_success ev raw_sent raw_received)
=
  match ev with
  | ConnLocalEvent _ -> ()
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then ()
    else
      match msg.CL.message_direction with
      | CL.Sent ->
        lemma_network_message_raw_delta_legal_protected_decompose_prefix model msg raw_sent
      | CL.Received ->
        lemma_network_message_raw_delta_legal_protected_decompose_prefix model msg raw_received;
        assert (exists fragment. exists (consumed:nat).
          W.parse_record raw_received ==
            Some (T.ApplicationData, fragment, consumed) /\
          consumed > 0 /\
          consumed <= B.length raw_received /\
          raw_records_exactly
            (Seq.slice raw_received consumed (B.length raw_received))
            T.ApplicationData
            (protected_record_count msg.CL.message_direction msg.CL.message_value - 1));
        W.lemma_parse_record_implies_parse_record_wire raw_received

let lemma_event_raw_delta_legal_protected_segmented
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires event_raw_delta_legal model ev raw_sent raw_received)
      (ensures event_protected_raw_segmented_success ev raw_sent raw_received)
=
  match ev with
  | ConnLocalEvent _ -> ()
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then ()
    else
      match msg.CL.message_direction with
      | CL.Sent ->
        lemma_network_message_raw_delta_legal_protected_segmented model msg raw_sent
      | CL.Received ->
        lemma_network_message_raw_delta_legal_protected_segmented model msg raw_received

let lemma_conn_events_raw_replay_cons
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (model1:connection_model)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (tail_sent:B.bytes)
  (tail_received:B.bytes)
  : Lemma
      (requires
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        conn_events_raw_replay model1 rest tail_sent tail_received final_model)
      (ensures
        conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model)
=
  FStar.Classical.exists_intro
    (fun tail_received' ->
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_raw_replay model1 rest tail_sent tail_received' final_model)
    tail_received;
  FStar.Classical.exists_intro
    (fun tail_sent' ->
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received tail_received') /\
        conn_events_raw_replay model1 rest tail_sent' tail_received' final_model)
    tail_sent;
  FStar.Classical.exists_intro
    (fun delta_received' ->
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received' /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_raw_replay model1 rest tail_sent' tail_received' final_model)
    delta_received;
  FStar.Classical.exists_intro
    (fun delta_sent' ->
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_raw_replay model1 rest tail_sent' tail_received' final_model)
    delta_sent;
  FStar.Classical.exists_intro
    (fun model1' ->
      exists (delta_sent':B.bytes).
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_raw_replay model1' rest tail_sent' tail_received' final_model)
    model1;
  assert_norm (
    conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model ==
    (exists (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_raw_replay model1' rest tail_sent' tail_received' final_model));
  assert (conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model)

let rec lemma_conn_events_raw_replay_snoc
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (model1:connection_model)
  (ev:conn_event)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (model2:connection_model)
  : Lemma
      (requires
        conn_events_raw_replay model events raw_sent raw_received model1 /\
        legal_event model1 ev /\
        step_model model1 ev == Some model2 /\
        event_raw_delta_legal model1 ev delta_sent delta_received)
      (ensures
        conn_events_raw_replay
          model
          (events @ [ev])
          (B.append raw_sent delta_sent)
          (B.append raw_received delta_received)
          model2)
      (decreases events)
=
  match events with
  | [] ->
    Seq.lemma_eq_elim raw_sent B.empty;
    Seq.lemma_eq_elim raw_received B.empty;
    CL.lemma_append_empty_left delta_sent;
    CL.lemma_append_empty_left delta_received;
    CL.lemma_append_empty_right delta_sent;
    CL.lemma_append_empty_right delta_received;
    assert (model1 == model);
    assert (legal_event model ev);
    assert (step_model model ev == Some model2);
    assert (event_raw_delta_legal model ev delta_sent delta_received);
    assert (Seq.equal
      (B.append raw_sent delta_sent)
      (B.append delta_sent B.empty));
    assert (Seq.equal
      (B.append raw_received delta_received)
      (B.append delta_received B.empty));
    assert (conn_events_raw_replay model2 [] B.empty B.empty model2);
    lemma_conn_events_raw_replay_cons
      model
      ev
      []
      (B.append raw_sent delta_sent)
      (B.append raw_received delta_received)
      model2
      model2
      delta_sent
      delta_received
      B.empty
      B.empty
  | ev0 :: rest ->
    assert_norm (
      conn_events_raw_replay model (ev0 :: rest) raw_sent raw_received model1 ==
      (exists (model0':connection_model)
              (delta_sent0:B.bytes)
              (delta_received0:B.bytes)
              (tail_sent:B.bytes)
              (tail_received:B.bytes).
         legal_event model ev0 /\
         step_model model ev0 == Some model0' /\
         event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
         Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
         Seq.equal raw_received (B.append delta_received0 tail_received) /\
         conn_events_raw_replay model0' rest tail_sent tail_received model1));
    assert (exists (model0':connection_model)
                   (delta_sent0:B.bytes)
                   (delta_received0:B.bytes)
                   (tail_sent:B.bytes)
                   (tail_received:B.bytes).
       legal_event model ev0 /\
       step_model model ev0 == Some model0' /\
       event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
       Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
       Seq.equal raw_received (B.append delta_received0 tail_received) /\
       conn_events_raw_replay model0' rest tail_sent tail_received model1);
    let model0'_w =
      ID.indefinite_description_ghost
        connection_model
        (fun model0' -> exists delta_sent0 delta_received0 tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_raw_replay model0' rest tail_sent tail_received model1) in
    let model0' : connection_model = model0'_w in
    assert (exists delta_sent0' delta_received0' tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0' delta_received0' /\
      Seq.equal raw_sent (B.append delta_sent0' tail_sent') /\
      Seq.equal raw_received (B.append delta_received0' tail_received') /\
      conn_events_raw_replay model0' rest tail_sent' tail_received' model1);
    let delta_sent0_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_sent0 -> exists delta_received0 tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_raw_replay model0' rest tail_sent tail_received model1) in
    let delta_sent0 : B.bytes = delta_sent0_w in
    assert (exists delta_received0' tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0' /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent') /\
      Seq.equal raw_received (B.append delta_received0' tail_received') /\
      conn_events_raw_replay model0' rest tail_sent' tail_received' model1);
    let delta_received0_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_received0 -> exists tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_raw_replay model0' rest tail_sent tail_received model1) in
    let delta_received0 : B.bytes = delta_received0_w in
    assert (exists tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent') /\
      Seq.equal raw_received (B.append delta_received0 tail_received') /\
      conn_events_raw_replay model0' rest tail_sent' tail_received' model1);
    let tail_sent_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_sent -> exists tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_raw_replay model0' rest tail_sent tail_received model1) in
    let tail_sent : B.bytes = tail_sent_w in
    assert (exists tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
      Seq.equal raw_received (B.append delta_received0 tail_received') /\
      conn_events_raw_replay model0' rest tail_sent tail_received' model1);
    let tail_received_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_received ->
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_raw_replay model0' rest tail_sent tail_received model1) in
    let tail_received : B.bytes = tail_received_w in
    assert (legal_event model ev0);
    assert (step_model model ev0 == Some model0');
    assert (event_raw_delta_legal model ev0 delta_sent0 delta_received0);
    assert (Seq.equal raw_sent (B.append delta_sent0 tail_sent));
    assert (Seq.equal raw_received (B.append delta_received0 tail_received));
    assert (conn_events_raw_replay model0' rest tail_sent tail_received model1);
    lemma_conn_events_raw_replay_snoc
      model0'
      rest
      tail_sent
      tail_received
      model1
      ev
      delta_sent
      delta_received
      model2;
    Seq.lemma_eq_elim raw_sent (B.append delta_sent0 tail_sent);
    Seq.lemma_eq_elim raw_received (B.append delta_received0 tail_received);
    Seq.append_assoc delta_sent0 tail_sent delta_sent;
    Seq.append_assoc delta_received0 tail_received delta_received;
    assert (Seq.equal
      (B.append (B.append delta_sent0 tail_sent) delta_sent)
      (B.append delta_sent0 (B.append tail_sent delta_sent)));
    assert (Seq.equal
      (B.append (B.append delta_received0 tail_received) delta_received)
      (B.append delta_received0 (B.append tail_received delta_received)));
    assert (conn_events_raw_replay
      model0'
      (rest @ [ev])
      (B.append tail_sent delta_sent)
      (B.append tail_received delta_received)
      model2);
    assert (events @ [ev] == ev0 :: (rest @ [ev]));
    assert (Seq.equal
      (B.append raw_sent delta_sent)
      (B.append delta_sent0 (B.append tail_sent delta_sent)));
    assert (Seq.equal
      (B.append raw_received delta_received)
      (B.append delta_received0 (B.append tail_received delta_received)));
    lemma_conn_events_raw_replay_cons
      model
      ev0
      (rest @ [ev])
      (B.append raw_sent delta_sent)
      (B.append raw_received delta_received)
      model2
      model0'
      delta_sent0
      delta_received0
      (B.append tail_sent delta_sent)
      (B.append tail_received delta_received)

let lemma_conn_events_protected_raw_segmented_replay_cons
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (model1:connection_model)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (tail_sent:B.bytes)
  (tail_received:B.bytes)
  : Lemma
      (requires
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        event_protected_raw_segmented_success ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        conn_events_protected_raw_segmented_replay
          model1
          rest
          tail_sent
          tail_received
          final_model)
      (ensures
        conn_events_protected_raw_segmented_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model)
=
  FStar.Classical.exists_intro
    (fun tail_received' ->
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      event_protected_raw_segmented_success ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_protected_raw_segmented_replay
        model1
        rest
        tail_sent
        tail_received'
        final_model)
    tail_received;
  FStar.Classical.exists_intro
    (fun tail_sent' ->
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        event_protected_raw_segmented_success ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received tail_received') /\
        conn_events_protected_raw_segmented_replay
          model1
          rest
          tail_sent'
          tail_received'
          final_model)
    tail_sent;
  FStar.Classical.exists_intro
    (fun delta_received' ->
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received' /\
        event_protected_raw_segmented_success ev delta_sent delta_received' /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_protected_raw_segmented_replay
          model1
          rest
          tail_sent'
          tail_received'
          final_model)
    delta_received;
  FStar.Classical.exists_intro
    (fun delta_sent' ->
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        event_protected_raw_segmented_success ev delta_sent' delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_protected_raw_segmented_replay
          model1
          rest
          tail_sent'
          tail_received'
          final_model)
    delta_sent;
  FStar.Classical.exists_intro
    (fun model1' ->
      exists (delta_sent':B.bytes).
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        event_protected_raw_segmented_success ev delta_sent' delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_protected_raw_segmented_replay
          model1'
          rest
          tail_sent'
          tail_received'
          final_model)
    model1;
  assert_norm (
    conn_events_protected_raw_segmented_replay
      model
      (ev :: rest)
      raw_sent
      raw_received
      final_model ==
    (exists (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1' /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      event_protected_raw_segmented_success ev delta_sent' delta_received' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_protected_raw_segmented_replay
        model1'
        rest
        tail_sent'
        tail_received'
        final_model));
  assert (conn_events_protected_raw_segmented_replay
    model
    (ev :: rest)
    raw_sent
    raw_received
    final_model)

let rec lemma_conn_events_raw_replay_protected_segmented
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_raw_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (ensures
        conn_events_protected_raw_segmented_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (decreases events)
=
  match events with
  | [] ->
    ()
  | ev :: rest ->
    assert_norm (
      conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model ==
      (exists (model1':connection_model)
              (delta_sent':B.bytes)
              (delta_received':B.bytes)
              (tail_sent':B.bytes)
              (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_raw_replay model1' rest tail_sent' tail_received' final_model));
    assert (exists (model1':connection_model)
                   (delta_sent':B.bytes)
                   (delta_received':B.bytes)
                   (tail_sent':B.bytes)
                   (tail_received':B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1' /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_raw_replay model1' rest tail_sent' tail_received' final_model);
    let model1_w =
      ID.indefinite_description_ghost
        connection_model
        (fun model1 -> exists delta_sent delta_received tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_raw_replay model1 rest tail_sent tail_received final_model) in
    let model1 : connection_model = model1_w in
    assert (exists delta_sent' delta_received' tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_raw_replay model1 rest tail_sent' tail_received' final_model);
    let delta_sent_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_sent -> exists delta_received tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_raw_replay model1 rest tail_sent tail_received final_model) in
    let delta_sent : B.bytes = delta_sent_w in
    assert (exists delta_received' tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received' /\
      Seq.equal raw_sent (B.append delta_sent tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_raw_replay model1 rest tail_sent' tail_received' final_model);
    let delta_received_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_received -> exists tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_raw_replay model1 rest tail_sent tail_received final_model) in
    let delta_received : B.bytes = delta_received_w in
    assert (exists tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent') /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_raw_replay model1 rest tail_sent' tail_received' final_model);
    let tail_sent_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_sent -> exists tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_raw_replay model1 rest tail_sent tail_received final_model) in
    let tail_sent : B.bytes = tail_sent_w in
    assert (exists tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_raw_replay model1 rest tail_sent tail_received' final_model);
    let tail_received_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_received ->
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_raw_replay model1 rest tail_sent tail_received final_model) in
    let tail_received : B.bytes = tail_received_w in
    assert (legal_event model ev);
    assert (step_model model ev == Some model1);
    assert (event_raw_delta_legal model ev delta_sent delta_received);
    assert (Seq.equal raw_sent (B.append delta_sent tail_sent));
    assert (Seq.equal raw_received (B.append delta_received tail_received));
    assert (conn_events_raw_replay model1 rest tail_sent tail_received final_model);
    lemma_event_raw_delta_legal_protected_segmented
      model
      ev
      delta_sent
      delta_received;
    lemma_conn_events_raw_replay_protected_segmented
      model1
      rest
      tail_sent
      tail_received
      final_model;
    lemma_conn_events_protected_raw_segmented_replay_cons
      model
      ev
      rest
      raw_sent
      raw_received
      final_model
      model1
      delta_sent
      delta_received
      tail_sent
      tail_received

let lemma_connection_state_protected_raw_segmented_replay
  (st:connection_state)
  : Lemma
      (requires connection_state_raw_event_replay_consistent st)
      (ensures connection_state_protected_raw_segmented_replay_consistent st)
=
  lemma_conn_events_raw_replay_protected_segmented
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model

let lemma_conn_events_sent_seal_replay_cons
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (model1:connection_model)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (tail_sent:B.bytes)
  (tail_received:B.bytes)
  : Lemma
      (requires
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        sent_event_nonempty_seal_projection model ev delta_sent /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        conn_events_sent_seal_replay model1 rest tail_sent tail_received final_model)
      (ensures
        conn_events_sent_seal_replay model (ev :: rest) raw_sent raw_received final_model)
=
  FStar.Classical.exists_intro
    (fun tail_received' ->
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_sent_seal_replay model1 rest tail_sent tail_received' final_model)
    tail_received;
  FStar.Classical.exists_intro
    (fun tail_sent' ->
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        sent_event_nonempty_seal_projection model ev delta_sent /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received tail_received') /\
        conn_events_sent_seal_replay model1 rest tail_sent' tail_received' final_model)
    tail_sent;
  FStar.Classical.exists_intro
    (fun delta_received' ->
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received' /\
        sent_event_nonempty_seal_projection model ev delta_sent /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_sent_seal_replay model1 rest tail_sent' tail_received' final_model)
    delta_received;
  FStar.Classical.exists_intro
    (fun delta_sent' ->
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        sent_event_nonempty_seal_projection model ev delta_sent' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_sent_seal_replay model1 rest tail_sent' tail_received' final_model)
    delta_sent;
  FStar.Classical.exists_intro
    (fun model1' ->
      exists (delta_sent':B.bytes).
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        sent_event_nonempty_seal_projection model ev delta_sent' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_sent_seal_replay model1' rest tail_sent' tail_received' final_model)
    model1;
  assert_norm (
    conn_events_sent_seal_replay model (ev :: rest) raw_sent raw_received final_model ==
    (exists (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       sent_event_nonempty_seal_projection model ev delta_sent' /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_sent_seal_replay model1' rest tail_sent' tail_received' final_model));
  assert (conn_events_sent_seal_replay model (ev :: rest) raw_sent raw_received final_model)

let lemma_conn_events_sent_seal_key_schedule_replay_cons
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (model1:connection_model)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (tail_sent:B.bytes)
  (tail_received:B.bytes)
  : Lemma
      (requires
       legal_event model ev /\
       step_model model ev == Some model1 /\
       event_raw_delta_legal model ev delta_sent delta_received /\
       sent_event_nonempty_seal_projection model ev delta_sent /\
       record_write_key_schedule_projection model /\
       Seq.equal raw_sent (B.append delta_sent tail_sent) /\
       Seq.equal raw_received (B.append delta_received tail_received) /\
       conn_events_sent_seal_key_schedule_replay
         model1
         rest
         tail_sent
         tail_received
         final_model)
      (ensures
       conn_events_sent_seal_key_schedule_replay
         model
         (ev :: rest)
         raw_sent
         raw_received
         final_model)
=
  FStar.Classical.exists_intro
    (fun tail_received' ->
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      record_write_key_schedule_projection model /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_sent_seal_key_schedule_replay
       model1
       rest
       tail_sent
       tail_received'
       final_model)
    tail_received;
  FStar.Classical.exists_intro
    (fun tail_sent' ->
      exists (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1 /\
       event_raw_delta_legal model ev delta_sent delta_received /\
       sent_event_nonempty_seal_projection model ev delta_sent /\
       record_write_key_schedule_projection model /\
       Seq.equal raw_sent (B.append delta_sent tail_sent') /\
       Seq.equal raw_received (B.append delta_received tail_received') /\
       conn_events_sent_seal_key_schedule_replay
         model1
         rest
         tail_sent'
         tail_received'
         final_model)
    tail_sent;
  FStar.Classical.exists_intro
    (fun delta_received' ->
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1 /\
       event_raw_delta_legal model ev delta_sent delta_received' /\
       sent_event_nonempty_seal_projection model ev delta_sent /\
       record_write_key_schedule_projection model /\
       Seq.equal raw_sent (B.append delta_sent tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_sent_seal_key_schedule_replay
         model1
         rest
         tail_sent'
         tail_received'
         final_model)
    delta_received;
  FStar.Classical.exists_intro
    (fun delta_sent' ->
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1 /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       sent_event_nonempty_seal_projection model ev delta_sent' /\
       record_write_key_schedule_projection model /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_sent_seal_key_schedule_replay
         model1
         rest
         tail_sent'
         tail_received'
         final_model)
    delta_sent;
  FStar.Classical.exists_intro
    (fun model1' ->
      exists (delta_sent':B.bytes).
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       sent_event_nonempty_seal_projection model ev delta_sent' /\
       record_write_key_schedule_projection model /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_sent_seal_key_schedule_replay
         model1'
         rest
         tail_sent'
         tail_received'
         final_model)
    model1;
  assert_norm (
    conn_events_sent_seal_key_schedule_replay
      model
      (ev :: rest)
      raw_sent
      raw_received
      final_model ==
    (exists (model1':connection_model)
           (delta_sent':B.bytes)
           (delta_received':B.bytes)
           (tail_sent':B.bytes)
           (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       sent_event_nonempty_seal_projection model ev delta_sent' /\
       record_write_key_schedule_projection model /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_sent_seal_key_schedule_replay
        model1'
        rest
        tail_sent'
        tail_received'
        final_model));
  assert (conn_events_sent_seal_key_schedule_replay
    model
    (ev :: rest)
    raw_sent
    raw_received
    final_model)

let rec lemma_conn_events_sent_seal_replay_strengthen
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
       conn_events_sent_seal_replay
         model
         events
         raw_sent
         raw_received
         final_model /\
       model.model_config.config_role == ClientEndpoint /\
       model_record_keys_consistent model)
      (ensures
       conn_events_sent_seal_key_schedule_replay
         model
         events
         raw_sent
         raw_received
         final_model)
      (decreases events)
=
  match events with
  | [] ->
    ()
  | ev :: rest ->
    assert_norm (
      conn_events_sent_seal_replay
       model
       (ev :: rest)
       raw_sent
       raw_received
       final_model ==
      (exists (model1':connection_model)
             (delta_sent':B.bytes)
             (delta_received':B.bytes)
             (tail_sent':B.bytes)
             (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        sent_event_nonempty_seal_projection model ev delta_sent' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_sent_seal_replay
          model1'
          rest
          tail_sent'
          tail_received'
          final_model));
    assert (exists (model1':connection_model)
                  (delta_sent':B.bytes)
                  (delta_received':B.bytes)
                  (tail_sent':B.bytes)
                  (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       sent_event_nonempty_seal_projection model ev delta_sent' /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_sent_seal_replay
        model1'
        rest
        tail_sent'
        tail_received'
        final_model);
    let model1_w =
      ID.indefinite_description_ghost
       connection_model
       (fun model1 -> exists delta_sent delta_received tail_sent tail_received.
         legal_event model ev /\
         step_model model ev == Some model1 /\
         event_raw_delta_legal model ev delta_sent delta_received /\
         sent_event_nonempty_seal_projection model ev delta_sent /\
         Seq.equal raw_sent (B.append delta_sent tail_sent) /\
         Seq.equal raw_received (B.append delta_received tail_received) /\
         conn_events_sent_seal_replay
           model1
           rest
           tail_sent
           tail_received
           final_model) in
    let model1 : connection_model = model1_w in
    assert (exists delta_sent' delta_received' tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      sent_event_nonempty_seal_projection model ev delta_sent' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_sent_seal_replay
       model1
       rest
       tail_sent'
       tail_received'
       final_model);
    let delta_sent_w =
      ID.indefinite_description_ghost
       B.bytes
       (fun delta_sent -> exists delta_received tail_sent tail_received.
         legal_event model ev /\
         step_model model ev == Some model1 /\
         event_raw_delta_legal model ev delta_sent delta_received /\
         sent_event_nonempty_seal_projection model ev delta_sent /\
         Seq.equal raw_sent (B.append delta_sent tail_sent) /\
         Seq.equal raw_received (B.append delta_received tail_received) /\
         conn_events_sent_seal_replay
           model1
           rest
           tail_sent
           tail_received
           final_model) in
    let delta_sent : B.bytes = delta_sent_w in
    assert (exists delta_received' tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received' /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      Seq.equal raw_sent (B.append delta_sent tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_sent_seal_replay
       model1
       rest
       tail_sent'
       tail_received'
       final_model);
    let delta_received_w =
      ID.indefinite_description_ghost
       B.bytes
       (fun delta_received -> exists tail_sent tail_received.
         legal_event model ev /\
         step_model model ev == Some model1 /\
         event_raw_delta_legal model ev delta_sent delta_received /\
         sent_event_nonempty_seal_projection model ev delta_sent /\
         Seq.equal raw_sent (B.append delta_sent tail_sent) /\
         Seq.equal raw_received (B.append delta_received tail_received) /\
         conn_events_sent_seal_replay
           model1
           rest
           tail_sent
           tail_received
           final_model) in
    let delta_received : B.bytes = delta_received_w in
    assert (exists tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      Seq.equal raw_sent (B.append delta_sent tail_sent') /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_sent_seal_replay
       model1
       rest
       tail_sent'
       tail_received'
       final_model);
    let tail_sent_w =
      ID.indefinite_description_ghost
       B.bytes
       (fun tail_sent -> exists tail_received.
         legal_event model ev /\
         step_model model ev == Some model1 /\
         event_raw_delta_legal model ev delta_sent delta_received /\
         sent_event_nonempty_seal_projection model ev delta_sent /\
         Seq.equal raw_sent (B.append delta_sent tail_sent) /\
         Seq.equal raw_received (B.append delta_received tail_received) /\
         conn_events_sent_seal_replay
           model1
           rest
           tail_sent
           tail_received
           final_model) in
    let tail_sent : B.bytes = tail_sent_w in
    assert (exists tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_sent_seal_replay
       model1
       rest
       tail_sent
       tail_received'
       final_model);
    let tail_received_w =
      ID.indefinite_description_ghost
       B.bytes
       (fun tail_received ->
         legal_event model ev /\
         step_model model ev == Some model1 /\
         event_raw_delta_legal model ev delta_sent delta_received /\
         sent_event_nonempty_seal_projection model ev delta_sent /\
         Seq.equal raw_sent (B.append delta_sent tail_sent) /\
         Seq.equal raw_received (B.append delta_received tail_received) /\
         conn_events_sent_seal_replay
           model1
           rest
           tail_sent
           tail_received
           final_model) in
    let tail_received : B.bytes = tail_received_w in
    assert (legal_event model ev);
    assert (step_model model ev == Some model1);
    assert (event_raw_delta_legal model ev delta_sent delta_received);
    assert (sent_event_nonempty_seal_projection model ev delta_sent);
    assert (Seq.equal raw_sent (B.append delta_sent tail_sent));
    assert (Seq.equal raw_received (B.append delta_received tail_received));
    assert (conn_events_sent_seal_replay
      model1
      rest
      tail_sent
      tail_received
      final_model);
    assert (model.model_config.config_role == ClientEndpoint);
    lemma_model_record_keys_consistent_record_write_key_schedule_projection model;
    lemma_step_model_record_keys_consistent model ev model1;
    assert (model_record_keys_consistent model1);
    assert_norm (model_record_keys_consistent model1 ==
      (model1.model_config.config_role == ClientEndpoint /\
       model_record_keys_consistent_for_role ClientEndpoint model1));
    assert (model1.model_config.config_role == ClientEndpoint);
    lemma_conn_events_sent_seal_replay_strengthen
      model1
      rest
      tail_sent
      tail_received
      final_model;
    lemma_conn_events_sent_seal_key_schedule_replay_cons
      model
      ev
      rest
      raw_sent
      raw_received
      final_model
      model1
      delta_sent
      delta_received
      tail_sent
      tail_received

let rec lemma_conn_events_sent_seal_replay_snoc
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (model1:connection_model)
  (ev:conn_event)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (model2:connection_model)
  : Lemma
      (requires
        conn_events_sent_seal_replay model events raw_sent raw_received model1 /\
        legal_event model1 ev /\
        step_model model1 ev == Some model2 /\
        event_raw_delta_legal model1 ev delta_sent delta_received /\
        sent_event_nonempty_seal_projection model1 ev delta_sent)
      (ensures
        conn_events_sent_seal_replay
          model
          (events @ [ev])
          (B.append raw_sent delta_sent)
          (B.append raw_received delta_received)
          model2)
      (decreases events)
=
  match events with
  | [] ->
    Seq.lemma_eq_elim raw_sent B.empty;
    Seq.lemma_eq_elim raw_received B.empty;
    CL.lemma_append_empty_left delta_sent;
    CL.lemma_append_empty_left delta_received;
    CL.lemma_append_empty_right delta_sent;
    CL.lemma_append_empty_right delta_received;
    assert (model1 == model);
    assert (legal_event model ev);
    assert (step_model model ev == Some model2);
    assert (event_raw_delta_legal model ev delta_sent delta_received);
    assert (sent_event_nonempty_seal_projection model ev delta_sent);
    assert (Seq.equal
      (B.append raw_sent delta_sent)
      (B.append delta_sent B.empty));
    assert (Seq.equal
      (B.append raw_received delta_received)
      (B.append delta_received B.empty));
    assert (conn_events_sent_seal_replay model2 [] B.empty B.empty model2);
    lemma_conn_events_sent_seal_replay_cons
      model
      ev
      []
      (B.append raw_sent delta_sent)
      (B.append raw_received delta_received)
      model2
      model2
      delta_sent
      delta_received
      B.empty
      B.empty
  | ev0 :: rest ->
    assert_norm (
      conn_events_sent_seal_replay model (ev0 :: rest) raw_sent raw_received model1 ==
      (exists (model0':connection_model)
              (delta_sent0:B.bytes)
              (delta_received0:B.bytes)
              (tail_sent:B.bytes)
              (tail_received:B.bytes).
         legal_event model ev0 /\
         step_model model ev0 == Some model0' /\
         event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
         sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
         Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
         Seq.equal raw_received (B.append delta_received0 tail_received) /\
         conn_events_sent_seal_replay model0' rest tail_sent tail_received model1));
    assert (exists (model0':connection_model)
                   (delta_sent0:B.bytes)
                   (delta_received0:B.bytes)
                   (tail_sent:B.bytes)
                   (tail_received:B.bytes).
       legal_event model ev0 /\
       step_model model ev0 == Some model0' /\
       event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
       sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
       Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
       Seq.equal raw_received (B.append delta_received0 tail_received) /\
       conn_events_sent_seal_replay model0' rest tail_sent tail_received model1);
    let model0'_w =
      ID.indefinite_description_ghost
        connection_model
        (fun model0' -> exists delta_sent0 delta_received0 tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_sent_seal_replay model0' rest tail_sent tail_received model1) in
    let model0' : connection_model = model0'_w in
    assert (exists delta_sent0' delta_received0' tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0' delta_received0' /\
      sent_event_nonempty_seal_projection model ev0 delta_sent0' /\
      Seq.equal raw_sent (B.append delta_sent0' tail_sent') /\
      Seq.equal raw_received (B.append delta_received0' tail_received') /\
      conn_events_sent_seal_replay model0' rest tail_sent' tail_received' model1);
    let delta_sent0_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_sent0 -> exists delta_received0 tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_sent_seal_replay model0' rest tail_sent tail_received model1) in
    let delta_sent0 : B.bytes = delta_sent0_w in
    assert (exists delta_received0' tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0' /\
      sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent') /\
      Seq.equal raw_received (B.append delta_received0' tail_received') /\
      conn_events_sent_seal_replay model0' rest tail_sent' tail_received' model1);
    let delta_received0_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_received0 -> exists tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_sent_seal_replay model0' rest tail_sent tail_received model1) in
    let delta_received0 : B.bytes = delta_received0_w in
    assert (exists tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
      sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent') /\
      Seq.equal raw_received (B.append delta_received0 tail_received') /\
      conn_events_sent_seal_replay model0' rest tail_sent' tail_received' model1);
    let tail_sent_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_sent -> exists tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_sent_seal_replay model0' rest tail_sent tail_received model1) in
    let tail_sent : B.bytes = tail_sent_w in
    assert (exists tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
      sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
      Seq.equal raw_received (B.append delta_received0 tail_received') /\
      conn_events_sent_seal_replay model0' rest tail_sent tail_received' model1);
    let tail_received_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_received ->
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_sent_seal_replay model0' rest tail_sent tail_received model1) in
    let tail_received : B.bytes = tail_received_w in
    assert (legal_event model ev0);
    assert (step_model model ev0 == Some model0');
    assert (event_raw_delta_legal model ev0 delta_sent0 delta_received0);
    assert (sent_event_nonempty_seal_projection model ev0 delta_sent0);
    assert (Seq.equal raw_sent (B.append delta_sent0 tail_sent));
    assert (Seq.equal raw_received (B.append delta_received0 tail_received));
    assert (conn_events_sent_seal_replay model0' rest tail_sent tail_received model1);
    lemma_conn_events_sent_seal_replay_snoc
      model0'
      rest
      tail_sent
      tail_received
      model1
      ev
      delta_sent
      delta_received
      model2;
    Seq.lemma_eq_elim raw_sent (B.append delta_sent0 tail_sent);
    Seq.lemma_eq_elim raw_received (B.append delta_received0 tail_received);
    Seq.append_assoc delta_sent0 tail_sent delta_sent;
    Seq.append_assoc delta_received0 tail_received delta_received;
    assert (Seq.equal
      (B.append (B.append delta_sent0 tail_sent) delta_sent)
      (B.append delta_sent0 (B.append tail_sent delta_sent)));
    assert (Seq.equal
      (B.append (B.append delta_received0 tail_received) delta_received)
      (B.append delta_received0 (B.append tail_received delta_received)));
    assert (conn_events_sent_seal_replay
      model0'
      (rest @ [ev])
      (B.append tail_sent delta_sent)
      (B.append tail_received delta_received)
      model2);
    assert (events @ [ev] == ev0 :: (rest @ [ev]));
    assert (Seq.equal
      (B.append raw_sent delta_sent)
      (B.append delta_sent0 (B.append tail_sent delta_sent)));
    assert (Seq.equal
      (B.append raw_received delta_received)
      (B.append delta_received0 (B.append tail_received delta_received)));
    lemma_conn_events_sent_seal_replay_cons
      model
      ev0
      (rest @ [ev])
      (B.append raw_sent delta_sent)
      (B.append raw_received delta_received)
      model2
      model0'
      delta_sent0
      delta_received0
      (B.append tail_sent delta_sent)
      (B.append tail_received delta_received)

let lemma_conn_events_received_decode_replay_cons
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (model1:connection_model)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (tail_sent:B.bytes)
  (tail_received:B.bytes)
  : Lemma
      (requires
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        received_event_nonempty_decode_projection model ev delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        conn_events_received_decode_replay model1 rest tail_sent tail_received final_model)
      (ensures
        conn_events_received_decode_replay model (ev :: rest) raw_sent raw_received final_model)
=
  FStar.Classical.exists_intro
    (fun tail_received' ->
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_received_decode_replay model1 rest tail_sent tail_received' final_model)
    tail_received;
  FStar.Classical.exists_intro
    (fun tail_sent' ->
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        received_event_nonempty_decode_projection model ev delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received tail_received') /\
        conn_events_received_decode_replay model1 rest tail_sent' tail_received' final_model)
    tail_sent;
  FStar.Classical.exists_intro
    (fun delta_received' ->
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_replay model1 rest tail_sent' tail_received' final_model)
    delta_received;
  FStar.Classical.exists_intro
    (fun delta_sent' ->
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_replay model1 rest tail_sent' tail_received' final_model)
    delta_sent;
  FStar.Classical.exists_intro
    (fun model1' ->
      exists (delta_sent':B.bytes).
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_replay model1' rest tail_sent' tail_received' final_model)
    model1;
  assert_norm (
    conn_events_received_decode_replay model (ev :: rest) raw_sent raw_received final_model ==
    (exists (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       received_event_nonempty_decode_projection model ev delta_received' /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_received_decode_replay model1' rest tail_sent' tail_received' final_model));
  assert (conn_events_received_decode_replay model (ev :: rest) raw_sent raw_received final_model)

let lemma_conn_events_received_decode_key_schedule_replay_cons
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (model1:connection_model)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (tail_sent:B.bytes)
  (tail_received:B.bytes)
  : Lemma
      (requires
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        received_event_nonempty_decode_projection model ev delta_received /\
        record_read_key_schedule_projection model /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        conn_events_received_decode_key_schedule_replay
          model1
          rest
          tail_sent
          tail_received
          final_model)
      (ensures
        conn_events_received_decode_key_schedule_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model)
=
  FStar.Classical.exists_intro
    (fun tail_received' ->
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      record_read_key_schedule_projection model /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_received_decode_key_schedule_replay
        model1
        rest
        tail_sent
        tail_received'
        final_model)
    tail_received;
  FStar.Classical.exists_intro
    (fun tail_sent' ->
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        received_event_nonempty_decode_projection model ev delta_received /\
        record_read_key_schedule_projection model /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received tail_received') /\
        conn_events_received_decode_key_schedule_replay
          model1
          rest
          tail_sent'
          tail_received'
          final_model)
    tail_sent;
  FStar.Classical.exists_intro
    (fun delta_received' ->
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        record_read_key_schedule_projection model /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_key_schedule_replay
          model1
          rest
          tail_sent'
          tail_received'
          final_model)
    delta_received;
  FStar.Classical.exists_intro
    (fun delta_sent' ->
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        record_read_key_schedule_projection model /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_key_schedule_replay
          model1
          rest
          tail_sent'
          tail_received'
          final_model)
    delta_sent;
  FStar.Classical.exists_intro
    (fun model1' ->
      exists (delta_sent':B.bytes).
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        record_read_key_schedule_projection model /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_key_schedule_replay
          model1'
          rest
          tail_sent'
          tail_received'
          final_model)
    model1;
  assert_norm (
    conn_events_received_decode_key_schedule_replay
      model
      (ev :: rest)
      raw_sent
      raw_received
      final_model ==
    (exists (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       received_event_nonempty_decode_projection model ev delta_received' /\
       record_read_key_schedule_projection model /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_received_decode_key_schedule_replay
         model1'
         rest
         tail_sent'
         tail_received'
         final_model));
  assert (conn_events_received_decode_key_schedule_replay
    model
    (ev :: rest)
    raw_sent
    raw_received
    final_model)

let rec lemma_conn_events_received_decode_replay_strengthen
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_received_decode_replay
          model
          events
          raw_sent
          raw_received
          final_model /\
        model.model_config.config_role == ClientEndpoint /\
        model_record_keys_consistent model)
      (ensures
        conn_events_received_decode_key_schedule_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (decreases events)
=
  match events with
  | [] ->
    ()
  | ev :: rest ->
    assert_norm (
      conn_events_received_decode_replay
        model
        (ev :: rest)
        raw_sent
        raw_received
        final_model ==
      (exists (model1':connection_model)
              (delta_sent':B.bytes)
              (delta_received':B.bytes)
              (tail_sent':B.bytes)
              (tail_received':B.bytes).
         legal_event model ev /\
         step_model model ev == Some model1' /\
         event_raw_delta_legal model ev delta_sent' delta_received' /\
         received_event_nonempty_decode_projection model ev delta_received' /\
         Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
         Seq.equal raw_received (B.append delta_received' tail_received') /\
         conn_events_received_decode_replay
           model1'
           rest
           tail_sent'
           tail_received'
           final_model));
    assert (exists (model1':connection_model)
                   (delta_sent':B.bytes)
                   (delta_received':B.bytes)
                   (tail_sent':B.bytes)
                   (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       received_event_nonempty_decode_projection model ev delta_received' /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_received_decode_replay
         model1'
         rest
         tail_sent'
         tail_received'
         final_model);
    let model1_w =
      ID.indefinite_description_ghost
        connection_model
        (fun model1 -> exists delta_sent delta_received tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          received_event_nonempty_decode_projection model ev delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_received_decode_replay
            model1
            rest
            tail_sent
            tail_received
            final_model) in
    let model1 : connection_model = model1_w in
    assert (exists delta_sent' delta_received' tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      received_event_nonempty_decode_projection model ev delta_received' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_received_decode_replay
        model1
        rest
        tail_sent'
        tail_received'
        final_model);
    let delta_sent_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_sent -> exists delta_received tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          received_event_nonempty_decode_projection model ev delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_received_decode_replay
            model1
            rest
            tail_sent
            tail_received
            final_model) in
    let delta_sent : B.bytes = delta_sent_w in
    assert (exists delta_received' tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received' /\
      received_event_nonempty_decode_projection model ev delta_received' /\
      Seq.equal raw_sent (B.append delta_sent tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_received_decode_replay
        model1
        rest
        tail_sent'
        tail_received'
        final_model);
    let delta_received_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_received -> exists tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          received_event_nonempty_decode_projection model ev delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_received_decode_replay
            model1
            rest
            tail_sent
            tail_received
            final_model) in
    let delta_received : B.bytes = delta_received_w in
    assert (exists tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent') /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_received_decode_replay
        model1
        rest
        tail_sent'
        tail_received'
        final_model);
    let tail_sent_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_sent -> exists tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          received_event_nonempty_decode_projection model ev delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_received_decode_replay
            model1
            rest
            tail_sent
            tail_received
            final_model) in
    let tail_sent : B.bytes = tail_sent_w in
    assert (exists tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_received_decode_replay
        model1
        rest
        tail_sent
        tail_received'
        final_model);
    let tail_received_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_received ->
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          received_event_nonempty_decode_projection model ev delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_received_decode_replay
            model1
            rest
            tail_sent
            tail_received
            final_model) in
    let tail_received : B.bytes = tail_received_w in
    assert (legal_event model ev);
    assert (step_model model ev == Some model1);
    assert (event_raw_delta_legal model ev delta_sent delta_received);
    assert (received_event_nonempty_decode_projection model ev delta_received);
    assert (Seq.equal raw_sent (B.append delta_sent tail_sent));
    assert (Seq.equal raw_received (B.append delta_received tail_received));
    assert (conn_events_received_decode_replay
      model1
      rest
      tail_sent
      tail_received
      final_model);
    assert (model.model_config.config_role == ClientEndpoint);
    lemma_model_record_keys_consistent_record_read_key_schedule_projection model;
    lemma_step_model_record_keys_consistent model ev model1;
    assert (model_record_keys_consistent model1);
    assert_norm (model_record_keys_consistent model1 ==
      (model1.model_config.config_role == ClientEndpoint /\
       model_record_keys_consistent_for_role ClientEndpoint model1));
    assert (model1.model_config.config_role == ClientEndpoint);
    lemma_conn_events_received_decode_replay_strengthen
      model1
      rest
      tail_sent
      tail_received
      final_model;
    lemma_conn_events_received_decode_key_schedule_replay_cons
      model
      ev
      rest
      raw_sent
      raw_received
      final_model
      model1
      delta_sent
      delta_received
      tail_sent
      tail_received

let rec lemma_conn_events_received_decode_replay_snoc
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (model1:connection_model)
  (ev:conn_event)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (model2:connection_model)
  : Lemma
      (requires
        conn_events_received_decode_replay model events raw_sent raw_received model1 /\
        legal_event model1 ev /\
        step_model model1 ev == Some model2 /\
        event_raw_delta_legal model1 ev delta_sent delta_received /\
        received_event_nonempty_decode_projection model1 ev delta_received)
      (ensures
        conn_events_received_decode_replay
          model
          (events @ [ev])
          (B.append raw_sent delta_sent)
          (B.append raw_received delta_received)
          model2)
      (decreases events)
=
  match events with
  | [] ->
    Seq.lemma_eq_elim raw_sent B.empty;
    Seq.lemma_eq_elim raw_received B.empty;
    CL.lemma_append_empty_left delta_sent;
    CL.lemma_append_empty_left delta_received;
    CL.lemma_append_empty_right delta_sent;
    CL.lemma_append_empty_right delta_received;
    assert (model1 == model);
    assert (legal_event model ev);
    assert (step_model model ev == Some model2);
    assert (event_raw_delta_legal model ev delta_sent delta_received);
    assert (received_event_nonempty_decode_projection model ev delta_received);
    assert (Seq.equal
      (B.append raw_sent delta_sent)
      (B.append delta_sent B.empty));
    assert (Seq.equal
      (B.append raw_received delta_received)
      (B.append delta_received B.empty));
    assert (conn_events_received_decode_replay model2 [] B.empty B.empty model2);
    lemma_conn_events_received_decode_replay_cons
      model
      ev
      []
      (B.append raw_sent delta_sent)
      (B.append raw_received delta_received)
      model2
      model2
      delta_sent
      delta_received
      B.empty
      B.empty
  | ev0 :: rest ->
    assert_norm (
      conn_events_received_decode_replay model (ev0 :: rest) raw_sent raw_received model1 ==
      (exists (model0':connection_model)
              (delta_sent0:B.bytes)
              (delta_received0:B.bytes)
              (tail_sent:B.bytes)
              (tail_received:B.bytes).
         legal_event model ev0 /\
         step_model model ev0 == Some model0' /\
         event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
         received_event_nonempty_decode_projection model ev0 delta_received0 /\
         Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
         Seq.equal raw_received (B.append delta_received0 tail_received) /\
         conn_events_received_decode_replay model0' rest tail_sent tail_received model1));
    assert (exists (model0':connection_model)
                   (delta_sent0:B.bytes)
                   (delta_received0:B.bytes)
                   (tail_sent:B.bytes)
                   (tail_received:B.bytes).
       legal_event model ev0 /\
       step_model model ev0 == Some model0' /\
       event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
       received_event_nonempty_decode_projection model ev0 delta_received0 /\
       Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
       Seq.equal raw_received (B.append delta_received0 tail_received) /\
       conn_events_received_decode_replay model0' rest tail_sent tail_received model1);
    let model0'_w =
      ID.indefinite_description_ghost
        connection_model
        (fun model0' -> exists delta_sent0 delta_received0 tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          received_event_nonempty_decode_projection model ev0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_received_decode_replay model0' rest tail_sent tail_received model1) in
    let model0' : connection_model = model0'_w in
    assert (exists delta_sent0' delta_received0' tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0' delta_received0' /\
      received_event_nonempty_decode_projection model ev0 delta_received0' /\
      Seq.equal raw_sent (B.append delta_sent0' tail_sent') /\
      Seq.equal raw_received (B.append delta_received0' tail_received') /\
      conn_events_received_decode_replay model0' rest tail_sent' tail_received' model1);
    let delta_sent0_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_sent0 -> exists delta_received0 tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          received_event_nonempty_decode_projection model ev0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_received_decode_replay model0' rest tail_sent tail_received model1) in
    let delta_sent0 : B.bytes = delta_sent0_w in
    assert (exists delta_received0' tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0' /\
      received_event_nonempty_decode_projection model ev0 delta_received0' /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent') /\
      Seq.equal raw_received (B.append delta_received0' tail_received') /\
      conn_events_received_decode_replay model0' rest tail_sent' tail_received' model1);
    let delta_received0_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_received0 -> exists tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          received_event_nonempty_decode_projection model ev0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_received_decode_replay model0' rest tail_sent tail_received model1) in
    let delta_received0 : B.bytes = delta_received0_w in
    assert (exists tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
      received_event_nonempty_decode_projection model ev0 delta_received0 /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent') /\
      Seq.equal raw_received (B.append delta_received0 tail_received') /\
      conn_events_received_decode_replay model0' rest tail_sent' tail_received' model1);
    let tail_sent_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_sent -> exists tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          received_event_nonempty_decode_projection model ev0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_received_decode_replay model0' rest tail_sent tail_received model1) in
    let tail_sent : B.bytes = tail_sent_w in
    assert (exists tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
      received_event_nonempty_decode_projection model ev0 delta_received0 /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
      Seq.equal raw_received (B.append delta_received0 tail_received') /\
      conn_events_received_decode_replay model0' rest tail_sent tail_received' model1);
    let tail_received_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_received ->
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          received_event_nonempty_decode_projection model ev0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_received_decode_replay model0' rest tail_sent tail_received model1) in
    let tail_received : B.bytes = tail_received_w in
    assert (legal_event model ev0);
    assert (step_model model ev0 == Some model0');
    assert (event_raw_delta_legal model ev0 delta_sent0 delta_received0);
    assert (received_event_nonempty_decode_projection model ev0 delta_received0);
    assert (Seq.equal raw_sent (B.append delta_sent0 tail_sent));
    assert (Seq.equal raw_received (B.append delta_received0 tail_received));
    assert (conn_events_received_decode_replay model0' rest tail_sent tail_received model1);
    lemma_conn_events_received_decode_replay_snoc
      model0'
      rest
      tail_sent
      tail_received
      model1
      ev
      delta_sent
      delta_received
      model2;
    Seq.lemma_eq_elim raw_sent (B.append delta_sent0 tail_sent);
    Seq.lemma_eq_elim raw_received (B.append delta_received0 tail_received);
    Seq.append_assoc delta_sent0 tail_sent delta_sent;
    Seq.append_assoc delta_received0 tail_received delta_received;
    assert (Seq.equal
      (B.append (B.append delta_sent0 tail_sent) delta_sent)
      (B.append delta_sent0 (B.append tail_sent delta_sent)));
    assert (Seq.equal
      (B.append (B.append delta_received0 tail_received) delta_received)
      (B.append delta_received0 (B.append tail_received delta_received)));
    assert (conn_events_received_decode_replay
      model0'
      (rest @ [ev])
      (B.append tail_sent delta_sent)
      (B.append tail_received delta_received)
      model2);
    assert (events @ [ev] == ev0 :: (rest @ [ev]));
    assert (Seq.equal
      (B.append raw_sent delta_sent)
      (B.append delta_sent0 (B.append tail_sent delta_sent)));
    assert (Seq.equal
      (B.append raw_received delta_received)
      (B.append delta_received0 (B.append tail_received delta_received)));
    lemma_conn_events_received_decode_replay_cons
      model
      ev0
      (rest @ [ev])
      (B.append raw_sent delta_sent)
      (B.append raw_received delta_received)
      model2
      model0'
      delta_sent0
      delta_received0
      (B.append tail_sent delta_sent)
      (B.append tail_received delta_received)

let lemma_initial_sent_seal_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_sent_seal_replay_consistent (initial cfg))
=
  ()

let lemma_initial_sent_seal_key_schedule_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_sent_seal_key_schedule_replay_consistent (initial cfg))
=
  ()

let lemma_connection_state_sent_seal_key_schedule_replay
  (st:connection_state)
  : Lemma
      (requires
        st.cs_model.model_config.config_role == ClientEndpoint /\
        connection_state_sent_seal_replay_consistent st)
      (ensures connection_state_sent_seal_key_schedule_replay_consistent st)
=
  lemma_initial_record_keys_consistent st.cs_model.model_config;
  assert (model_record_keys_consistent (initial_model st.cs_model.model_config));
  lemma_conn_events_sent_seal_replay_strengthen
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model

let lemma_initial_received_decode_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_received_decode_replay_consistent (initial cfg))
=
  ()

let lemma_initial_received_decode_key_schedule_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_received_decode_key_schedule_replay_consistent (initial cfg))
=
  ()

let lemma_connection_state_received_decode_key_schedule_replay
  (st:connection_state)
  : Lemma
      (requires
        st.cs_model.model_config.config_role == ClientEndpoint /\
        connection_state_received_decode_replay_consistent st)
      (ensures connection_state_received_decode_key_schedule_replay_consistent st)
=
  lemma_initial_record_keys_consistent st.cs_model.model_config;
  assert (model_record_keys_consistent (initial_model st.cs_model.model_config));
  lemma_conn_events_received_decode_replay_strengthen
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model

let lemma_initial_raw_to_message_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_raw_to_message_replay_consistent (initial cfg))
=
  lemma_connection_state_protected_raw_segmented_replay (initial cfg);
  lemma_initial_sent_seal_replay_consistent cfg;
  lemma_initial_sent_seal_key_schedule_replay_consistent cfg;
  lemma_initial_received_decode_replay_consistent cfg;
  lemma_initial_received_decode_key_schedule_replay_consistent cfg

let lemma_connection_state_raw_to_message_replay
  (st:connection_state)
  : Lemma
      (requires
        st.cs_model.model_config.config_role == ClientEndpoint /\
        connection_state_raw_event_replay_consistent st /\
        connection_state_sent_seal_replay_consistent st /\
        connection_state_received_decode_replay_consistent st)
      (ensures connection_state_raw_to_message_replay_consistent st)
=
  lemma_connection_state_protected_raw_segmented_replay st;
  lemma_connection_state_sent_seal_key_schedule_replay st;
  lemma_connection_state_received_decode_key_schedule_replay st

let lemma_initial_raw_event_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_raw_event_replay_consistent (initial cfg))
=
  ()

let lemma_legal_connection_delta_raw_event_replay_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_raw_event_replay_consistent st0)
      (ensures connection_state_raw_event_replay_consistent st1)
=
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  assert (st1.cs_wire_log.CL.raw_sent ==
    B.append st0.cs_wire_log.CL.raw_sent delta.delta_raw_sent);
  assert (st1.cs_wire_log.CL.raw_received ==
    B.append st0.cs_wire_log.CL.raw_received delta.delta_raw_received);
  lemma_conn_events_raw_replay_snoc
    (initial_model st0.cs_model.model_config)
    st0.cs_event_log
    st0.cs_wire_log.CL.raw_sent
    st0.cs_wire_log.CL.raw_received
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received
    st1.cs_model

let lemma_legal_connection_delta_sent_seal_replay_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_sent_seal_replay_consistent st0 /\
        sent_event_nonempty_seal_projection
          st0.cs_model
          delta.delta_event
          delta.delta_raw_sent)
      (ensures connection_state_sent_seal_replay_consistent st1)
=
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  assert (st1.cs_wire_log.CL.raw_sent ==
    B.append st0.cs_wire_log.CL.raw_sent delta.delta_raw_sent);
  assert (st1.cs_wire_log.CL.raw_received ==
    B.append st0.cs_wire_log.CL.raw_received delta.delta_raw_received);
  lemma_conn_events_sent_seal_replay_snoc
    (initial_model st0.cs_model.model_config)
    st0.cs_event_log
    st0.cs_wire_log.CL.raw_sent
    st0.cs_wire_log.CL.raw_received
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received
    st1.cs_model

let lemma_legal_connection_delta_received_decode_replay_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_received_decode_replay_consistent st0 /\
        received_event_nonempty_decode_projection
          st0.cs_model
          delta.delta_event
          delta.delta_raw_received)
      (ensures connection_state_received_decode_replay_consistent st1)
=
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  assert (st1.cs_wire_log.CL.raw_sent ==
    B.append st0.cs_wire_log.CL.raw_sent delta.delta_raw_sent);
  assert (st1.cs_wire_log.CL.raw_received ==
    B.append st0.cs_wire_log.CL.raw_received delta.delta_raw_received);
  lemma_conn_events_received_decode_replay_snoc
    (initial_model st0.cs_model.model_config)
    st0.cs_event_log
    st0.cs_wire_log.CL.raw_sent
    st0.cs_wire_log.CL.raw_received
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received
    st1.cs_model

let lemma_legal_connection_delta_app_log_delta
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures model_app_log_delta st0.cs_model delta.delta_event st1.cs_model)
=
  lemma_step_model_app_log_delta
    st0.cs_model
    delta.delta_event
    st1.cs_model

let lemma_legal_connection_delta_app_log_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_app_log_consistent st0)
      (ensures connection_state_app_log_consistent st1)
=
  lemma_legal_connection_delta_app_log_delta st0 delta st1;
  lemma_app_sent_messages_snoc st0.cs_event_log delta.delta_event;
  lemma_app_received_messages_snoc st0.cs_event_log delta.delta_event;
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  assert (st1.cs_model.model_application.app_log.CL.app_sent ==
    st0.cs_model.model_application.app_log.CL.app_sent @
      conn_event_app_sent_delta delta.delta_event);
  assert (st1.cs_model.model_application.app_log.CL.app_received ==
    st0.cs_model.model_application.app_log.CL.app_received @
      conn_event_app_received_delta delta.delta_event);
  assert (app_sent_messages st1.cs_event_log ==
    app_sent_messages st0.cs_event_log @
      conn_event_app_sent_delta delta.delta_event);
  assert (app_received_messages st1.cs_event_log ==
    app_received_messages st0.cs_event_log @
      conn_event_app_received_delta delta.delta_event)

let lemma_legal_connection_delta_event_log_consistent_with
  (cfg:connection_config)
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_event_log_consistent_with cfg st0)
      (ensures connection_state_event_log_consistent_with cfg st1)
=
  lemma_step_model_many_snoc
    (initial_model cfg)
    st0.cs_event_log
    delta.delta_event
    st0.cs_model
    st1.cs_model;
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event])

let lemma_legal_connection_delta_event_log_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_event_log_consistent st0)
      (ensures connection_state_event_log_consistent st1)
=
  lemma_legal_connection_delta_event_log_consistent_with
    st0.cs_model.model_config
    st0
    delta
    st1;
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config)

let lemma_legal_connection_delta_transcript_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_transcript_consistent st0)
      (ensures connection_state_transcript_consistent st1)
=
  lemma_step_model_transcript_delta st0.cs_model delta.delta_event st1.cs_model;
  lemma_transcript_bytes_snoc st0.cs_event_log delta.delta_event;
  Seq.lemma_eq_elim
    st0.cs_model.model_handshake.hs_transcript
    (transcript_bytes_of_conn_events st0.cs_event_log);
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  assert (Seq.equal
    st1.cs_model.model_handshake.hs_transcript
    (B.append
      st0.cs_model.model_handshake.hs_transcript
      (conn_event_transcript_delta delta.delta_event)));
  assert (B.append
    st0.cs_model.model_handshake.hs_transcript
    (conn_event_transcript_delta delta.delta_event) ==
    transcript_bytes_of_conn_events st1.cs_event_log)

let lemma_legal_connection_delta_key_update_pending_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_key_update_pending_consistent st0)
      (ensures connection_state_key_update_pending_consistent st1)
=
  lemma_step_model_key_update_pending_delta st0.cs_model delta.delta_event st1.cs_model;
  lemma_key_update_response_pending_snoc st0.cs_event_log delta.delta_event;
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  assert (st1.cs_model.model_application.app_key_update_response_pending ==
    key_update_response_pending_step
      st0.cs_model.model_application.app_key_update_response_pending
      delta.delta_event);
  assert (st0.cs_model.model_application.app_key_update_response_pending ==
    key_update_response_pending_of_conn_events st0.cs_event_log);
  assert (st1.cs_model.model_application.app_key_update_response_pending ==
    key_update_response_pending_step
      (key_update_response_pending_of_conn_events st0.cs_event_log)
      delta.delta_event);
  assert (key_update_response_pending_of_conn_events st1.cs_event_log ==
    key_update_response_pending_step
      (key_update_response_pending_of_conn_events st0.cs_event_log)
      delta.delta_event)

let lemma_legal_connection_delta_record_layer_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_record_layer_consistent st0)
      (ensures connection_state_record_layer_consistent st1)
=
  lemma_step_model_record_layer_delta st0.cs_model delta.delta_event st1.cs_model;
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  lemma_projected_record_layer_snoc_for_role
    st0.cs_model.model_config.config_role
    st0.cs_event_log
    delta.delta_event;
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  match st1.cs_model.model_control with
  | ControlFailed _ -> ()
  | _ ->
    assert (projected_record_layer_state_of_record st1.cs_model.model_record ==
      projected_record_layer_step_for_role
        st0.cs_model.model_config.config_role
        (projected_record_layer_state_of_record st0.cs_model.model_record)
        delta.delta_event);
    assert (projected_record_layer_state_of_record st0.cs_model.model_record ==
      projected_record_layer_of_conn_events_for_role
        st0.cs_model.model_config.config_role
        st0.cs_event_log);
    assert (projected_record_layer_state_of_record st1.cs_model.model_record ==
      projected_record_layer_step_for_role
        st0.cs_model.model_config.config_role
        (projected_record_layer_of_conn_events_for_role
          st0.cs_model.model_config.config_role
          st0.cs_event_log)
        delta.delta_event);
    assert (projected_record_layer_of_conn_events_for_role
      st0.cs_model.model_config.config_role
      st1.cs_event_log ==
      projected_record_layer_step_for_role
        st0.cs_model.model_config.config_role
        (projected_record_layer_of_conn_events_for_role
          st0.cs_model.model_config.config_role
          st0.cs_event_log)
        delta.delta_event)

let lemma_legal_connection_delta_record_keys_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_record_keys_consistent st0)
      (ensures connection_state_record_keys_consistent st1)
=
  assert (st0.cs_model.model_config.config_role == ClientEndpoint);
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  lemma_step_model_record_keys_consistent
    st0.cs_model
    delta.delta_event
    st1.cs_model

let lemma_legal_connection_delta_record_keys_consistent_for_role
  (role:endpoint_role)
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        role == st0.cs_model.model_config.config_role /\
        connection_state_record_keys_consistent_for_role role st0)
      (ensures connection_state_record_keys_consistent_for_role role st1)
=
  lemma_step_model_record_keys_consistent_for_role
    role
    st0.cs_model
    delta.delta_event
    st1.cs_model

let lemma_legal_connection_delta_pending_application_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_pending_application_consistent st0)
      (ensures connection_state_pending_application_consistent st1)
=
  lemma_step_model_pending_application_delta
    st0.cs_model
    delta.delta_event
    st1.cs_model

let lemma_legal_connection_delta_layered_log_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_layered_log_consistent st0)
      (ensures connection_state_layered_log_consistent st1)
=
  assert (st0.cs_model.model_config.config_role == ClientEndpoint);
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  lemma_legal_connection_delta_event_log_consistent st0 delta st1;
  lemma_legal_connection_delta_transcript_consistent st0 delta st1;
  lemma_legal_connection_delta_key_update_pending_consistent st0 delta st1;
  lemma_legal_connection_delta_record_layer_consistent st0 delta st1;
  lemma_legal_connection_delta_record_keys_consistent st0 delta st1;
  lemma_legal_connection_delta_pending_application_consistent st0 delta st1;
  lemma_legal_connection_delta_app_log_consistent st0 delta st1

let lemma_legal_connection_delta_layered_log_consistent_for_role
  (role:endpoint_role)
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        role == st0.cs_model.model_config.config_role /\
        connection_state_layered_log_consistent_for_role role st0)
      (ensures connection_state_layered_log_consistent_for_role role st1)
=
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  assert (role == st1.cs_model.model_config.config_role);
  lemma_legal_connection_delta_event_log_consistent st0 delta st1;
  lemma_legal_connection_delta_transcript_consistent st0 delta st1;
  lemma_legal_connection_delta_key_update_pending_consistent st0 delta st1;
  lemma_legal_connection_delta_record_layer_consistent st0 delta st1;
  lemma_legal_connection_delta_record_keys_consistent_for_role role st0 delta st1;
  lemma_legal_connection_delta_pending_application_consistent st0 delta st1;
  lemma_legal_connection_delta_app_log_consistent st0 delta st1

let lemma_initial_full_log_consistent
  (cfg:connection_config)
  : Lemma
      (requires cfg.config_role == ClientEndpoint)
      (ensures connection_state_full_log_consistent (initial cfg))
=
  lemma_initial_layered_log_consistent cfg;
  lemma_connection_state_connection_log_view_consistent (initial cfg);
  lemma_initial_raw_event_replay_consistent cfg

let lemma_initial_full_log_consistent_for_role
  (role:endpoint_role)
  (cfg:connection_config)
  : Lemma (connection_state_full_log_consistent_for_role role (initial cfg))
=
  lemma_initial_layered_log_consistent_for_role role cfg;
  lemma_connection_state_connection_log_view_consistent (initial cfg);
  lemma_initial_raw_event_replay_consistent cfg

let lemma_legal_connection_delta_full_log_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_full_log_consistent st0)
      (ensures connection_state_full_log_consistent st1)
=
  assert (st0.cs_model.model_config.config_role == ClientEndpoint);
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  lemma_legal_connection_delta_layered_log_consistent st0 delta st1;
  lemma_connection_state_connection_log_view_consistent st1;
  lemma_legal_connection_delta_raw_event_replay_consistent st0 delta st1

let lemma_legal_connection_delta_full_log_consistent_for_role
  (role:endpoint_role)
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        role == st0.cs_model.model_config.config_role /\
        connection_state_full_log_consistent_for_role role st0)
      (ensures connection_state_full_log_consistent_for_role role st1)
=
  lemma_legal_connection_delta_layered_log_consistent_for_role role st0 delta st1;
  lemma_connection_state_connection_log_view_consistent st1;
  lemma_legal_connection_delta_raw_event_replay_consistent st0 delta st1

let lemma_legal_connection_delta_protected_single_parse_record
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures event_protected_single_raw_parse_success
        delta.delta_event
        delta.delta_raw_sent
        delta.delta_raw_received)
=
  lemma_event_raw_delta_legal_protected_single_parse_record
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received

let lemma_legal_connection_delta_protected_parse_prefix
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures event_protected_raw_parse_prefix_success
        delta.delta_event
        delta.delta_raw_sent
        delta.delta_raw_received)
=
  lemma_event_raw_delta_legal_protected_parse_prefix
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received

let lemma_legal_connection_delta_protected_decompose_prefix
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures event_protected_raw_decompose_prefix_success
        delta.delta_event
        delta.delta_raw_sent
        delta.delta_raw_received)
=
  lemma_event_raw_delta_legal_protected_decompose_prefix
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received

let lemma_legal_connection_delta_protected_segmented
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures event_protected_raw_segmented_success
        delta.delta_event
        delta.delta_raw_sent
        delta.delta_raw_received)
=
  lemma_event_raw_delta_legal_protected_segmented
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received

let lemma_legal_connection_delta_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        connection_state_consistent st0 /\
        legal_connection_delta st0 delta st1)
      (ensures connection_state_consistent st1)
=
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  assert (connection_state_single_step st0 st1);
  RTC.closure_step connection_state_single_step st0 st1;
  assert (connection_state_evolves st0 st1);
  assert (connection_state_evolves (initial st0.cs_model.model_config) st0);
  assert (connection_state_evolves (initial st0.cs_model.model_config) st1)
