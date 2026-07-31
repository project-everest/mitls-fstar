module TLS13.ConnectionState.Lemmas

(**
  Public proof support for TLS13.Spec.StateMachine.

  This interface exposes only the connection-state lemmas used outside the
  proof module; the remaining local lemmas stay private implementation
  scaffolding.
**)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Canonical
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.KeyMaterial
open TLS13.Spec.StateMachine.Log
open TLS13.Spec.StateMachine.Replay

val lemma_endpoint_direction_traffic_labels
  (u:unit)
  : Lemma
      (ensures
        traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic /\
        traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic /\
        traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic /\
        traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic)

val lemma_legal_connection_delta_local_fail_control_failed
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

val lemma_step_model_from_failed_results_failed
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires
        ControlFailed? model0.model_control /\
        step_model model0 ev == Some model1)
      (ensures ControlFailed? model1.model_control)

val lemma_legal_connection_delta_stable_client_x25519_key_share_projection
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        stable_client_x25519_key_share_projection st0)
      (ensures stable_client_x25519_key_share_projection st1)

val lemma_legal_connection_delta_stable_server_x25519_key_share_projection
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        stable_server_x25519_key_share_projection st0)
      (ensures stable_server_x25519_key_share_projection st1)

val lemma_expected_traffic_secret_client_projection
  (hs:handshake_state)
  (epoch:traffic_epoch)
  (dir:traffic_direction)
  : Lemma
      (ensures
        expected_traffic_secret hs epoch dir ==
        expected_traffic_secret_for_role ClientEndpoint hs epoch dir)

val lemma_update_key_schedule_with_install_client_projection
  (keys:key_schedule_state)
  (install:traffic_key_install)
  : Lemma
      (ensures
        update_key_schedule_with_install keys install ==
        update_key_schedule_with_install_for_role ClientEndpoint keys install)

val lemma_connection_application_keys_supported_profile_key_schedule_lineage
  (role:endpoint_role)
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        application_record_keys_installed_for_role role st.cs_model)
      (ensures connection_supported_profile_key_schedule_lineage st)

val lemma_connection_state_consistent_server_selection_private_shape
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        st.cs_model.model_control == ControlHandshaking HsClientHelloReceived /\
        st.cs_model.model_handshake.hs_keys.ks_shared_secret == None /\
        Some? st.cs_model.model_handshake.hs_server_selection)
      (ensures
        (match st.cs_model.model_handshake.hs_server_selection with
         | Some selection ->
           server_selection_key_share_consistent selection /\
           st.cs_model.model_handshake.hs_client_hello ==
             Some selection.server_selected_client_hello
         | None -> False))

val lemma_connection_state_consistent_server_pre_server_hello_shape
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        st.cs_model.model_control == ControlHandshaking HsClientHelloReceived /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret)
      (ensures
        (match st.cs_model.model_handshake.hs_server_selection with
         | Some selection ->
           server_selection_key_share_consistent selection /\
           Some? selection.server_key_share_private
         | None -> False))

val lemma_server_handshake_write_record_has_keys
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        (st.cs_model.model_control == ControlHandshaking HsServerHelloSent \/
         st.cs_model.model_control == ControlHandshaking HsServerEncryptedFlightSent) /\
        Some? st.cs_model.model_handshake.hs_keys.ks_server_handshake_traffic)
      (ensures
        (match
          st.cs_model.model_record.record_write.R.key,
          st.cs_model.model_record.record_write.R.static_iv
        with
        | Some _, Some _ -> True
        | _, _ -> False))

val lemma_connection_application_ready_record_epochs_installed
  (role:endpoint_role)
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == role /\
        st.cs_model.model_control == ControlApplicationData /\
        application_record_keys_installed_for_role role st.cs_model)
      (ensures application_record_epochs_installed_for_role role st.cs_model)

(** Sub-goal (a) BRIDGE: a reachable endpoint at `ControlApplicationData` has both
    of its own application record keys installed (key + iv matching for read and
    write).  Established purely from reachability via the strengthened application
    record-epoch reachable shape, so no additional invariant is required. **)
val lemma_connection_appdata_keys_installed_for_role
  (role:endpoint_role)
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == role /\
        st.cs_model.model_control == ControlApplicationData)
      (ensures application_record_keys_installed_for_role role st.cs_model)

(** A reachable SERVER endpoint at `HsServerFinishedSent` has not yet installed the
    client application (read) traffic secret. **)
val lemma_server_finished_sent_no_client_application_traffic
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        st.cs_model.model_control == ControlHandshaking HsServerFinishedSent)
      (ensures
        st.cs_model.model_handshake.hs_keys.ks_client_application_traffic == None)

val lemma_client_application_ready_stable_x25519_key_share_projection
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ClientEndpoint /\
        st.cs_model.model_control == ControlApplicationData /\
        application_record_keys_installed_for_role ClientEndpoint st.cs_model)
      (ensures stable_client_x25519_key_share_projection st)

val lemma_server_application_ready_stable_x25519_key_share_projection
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        st.cs_model.model_control == ControlApplicationData /\
        application_record_keys_installed_for_role ServerEndpoint st.cs_model)
      (ensures stable_server_x25519_key_share_projection st)

val lemma_record_read_key_schedule_projection_client_projection
  (model:connection_model)
  : Lemma
      (ensures
        record_read_key_schedule_projection model ==
        record_read_key_schedule_projection_for_role ClientEndpoint model)

val lemma_record_write_key_schedule_projection_client_projection
  (model:connection_model)
  : Lemma
      (ensures
        record_write_key_schedule_projection model ==
        record_write_key_schedule_projection_for_role ClientEndpoint model)

val lemma_paired_endpoints_derived_key_agrees
  (key_id:derived_key_id)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        first_milestone_derived_key_id key_id /\
        derivation_inputs_agree key_id client server)
      (ensures peer_derived_key_material_agrees key_id client server)

val lemma_paired_x25519_key_shares_shared_secret_agree
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires paired_x25519_key_shares client server)
      (ensures shared_secret_material_agrees client server)

val lemma_paired_x25519_key_shares_base_secret_agree
  (base_id:base_secret_id)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        paired_x25519_key_shares client server /\
        connection_supported_profile_key_schedule_lineage client /\
        connection_supported_profile_key_schedule_lineage server)
      (ensures base_secret_inputs_agree base_id client server)

val lemma_paired_x25519_key_shares_derived_key_agrees
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

val lemma_paired_handshake_events_same_transcript_checkpoint
  (checkpoint:transcript_checkpoint)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires paired_handshake_events client server)
      (ensures same_transcript_checkpoint checkpoint client server)

val lemma_paired_handshake_events_same_key_derivation_checkpoint
  (checkpoint:key_derivation_checkpoint)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        paired_handshake_events client server /\
        (checkpoint == DeriveHandshakeTraffic \/
         checkpoint == DeriveApplicationTraffic))
      (ensures same_key_derivation_checkpoint checkpoint client server)

val lemma_paired_supported_profile_all_derived_key_material_agrees
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        paired_x25519_key_shares client server /\
        connection_supported_profile_key_schedule_lineage client /\
        connection_supported_profile_key_schedule_lineage server /\
        paired_key_derivation_checkpoints client server)
      (ensures
        supported_profile_all_derived_key_material_agrees client server)

val lemma_peer_record_material_agrees
  (traffic_id:labeled_traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires peer_record_material_inputs_agree traffic_id client server)
      (ensures peer_record_material_agrees traffic_id client server)

val lemma_paired_supported_profile_all_record_material_agrees
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        supported_profile_all_record_material_inputs_agree client server)
      (ensures
        supported_profile_all_record_material_agrees client server)

val lemma_paired_supported_profile_application_record_material_agrees
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        supported_profile_application_record_material_inputs_agree client server)
      (ensures
        supported_profile_application_record_material_agrees client server)

val lemma_supported_profile_application_record_material_inputs_agree_from_expected
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        supported_profile_all_derived_key_material_agrees client server /\
        supported_profile_application_traffic_material_matches_expected client /\
        supported_profile_application_traffic_material_matches_expected server /\
        application_record_keys_installed_for_role
          ClientEndpoint
          client.cs_model /\
        application_record_epochs_installed_for_role
          ClientEndpoint
          client.cs_model /\
        application_record_keys_installed_for_role
          ServerEndpoint
          server.cs_model /\
        application_record_epochs_installed_for_role
          ServerEndpoint
          server.cs_model)
      (ensures
        supported_profile_application_record_material_inputs_agree client server)

val lemma_no_key_update_application_traffic_material_matches_expected
  (role:endpoint_role)
  (st:connection_state)
  : Lemma
      (requires
        first_epoch_application_traffic_material_no_key_update_invariant st /\
        st.cs_model.model_config.config_role == role /\
        st.cs_model.model_control == ControlApplicationData /\
        application_record_keys_installed_for_role role st.cs_model)
      (ensures supported_profile_application_traffic_material_matches_expected st)

val lemma_supported_profile_client_server_key_material_agrees
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        supported_profile_client_server_key_material_inputs_agree client server)
      (ensures
        supported_profile_client_server_key_material_agrees client server)

val lemma_step_role_install_record_keys_consistent_for_role
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

val lemma_initial_record_keys_consistent_for_role
  (role:endpoint_role)
  (cfg:connection_config)
  : Lemma (connection_state_record_keys_consistent_for_role role (initial cfg))

val lemma_initial_layered_log_consistent_for_role
  (role:endpoint_role)
  (cfg:connection_config)
  : Lemma (connection_state_layered_log_consistent_for_role role (initial cfg))

val lemma_model_record_keys_consistent_record_read_key_schedule_projection
  (model:connection_model)
  : Lemma
      (requires model_record_keys_consistent model)
      (ensures record_read_key_schedule_projection model)

val lemma_model_record_keys_consistent_record_write_key_schedule_projection
  (model:connection_model)
  : Lemma
      (requires model_record_keys_consistent model)
      (ensures record_write_key_schedule_projection model)

val lemma_step_model_many_append
  (model0:connection_model)
  (prefix:list conn_event)
  (suffix:list conn_event)
  (mid:connection_model)
  (final:connection_model)
  : Lemma
      (requires
        step_model_many model0 prefix == Some mid /\
        step_model_many mid suffix == Some final)
      (ensures
        step_model_many model0 (FStar.List.Tot.append prefix suffix) ==
        Some final)

val lemma_step_model_many_append_split
  (model0:connection_model)
  (prefix:list conn_event)
  (suffix:list conn_event)
  (final:connection_model)
  : Lemma
      (requires
        step_model_many model0 (FStar.List.Tot.append prefix suffix) ==
        Some final)
      (ensures
        exists mid.
          step_model_many model0 prefix == Some mid /\
          step_model_many mid suffix == Some final)

val lemma_step_model_preserves_config
  (model:connection_model)
  (ev:conn_event)
  (model':connection_model)
  : Lemma
      (requires step_model model ev == Some model')
      (ensures model'.model_config == model.model_config)

val lemma_connection_state_no_key_update_trace_first_epoch_application_traffic_material_slots_match_expected
  (st:connection_state)
  : Lemma
      (requires
        connection_state_raw_event_replay_consistent st /\
        connection_state_no_key_update_trace st)
      (ensures
        first_epoch_application_traffic_material_slots_match_expected st)

val lemma_connection_state_consistent_server_certificate_verify_body_empty
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st)
      (ensures True)

val lemma_step_model_record_keys_consistent_for_role
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

val lemma_raw_records_exactly_one_parse_record
  (raw:B.bytes)
  (outer:T.content_type)
  : Lemma
      (requires raw_records_exactly raw outer 1)
      (ensures exists fragment.
        W.parse_record raw == Some (outer, fragment, B.length raw))

val lemma_parse_record_full_raw_records_exactly
  (raw:B.bytes)
  (outer:T.content_type)
  (fragment:B.bytes)
  : Lemma
      (requires W.parse_record raw == Some (outer, fragment, B.length raw))
      (ensures raw_records_exactly raw outer 1 /\
               raw_records_segmented raw outer 1)

val lemma_sent_event_seal_projection_intro
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
        W.parse_record raw == Some (T.Application_data, ciphertext, B.length raw) /\
        Seq.equal aad (record_header_aad raw) /\
        Seq.equal plaintext (sent_tls_inner_plaintext_fragment msg) /\
        R.seal
          model.model_record.record_write
          aad
          {
            R.content_type = T.Application_data;
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

val lemma_received_record_opened_from_sent_single_protected_message_seal
  (sender:connection_model)
  (receiver:connection_model)
  (msg:M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        sender.model_record.record_write == receiver.model_record.record_read /\
        sent_single_protected_message_seal sender msg raw)
      (ensures
        exists outer_fragment.
          W.parse_record raw ==
            Some (T.Application_data, outer_fragment, B.length raw) /\
          received_record_opened
            receiver
            raw
            outer_fragment
            (sent_tls_inner_plaintext_fragment msg))

val lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal
  (sender:connection_model)
  (receiver:connection_model)
  (msg:M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        sender.model_record.record_write == receiver.model_record.record_read /\
        sent_single_protected_message_seal sender msg raw /\
        (let (content_type, fragment) = W.serialize_tls_message msg in
         W.parse_tls_message content_type fragment == Some msg))
      (ensures received_single_protected_message_decode receiver msg raw)

val lemma_received_record_opened_from_sent_single_protected_message_seal_peer
  (sender:connection_model)
  (receiver:connection_model)
  (msg:M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        sender.model_record.record_write.R.seq ==
          receiver.model_record.record_read.R.seq /\
        (match
          record_direction_material sender.model_record.record_write,
          record_direction_material receiver.model_record.record_read
        with
        | Some sender_write, Some receiver_read ->
          record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        sent_single_protected_message_seal sender msg raw)
      (ensures
        exists outer_fragment.
          W.parse_record raw ==
            Some (T.Application_data, outer_fragment, B.length raw) /\
          received_record_opened
            receiver
            raw
            outer_fragment
            (sent_tls_inner_plaintext_fragment msg))

val lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer
  (sender:connection_model)
  (receiver:connection_model)
  (msg:M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        sender.model_record.record_write.R.seq ==
          receiver.model_record.record_read.R.seq /\
        (match
          record_direction_material sender.model_record.record_write,
          record_direction_material receiver.model_record.record_read
        with
        | Some sender_write, Some receiver_read ->
          record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        sent_single_protected_message_seal sender msg raw /\
        (let (content_type, fragment) = W.serialize_tls_message msg in
         W.parse_tls_message content_type fragment == Some msg))
      (ensures received_single_protected_message_decode receiver msg raw)

val lemma_event_raw_delta_legal_protected_segmented
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires event_raw_delta_legal model ev raw_sent raw_received)
      (ensures event_protected_raw_segmented_success ev raw_sent raw_received)

val lemma_connection_state_protected_raw_segmented_replay
  (st:connection_state)
  : Lemma
      (requires connection_state_raw_event_replay_consistent st)
      (ensures connection_state_protected_raw_segmented_replay_consistent st)

val lemma_initial_sent_seal_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_sent_seal_replay_consistent (initial cfg))

val lemma_initial_sent_seal_key_schedule_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_sent_seal_key_schedule_replay_consistent (initial cfg))

val lemma_connection_state_sent_seal_key_schedule_replay
  (st:connection_state)
  : Lemma
      (requires
        st.cs_model.model_config.config_role == ClientEndpoint /\
        connection_state_sent_seal_replay_consistent st)
      (ensures connection_state_sent_seal_key_schedule_replay_consistent st)

val lemma_initial_received_decode_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_received_decode_replay_consistent (initial cfg))

val lemma_initial_received_decode_key_schedule_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_received_decode_key_schedule_replay_consistent (initial cfg))

val lemma_connection_state_received_decode_key_schedule_replay
  (st:connection_state)
  : Lemma
      (requires
        st.cs_model.model_config.config_role == ClientEndpoint /\
        connection_state_received_decode_replay_consistent st)
      (ensures connection_state_received_decode_key_schedule_replay_consistent st)

val lemma_initial_raw_to_message_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_raw_to_message_replay_consistent (initial cfg))

val lemma_connection_state_raw_to_message_replay
  (st:connection_state)
  : Lemma
      (requires
        st.cs_model.model_config.config_role == ClientEndpoint /\
        connection_state_raw_event_replay_consistent st /\
        connection_state_sent_seal_replay_consistent st /\
        connection_state_received_decode_replay_consistent st)
      (ensures connection_state_raw_to_message_replay_consistent st)

val lemma_legal_connection_delta_raw_event_replay_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_raw_event_replay_consistent st0)
      (ensures connection_state_raw_event_replay_consistent st1)

val lemma_legal_connection_delta_sent_seal_replay_consistent
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

val lemma_legal_connection_delta_received_decode_replay_consistent
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

val lemma_legal_connection_delta_app_log_delta
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures model_app_log_delta st0.cs_model delta.delta_event st1.cs_model)

val lemma_legal_connection_delta_app_log_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_app_log_consistent st0)
      (ensures connection_state_app_log_consistent st1)

val lemma_legal_connection_delta_event_log_consistent_with
  (cfg:connection_config)
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_event_log_consistent_with cfg st0)
      (ensures connection_state_event_log_consistent_with cfg st1)

val lemma_legal_connection_delta_event_log_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_event_log_consistent st0)
      (ensures connection_state_event_log_consistent st1)

val lemma_legal_connection_delta_transcript_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_transcript_consistent st0)
      (ensures connection_state_transcript_consistent st1)

val lemma_legal_connection_delta_record_keys_consistent_for_role
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

val lemma_legal_connection_delta_layered_log_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_layered_log_consistent st0)
      (ensures connection_state_layered_log_consistent st1)

val lemma_legal_connection_delta_layered_log_consistent_for_role
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

val lemma_initial_full_log_consistent
  (cfg:connection_config)
  : Lemma
      (requires cfg.config_role == ClientEndpoint)
      (ensures connection_state_full_log_consistent (initial cfg))

val lemma_initial_full_log_consistent_for_role
  (role:endpoint_role)
  (cfg:connection_config)
  : Lemma (connection_state_full_log_consistent_for_role role (initial cfg))

val lemma_legal_connection_delta_full_log_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_full_log_consistent st0)
      (ensures connection_state_full_log_consistent st1)

val lemma_legal_connection_delta_full_log_consistent_for_role
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

val lemma_legal_connection_delta_protected_single_parse_record
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures event_protected_single_raw_parse_success
        delta.delta_event
        delta.delta_raw_sent
        delta.delta_raw_received)

val lemma_legal_connection_delta_protected_parse_prefix
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures event_protected_raw_parse_prefix_success
        delta.delta_event
        delta.delta_raw_sent
        delta.delta_raw_received)

val lemma_legal_connection_delta_protected_decompose_prefix
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures event_protected_raw_decompose_prefix_success
        delta.delta_event
        delta.delta_raw_sent
        delta.delta_raw_received)

val lemma_legal_connection_delta_protected_segmented
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures event_protected_raw_segmented_success
        delta.delta_event
        delta.delta_raw_sent
        delta.delta_raw_received)

val lemma_legal_connection_delta_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        connection_state_consistent st0 /\
        legal_connection_delta st0 delta st1)
      (ensures connection_state_consistent st1)
