module TLS13.Impl.Server.Schedule

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CryptoSpec = TLS13.Crypto.Spec
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module M = TLS13.Messages
module Sem = TLS13.Wire.Semantics
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module R = TLS13.Record.Spec
module ST = TLS13.Impl.Server.Types
module Tags = TLS13.Impl.ConnectionState.Tags
module T = TLS13.Types
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module W = TLS13.Wire.Spec

let lemma_control_snapshot_matches_hs_server_hello_sent
  (snapshot:CR.control_snapshot)
  (st:CS.connection_state)
  : Lemma
      (requires CR.control_snapshot_matches snapshot st /\
                U8.v snapshot.CR.snapshot_control_tag == 1 /\
                U8.v snapshot.CR.snapshot_handshake_stage_tag == 14)
      (ensures st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerHelloSent)
=
  assert (Tags.control_state_matches
    snapshot.CR.snapshot_control_tag
    snapshot.CR.snapshot_handshake_stage_tag
    snapshot.CR.snapshot_failure_present
    snapshot.CR.snapshot_failure_code
    snapshot.CR.snapshot_failure_alert
    st.CS.cs_model.CS.model_control);
  match st.CS.cs_model.CS.model_control with
  | CS.ControlHandshaking stage ->
    assert (Tags.handshake_stage_tag_matches
      snapshot.CR.snapshot_handshake_stage_tag
      stage);
    match stage with
    | CS.HsServerHelloSent -> ()
    | _ -> assert False
  | _ -> assert False

let lemma_control_snapshot_matches_hs_server_finished_sent
  (snapshot:CR.control_snapshot)
  (st:CS.connection_state)
  : Lemma
      (requires CR.control_snapshot_matches snapshot st /\
                U8.v snapshot.CR.snapshot_control_tag == 1 /\
                U8.v snapshot.CR.snapshot_handshake_stage_tag == 16)
      (ensures st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerFinishedSent)
=
  assert (Tags.control_state_matches
    snapshot.CR.snapshot_control_tag
    snapshot.CR.snapshot_handshake_stage_tag
    snapshot.CR.snapshot_failure_present
    snapshot.CR.snapshot_failure_code
    snapshot.CR.snapshot_failure_alert
    st.CS.cs_model.CS.model_control);
  match st.CS.cs_model.CS.model_control with
  | CS.ControlHandshaking stage ->
    assert (Tags.handshake_stage_tag_matches
      snapshot.CR.snapshot_handshake_stage_tag
      stage);
    match stage with
    | CS.HsServerFinishedSent -> ()
    | _ -> assert False
  | _ -> assert False

let lemma_control_snapshot_matches_hs_client_finished_received
  (snapshot:CR.control_snapshot)
  (st:CS.connection_state)
  : Lemma
      (requires CR.control_snapshot_matches snapshot st /\
                U8.v snapshot.CR.snapshot_control_tag == 1 /\
                U8.v snapshot.CR.snapshot_handshake_stage_tag == 17)
      (ensures st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsClientFinishedReceived)
=
  assert (Tags.control_state_matches
    snapshot.CR.snapshot_control_tag
    snapshot.CR.snapshot_handshake_stage_tag
    snapshot.CR.snapshot_failure_present
    snapshot.CR.snapshot_failure_code
    snapshot.CR.snapshot_failure_alert
    st.CS.cs_model.CS.model_control);
  match st.CS.cs_model.CS.model_control with
  | CS.ControlHandshaking stage ->
    assert (Tags.handshake_stage_tag_matches
      snapshot.CR.snapshot_handshake_stage_tag
      stage);
    match stage with
    | CS.HsClientFinishedReceived -> ()
    | _ -> assert False
  | _ -> assert False

#push-options "--z3rlimit 200"
fn next_local_action
  (s:server)
  requires connection_exactly s 'st0 **
           pure (ST.server_state_correct 'st0)
  returns action:ST.next_local_action
  ensures connection_exactly s 'st0 **
          pure (ST.server_state_correct 'st0 /\
                ST.next_local_action_sound 'st0 action)
{
  unfold (connection_exactly s 'st0);
  let control = CQ.get_control_snapshot s;
  let keys = CQ.get_key_schedule_snapshot s;
  let start_ready = CQ.can_start_server_runtime s;
  assert (pure (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
    | Some cfg ->
      B.length cfg.CS.server_certificate_chain <=
        Bounds.max_server_certificate_chain_len
    | None -> False));
  let select_server_parameters_ready = CQ.can_schedule_select_server_parameters_runtime s;
  let derive_shared_secret_ready = CQ.can_schedule_derive_shared_secret_runtime s;
  let send_server_hello_ready = CQ.can_send_server_hello_runtime s;
  let send_encrypted_extensions_ready = CQ.can_send_encrypted_extensions_runtime s;
  let send_certificate_ready = CQ.can_send_certificate_runtime s;
  let sign_certificate_verify_ready = CQ.can_sign_certificate_verify_runtime s;
  let send_certificate_verify_ready = CQ.can_send_certificate_verify_runtime s;
  let send_server_finished_ready = CQ.can_send_server_finished_runtime s;
  let key_update_response_ready = CQ.server_key_update_response_ready_runtime s;
  fold (connection_exactly s 'st0);
  let server_handshake_write_keys_ready =
    (control.CR.snapshot_control_tag = 1uy) &&
    (control.CR.snapshot_handshake_stage_tag = 14uy) &&
    keys.CR.snapshot_handshake_secret_present &&
    not keys.CR.snapshot_server_handshake_traffic_present;
  let client_handshake_read_keys_ready =
    (control.CR.snapshot_control_tag = 1uy) &&
    (control.CR.snapshot_handshake_stage_tag = 14uy) &&
    keys.CR.snapshot_handshake_secret_present &&
    not keys.CR.snapshot_client_handshake_traffic_present;
  let server_application_write_keys_ready =
    (control.CR.snapshot_control_tag = 1uy) &&
    (control.CR.snapshot_handshake_stage_tag = 16uy) &&
    keys.CR.snapshot_master_secret_present &&
    not keys.CR.snapshot_server_application_traffic_present;
  let client_application_read_keys_ready =
    (control.CR.snapshot_control_tag = 1uy) &&
    (control.CR.snapshot_handshake_stage_tag = 17uy) &&
    keys.CR.snapshot_master_secret_present &&
    not keys.CR.snapshot_client_application_traffic_present;
  let verify_client_finished_ready =
    (control.CR.snapshot_control_tag = 1uy) &&
    (control.CR.snapshot_handshake_stage_tag = 17uy) &&
    keys.CR.snapshot_client_handshake_traffic_present &&
    keys.CR.snapshot_client_application_traffic_present &&
    keys.CR.snapshot_server_application_traffic_present;
  if start_ready {
    assert (pure ('st0.CS.cs_model.CS.model_control == CS.ControlNew));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure (Some? 'st0.CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (CS.legal_event
      'st0.CS.cs_model
      (CS.ConnLocalEvent CS.LocalStartServer)));
    assert (pure (CM.can_start_server 'st0));
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalStartServer;
      ST.next_local_payload = ST.LocalPayloadNone;
    }
  } else if select_server_parameters_ready {
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloReceived));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure (CR.server_selection_absent
      'st0.CS.cs_model.CS.model_handshake));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_config.CS.config_server));
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSelectServerParameters;
      ST.next_local_payload = ST.LocalPayloadServerRandomAndPrivateKey;
    }
  } else if derive_shared_secret_ready {
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloReceived));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure (
      match 'st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
      | Some selection ->
        CS.server_selection_key_share_consistent selection /\
        CS.server_selected_kex_group selection == CM.stored_client_hello_kex_group 'st0 /\
        'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
          Some selection.CS.server_selected_client_hello
      | None -> False));
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalDeriveSharedSecret;
      ST.next_local_payload = ST.LocalPayloadServerPrivateKey;
    }
  } else if send_server_hello_ready {
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloReceived));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret));
    assert (pure (
      'st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None));
    assert (pure (
      match 'st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
      | Some selection ->
        CS.server_selection_key_share_consistent selection /\
        CS.server_selected_kex_group selection == CM.stored_client_hello_kex_group 'st0 /\
        Some? selection.CS.server_key_share_private
      | None -> False));
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSendServerHello;
      ST.next_local_payload = ST.LocalPayloadServerRandomAndPrivateKey;
    }
  } else if server_handshake_write_keys_ready {
    assert (pure (control.CR.snapshot_control_tag == 1uy));
    assert (pure (control.CR.snapshot_handshake_stage_tag == 14uy));
    assert (pure (U8.v control.CR.snapshot_control_tag == 1));
    assert (pure (U8.v control.CR.snapshot_handshake_stage_tag == 14));
    assert_norm (Tags.handshake_stage_tag_matches 14uy CS.HsServerHelloSent);
    assert (pure (CR.control_snapshot_matches control 'st0));
    lemma_control_snapshot_matches_hs_server_hello_sent control 'st0;
    assert (pure (keys.CR.snapshot_handshake_secret_present));
    assert (pure (not keys.CR.snapshot_server_handshake_traffic_present));
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerHelloSent));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret));
    assert (pure (not (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic)));
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalInstallServerHandshakeTrafficKeys;
      ST.next_local_payload = ST.LocalPayloadNone;
    }
  } else if client_handshake_read_keys_ready {
    assert (pure (control.CR.snapshot_control_tag == 1uy));
    assert (pure (control.CR.snapshot_handshake_stage_tag == 14uy));
    assert (pure (U8.v control.CR.snapshot_control_tag == 1));
    assert (pure (U8.v control.CR.snapshot_handshake_stage_tag == 14));
    assert_norm (Tags.handshake_stage_tag_matches 14uy CS.HsServerHelloSent);
    assert (pure (CR.control_snapshot_matches control 'st0));
    lemma_control_snapshot_matches_hs_server_hello_sent control 'st0;
    assert (pure (keys.CR.snapshot_handshake_secret_present));
    assert (pure (not keys.CR.snapshot_client_handshake_traffic_present));
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerHelloSent));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret));
    assert (pure (not (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)));
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalInstallClientHandshakeTrafficKeys;
      ST.next_local_payload = ST.LocalPayloadNone;
    }
  } else if send_encrypted_extensions_ready {
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerHelloSent));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
    assert (pure (U64.fits
      ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    assert (pure (
      B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 6 <=
        Bounds.max_transcript_len));
    assert (pure (CS.legal_event
      'st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value =
          M.TlsHandshake (M.EncryptedExtensions ([] <: GEE.encryptedExtensions));
      })));
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSendEncryptedExtensions;
      ST.next_local_payload = ST.LocalPayloadNone;
    }
  } else if send_certificate_ready {
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerEncryptedFlightSent));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure ('st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None));
    assert (pure ('st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None));
    assert (pure ('st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
    assert (pure (U64.fits
      ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    assert (pure (Some? 'st0.CS.cs_model.CS.model_config.CS.config_server));
    let server_cfg =
      Ghost.hide (Some?.v 'st0.CS.cs_model.CS.model_config.CS.config_server);
    assert (pure (
      'st0.CS.cs_model.CS.model_config.CS.config_server ==
        Some (Ghost.reveal server_cfg)));
    assert (pure (
      B.length (Ghost.reveal server_cfg).CS.server_certificate_chain <=
        Bounds.max_server_certificate_chain_len));
    // Transcript-length bound restored: can_send_certificate_runtime exposes
    // send_certificate_ready ==> |transcript| + 13 + |chain| <= max_transcript_len,
    // and we are on the send_certificate_ready branch.  (The legal_event
    // (M.Certificate cert) obligation stays a caller obligation, discharged at
    // the send site with the build-direction witness.)
    assert (pure (
      B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 13 +
        B.length (Ghost.reveal server_cfg).CS.server_certificate_chain <=
          Bounds.max_transcript_len));
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSendCertificate;
      ST.next_local_payload = ST.LocalPayloadNone;
    }
  } else if sign_certificate_verify_ready {
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerEncryptedFlightSent));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure ('st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None));
    assert (pure ('st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None));
    assert (pure (
      'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None));
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSignCertificateVerify;
      ST.next_local_payload = ST.LocalPayloadNone;
    }
  } else if send_certificate_verify_ready {
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerEncryptedFlightSent));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure ('st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
    assert (pure (U64.fits
      ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    let cv = Ghost.hide (Some?.v
      'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
    // Transcript-length bound restored: can_send_certificate_verify_runtime exposes
    // send_certificate_verify_ready ==> |transcript| + 8 + |signature| <= max_transcript_len,
    // and we are on the send_certificate_verify_ready branch.
    assert (pure (
      B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 8 +
        B.length (Sem.certificateVerify_signature_bytes (Ghost.reveal cv)) <=
          Bounds.max_transcript_len));
    assert (pure (CS.legal_event
      'st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
      })));
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSendCertificateVerify;
      ST.next_local_payload = ST.LocalPayloadNone;
    }
  } else if send_server_finished_ready {
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerEncryptedFlightSent));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure ('st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
    assert (pure (U64.fits
      ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    assert (pure (
      B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
        Bounds.max_transcript_len));
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSendServerFinished;
      ST.next_local_payload = ST.LocalPayloadNone;
    }
  } else if server_application_write_keys_ready {
    assert (pure (control.CR.snapshot_control_tag == 1uy));
    assert (pure (control.CR.snapshot_handshake_stage_tag == 16uy));
    assert (pure (U8.v control.CR.snapshot_control_tag == 1));
    assert (pure (U8.v control.CR.snapshot_handshake_stage_tag == 16));
    assert_norm (Tags.handshake_stage_tag_matches 16uy CS.HsServerFinishedSent);
    assert (pure (CR.control_snapshot_matches control 'st0));
    lemma_control_snapshot_matches_hs_server_finished_sent control 'st0;
    assert (pure (keys.CR.snapshot_master_secret_present));
    assert (pure (not keys.CR.snapshot_server_application_traffic_present));
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerFinishedSent));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret));
    assert (pure (not (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)));
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalInstallServerApplicationTrafficKeys;
      ST.next_local_payload = ST.LocalPayloadNone;
    }
  } else if client_application_read_keys_ready {
    assert (pure (control.CR.snapshot_control_tag == 1uy));
    assert (pure (control.CR.snapshot_handshake_stage_tag == 17uy));
    assert (pure (U8.v control.CR.snapshot_control_tag == 1));
    assert (pure (U8.v control.CR.snapshot_handshake_stage_tag == 17));
    assert_norm (Tags.handshake_stage_tag_matches 17uy CS.HsClientFinishedReceived);
    assert (pure (CR.control_snapshot_matches control 'st0));
    lemma_control_snapshot_matches_hs_client_finished_received control 'st0;
    assert (pure (keys.CR.snapshot_master_secret_present));
    assert (pure (not keys.CR.snapshot_client_application_traffic_present));
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientFinishedReceived));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret));
    assert (pure (not (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic)));
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalInstallClientApplicationTrafficKeys;
      ST.next_local_payload = ST.LocalPayloadNone;
    }
  } else if verify_client_finished_ready {
    assert (pure (control.CR.snapshot_control_tag == 1uy));
    assert (pure (control.CR.snapshot_handshake_stage_tag == 17uy));
    assert (pure (U8.v control.CR.snapshot_control_tag == 1));
    assert (pure (U8.v control.CR.snapshot_handshake_stage_tag == 17));
    assert_norm (Tags.handshake_stage_tag_matches 17uy CS.HsClientFinishedReceived);
    assert (pure (CR.control_snapshot_matches control 'st0));
    assert (pure (Tags.control_state_matches
      control.CR.snapshot_control_tag
      control.CR.snapshot_handshake_stage_tag
      control.CR.snapshot_failure_present
      control.CR.snapshot_failure_code
      control.CR.snapshot_failure_alert
      'st0.CS.cs_model.CS.model_control));
    lemma_control_snapshot_matches_hs_client_finished_received control 'st0;
    assert (pure (keys.CR.snapshot_client_handshake_traffic_present));
    assert (pure (keys.CR.snapshot_client_application_traffic_present));
    assert (pure (keys.CR.snapshot_server_application_traffic_present));
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientFinishedReceived));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
    unfold (connection_exactly s 'st0);
    let verify_ready = CQ.can_verify_client_finished_runtime s;
    fold (connection_exactly s 'st0);
    if verify_ready {
      assert (pure (Some?
        'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
      // Restated (provable) conjuncts of CM.can_verify_client_finished plus the
      // transcript-length bound restored via can_verify_client_finished_runtime
      // (verify_ready ==> |transcript| + 36 <= max_transcript_len; we are on the
      // verify_ready branch).  Together these discharge ST.next_local_action_sound
      // for LocalVerifyClientFinished.
      assert (pure (ST.server_local_event_input_ready
        'st0
        ST.LocalVerifyClientFinished
        B.empty));
      assert (pure (
        B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
          Bounds.max_transcript_len));
      {
        ST.next_local_ready = true;
        ST.next_local_kind = ST.LocalVerifyClientFinished;
        ST.next_local_payload = ST.LocalPayloadNone;
      }
    } else {
      {
        ST.next_local_ready = false;
        ST.next_local_kind = ST.LocalFail;
        ST.next_local_payload = ST.LocalPayloadNone;
      }
    }
  } else if key_update_response_ready {
    // RFC 8446 4.6.3: a received KeyUpdate with update_requested obliges us to
    // send our own update_not_requested.  server_key_update_response_ready_runtime
    // exposes exactly the conjuncts of next_local_action_sound/LocalSendKeyUpdate.
    assert (pure ('st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure ('st0.CS.cs_model.CS.model_application.CS.app_key_update_response_pending));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSendKeyUpdate;
      ST.next_local_payload = ST.LocalPayloadNone;
    }
  } else {
    {
      ST.next_local_ready = false;
      ST.next_local_kind = ST.LocalFail;
      ST.next_local_payload = ST.LocalPayloadNone;
    }
  }
}

#pop-options