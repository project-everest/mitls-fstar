module TLS13.Impl.Server

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module CM = TLS13.Impl.ConnectionState.Model
module CF = TLS13.Impl.ConnectionState.Fail
module H = TLS13.Handshake.Spec
module CLA = TLS13.Impl.ConnectionState.LocalAuth
module CLH = TLS13.Impl.ConnectionState.LocalHandshake
module CLS = TLS13.Impl.ConnectionState.LocalSend
module CN = TLS13.Impl.ConnectionState.Network
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module KS = TLS13.KeySchedule
module List = FStar.List.Tot
module M = TLS13.Messages
module O = TLS13.OpenSSL
module P = TLS13.Impl.Parser
module R = TLS13.Record.Spec
module Ser = TLS13.Impl.Serializer
module SM = TLS13.StateMachine
module SSetup = TLS13.Impl.Server.Setup
module SA = TLS13.Impl.Server.Auth
module SS = TLS13.Impl.Server.Send
module SN = TLS13.Impl.Server.Network
module SK = TLS13.Impl.Server.Keys
module ST = TLS13.Impl.Server.Types
module Tags = TLS13.Impl.ConnectionState.Tags
module T = TLS13.Types
module Tr = TLS13.Transcript
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec

fn new_server
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (credential_identity:array U8.t)
  (credential_identity_len:SZ.t)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to credential_identity 'credential_identity_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'credential_identity_bytes == SZ.v credential_identity_len /\
                 B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len)
  returns s:server
  ensures pts_to certificate_chain 'certificate_chain_bytes **
          pts_to credential_identity 'credential_identity_bytes **
          connection_exactly
            s
            (CR.server_initial_state
              (Ghost.reveal 'certificate_chain_bytes)
              (Ghost.reveal 'credential_identity_bytes)) **
          pure (ST.server_state_correct
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                ST.server_end_to_end_invariant
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                ST.server_raw_to_message_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                CS.connection_state_sent_seal_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                CS.connection_state_received_decode_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                CS.connection_state_protected_raw_segmented_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)))
{
  let s =
    CR.new_server
      certificate_chain
      certificate_chain_len
      credential_identity
      credential_identity_len;
  ST.lemma_initial_server_state_correct
    (CR.server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes));
  ST.lemma_initial_server_end_to_end_invariant
    (CR.server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CR.server_initial_state
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes));
  CSL.lemma_initial_sent_seal_replay_consistent
    (CR.server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes));
  CSL.lemma_initial_received_decode_replay_consistent
    (CR.server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes));
  ST.lemma_server_state_correct_protected_raw_segmented_replay
    (CR.server_initial_state
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes));
  fold (connection_exactly
    s
    (CR.server_initial_state
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes)));
  s
}

fn next_local_action
  (s:server)
  requires connection_exactly s 'st0 **
           pure (ST.server_state_correct 'st0)
  returns action:ST.next_local_action
  ensures connection_exactly s 'st0 **
          pure (ST.server_state_correct 'st0 /\
                next_local_action_sound 'st0 action)
{
  unfold (connection_exactly s 'st0);
  let control = CQ.get_control_snapshot s;
  let keys = CQ.get_key_schedule_snapshot s;
  let start_ready = CQ.can_start_server_runtime s;
  let send_encrypted_extensions_ready = CQ.can_send_encrypted_extensions_runtime s;
  assert (pure (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
    | Some cfg ->
      B.length cfg.CS.server_certificate_chain <=
        Bounds.max_server_certificate_chain_len
    | None -> False));
  let send_certificate_ready = CQ.can_send_certificate_runtime s;
  let sign_certificate_verify_ready = CQ.can_sign_certificate_verify_runtime s;
  let send_certificate_verify_ready = CQ.can_send_certificate_verify_runtime s;
  let send_server_finished_ready = CQ.can_send_server_finished_runtime s;
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
  } else if server_handshake_write_keys_ready {
    assert (pure (control.CR.snapshot_control_tag == 1uy));
    assert (pure (control.CR.snapshot_handshake_stage_tag == 14uy));
    assert_norm (Tags.handshake_stage_tag_matches 14uy CS.HsServerHelloSent);
    assert (pure (CR.control_snapshot_matches control 'st0));
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
    assert_norm (Tags.handshake_stage_tag_matches 14uy CS.HsServerHelloSent);
    assert (pure (CR.control_snapshot_matches control 'st0));
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
          M.TlsHandshake (M.EncryptedExtensions { M.negotiated_alpn = None });
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
    assert (pure (
      B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
        B.length
          (W.serialize_certificate_from_credential
            { M.chain = [(Ghost.reveal server_cfg).CS.server_certificate_chain] }) <=
          Bounds.max_transcript_len));
    assert (pure (CS.legal_event
      'st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value =
          M.TlsHandshake
            (M.Certificate { M.chain = [(Ghost.reveal server_cfg).CS.server_certificate_chain] });
      })));
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
    assert (pure ('st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
    assert (pure (U64.fits
      ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    let cv = Ghost.hide (Some?.v
      'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
    assert (pure (
      B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
        B.length (W.serialize_certificate_verify_from_signature (Ghost.reveal cv)) <=
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
    assert_norm (Tags.handshake_stage_tag_matches 16uy CS.HsServerFinishedSent);
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
    assert_norm (Tags.handshake_stage_tag_matches 17uy CS.HsClientFinishedReceived);
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
  } else {
    {
      ST.next_local_ready = false;
      ST.next_local_kind = ST.LocalFail;
      ST.next_local_payload = ST.LocalPayloadNone;
    }
  }
}

fn process_start_server_local_event
  (s:server)
  (kind:ST.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 kind == ST.LocalStartServer /\
                 Seq.equal (Ghost.reveal 'payload_bytes) B.empty /\
                 CM.can_start_server 'st0)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  kind
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SSetup.connection_exactly s 'st0);
  let resp = SSetup.process_start_server_local_event
    s
    kind
    payload
    payload_len
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SSetup.connection_exactly s st1 **
            pts_to payload 'payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SSetup.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_select_server_parameters
  (s:server)
  (#selection:erased CS.server_handshake_selection)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                  B.length 'old_app_out == SZ.v app_out_len /\
                  ST.server_end_to_end_invariant 'st0 /\
                  CM.can_select_server_parameters 'st0 selection)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.selected_server_parameters_state
                    'st0
                    (Ghost.reveal selection) /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalSelectServerParameters
                   B.empty
                   network_out_bytes
                   app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SSetup.connection_exactly s 'st0);
  let resp = SSetup.process_select_server_parameters
    s
    #selection
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SSetup.connection_exactly s st1 **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SSetup.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_select_default_server_parameters_from_arrays
  (s:server)
  (server_random:array U8.t)
  (server_key_share:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to server_random 'server_random_bytes **
           pts_to server_key_share 'server_key_share_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'server_random_bytes == 32 /\
                 B.length 'server_key_share_bytes == 32 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (let ch =
                    Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello in
                  let cfg =
                    Some?.v 'st0.CS.cs_model.CS.model_config.CS.config_server in
                  let selection = {
                    CS.server_selected_client_hello = ch;
                    CS.server_selected_cipher_suite =
                      T.TLS_CHACHA20_POLY1305_SHA256;
                    CS.server_selected_group = T.X25519;
                    CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
                    CS.server_random = Ghost.reveal 'server_random_bytes;
                    CS.server_key_share_private = None;
                    CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
                    CS.server_selected_credential =
                      cfg.CS.server_credential_identity;
                  } in
                  CM.can_select_server_parameters 'st0 selection))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to server_random 'server_random_bytes **
          pts_to server_key_share 'server_key_share_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (B.length (Ghost.reveal 'server_random_bytes) == 32 /\
                 B.length (Ghost.reveal 'server_key_share_bytes) == 32 ==>
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                        'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some ch, Some cfg ->
                    let selection = {
                      CS.server_selected_client_hello = ch;
                      CS.server_selected_cipher_suite =
                        T.TLS_CHACHA20_POLY1305_SHA256;
                      CS.server_selected_group = T.X25519;
                      CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
                      CS.server_random = Ghost.reveal 'server_random_bytes;
                      CS.server_key_share_private = None;
                      CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
                      CS.server_selected_credential =
                        cfg.CS.server_credential_identity;
                    } in
                    st1 == CM.selected_server_parameters_state 'st0 selection
                  | _ -> True)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSelectServerParameters
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SSetup.connection_exactly s 'st0);
  let resp = SSetup.process_select_default_server_parameters_from_arrays
    s
    server_random
    server_key_share
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SSetup.connection_exactly s st1 **
            pts_to server_random 'server_random_bytes **
            pts_to server_key_share 'server_key_share_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SSetup.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_send_server_hello
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lsh:IM.server_hello)
  (#sh:erased M.server_hello)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           IM.is_valid_server_hello lsh sh **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v raw_len <= SZ.v network_out_len /\
                 Seq.equal
                   (Seq.slice (Ghost.reveal 'old_network_out) 0 (SZ.v raw_len))
                   (Ghost.reveal 'raw_bytes) /\
                 Seq.equal
                   (Ghost.reveal 'fragment_bytes)
                   (W.serialize_handshake (M.ServerHello sh)) /\
                 SZ.v fragment_len <= Bounds.max_server_hello_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CM.can_send_server_hello 'st0 sh (Ghost.reveal 'raw_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_server_hello_state
                    'st0
                    sh
                    (Ghost.reveal 'raw_bytes) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendServerHello
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SS.connection_exactly s 'st0);
  let resp = SS.process_send_server_hello
    s
    raw
    raw_len
    fragment
    fragment_len
    lsh
    #sh
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SS.connection_exactly s st1 **
            pts_to raw 'raw_bytes **
            pts_to fragment 'fragment_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SS.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_send_server_hello_serialized
  (s:server)
  (lsh:IM.server_hello)
  (#sh:erased M.server_hello)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           IM.is_valid_server_hello lsh sh **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 95 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CM.can_send_server_hello
                   'st0
                   sh
                   (CS.serialized_cleartext_tls_message
                     (M.TlsHandshake (M.ServerHello sh))))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                Seq.equal
                  network_out_bytes
                  (CS.serialized_cleartext_tls_message
                    (M.TlsHandshake (M.ServerHello sh))) /\
                st1 ==
                  CM.sent_server_hello_state
                    'st0
                    sh
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendServerHello
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SS.connection_exactly s 'st0);
  let resp = SS.process_send_server_hello_serialized
        s
        lsh
        #sh
        network_out
        network_out_len
        app_out
        app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SS.connection_exactly s st1 **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SS.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_send_server_hello_from_arrays
  (s:server)
  (server_random:array U8.t)
  (server_key_share:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to server_random 'server_random_bytes **
           pts_to server_key_share 'server_key_share_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'server_random_bytes == 32 /\
                 B.length 'server_key_share_bytes == 32 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 95 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 (let sh = {
                   M.random = Ghost.reveal 'server_random_bytes;
                   M.key_share = Ghost.reveal 'server_key_share_bytes;
                   M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
                 } in
                 CM.can_send_server_hello
                   'st0
                   sh
                   (CS.serialized_cleartext_tls_message
                     (M.TlsHandshake (M.ServerHello sh)))))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to server_random 'server_random_bytes **
          pts_to server_key_share 'server_key_share_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (B.length (Ghost.reveal 'server_random_bytes) == 32 /\
                 B.length (Ghost.reveal 'server_key_share_bytes) == 32 ==>
                 (let sh = {
                    M.random = Ghost.reveal 'server_random_bytes;
                    M.key_share = Ghost.reveal 'server_key_share_bytes;
                    M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
                  } in
                  Seq.equal
                    network_out_bytes
                    (CS.serialized_cleartext_tls_message
                      (M.TlsHandshake (M.ServerHello sh))) /\
                  st1 ==
                    CM.sent_server_hello_state
                      'st0
                      sh
                      network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendServerHello
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SS.connection_exactly s 'st0);
  let resp = SS.process_send_server_hello_from_arrays
    s
    server_random
    server_key_share
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SS.connection_exactly s st1 **
            pts_to server_random 'server_random_bytes **
            pts_to server_key_share 'server_key_share_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SS.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_send_encrypted_extensions_serialized
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 28 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerHelloSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 6 <=
                   Bounds.max_transcript_len /\
                 CS.legal_event
                   'st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Sent;
                     CL.message_value =
                       M.TlsHandshake
                         (M.EncryptedExtensions { M.negotiated_alpn = None });
                   }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (let ee = { M.negotiated_alpn = None } in
                 st1 ==
                   CM.sent_encrypted_extensions_state
                     'st0
                     ee
                     network_out_bytes) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendEncryptedExtensions
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SS.connection_exactly s 'st0);
  let resp = SS.process_send_encrypted_extensions_serialized
    s
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SS.connection_exactly s st1 **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SS.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_send_certificate_serialized
  (s:server)
  (lcert:IM.certificate_msg)
  (#cert:erased M.certificate_msg)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           IM.is_valid_certificate_msg lcert cert **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v fragment_len ==
                   B.length
                     (TLS13.Wire.Spec.serialize_certificate_from_credential
                       (Ghost.reveal cert)) /\
                 SZ.v fragment_len + 17 <= 16640 /\
                 SZ.v network_out_len == SZ.v fragment_len + 22 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
                 (Ghost.reveal cert).M.chain <> [] /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some cfg -> CS.certificate_msg_matches_server_config cfg (Ghost.reveal cert)
                  | None -> False) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   SZ.v fragment_len <= Bounds.max_transcript_len /\
                 CS.legal_event
                   'st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Sent;
                     CL.message_value =
                       M.TlsHandshake (M.Certificate (Ghost.reveal cert));
                   }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_certificate_state
                    'st0
                    (Ghost.reveal cert)
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificate
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SS.connection_exactly s 'st0);
  let resp = SS.process_send_certificate_serialized
    s
    lcert
    #cert
    fragment_len
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SS.connection_exactly s st1 **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SS.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_send_certificate_from_credentials
  (s:server)
  (creds:O.server_credentials)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           O.is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
                 Some?
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                  ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 13 + B.length (Ghost.reveal 'certificate_chain) + 17 <= 16640 /\
                 SZ.v network_out_len ==
                  13 + B.length (Ghost.reveal 'certificate_chain) + 22 /\
                 (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some cfg -> cfg.CS.server_certificate_chain == Ghost.reveal 'certificate_chain
                  | None -> False) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                  13 + B.length (Ghost.reveal 'certificate_chain) <=
                    Bounds.max_transcript_len /\
                 CS.legal_event
                  'st0.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Sent;
                    CL.message_value =
                      M.TlsHandshake
                        (M.Certificate { M.chain = [Ghost.reveal 'certificate_chain] });
                  }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          O.is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_certificate_state
                    'st0
                    { M.chain = [Ghost.reveal 'certificate_chain] }
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificate
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SS.connection_exactly s 'st0);
  let resp = SS.process_send_certificate_from_credentials
    s
    creds
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SS.connection_exactly s st1 **
            O.is_server_credentials creds 'certificate_chain 'credential_identity **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SS.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_send_certificate_verify_serialized
  (s:server)
  (lcv:IM.certificate_verify)
  (#cv:erased M.certificate_verify)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           IM.is_valid_certificate_verify lcv cv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v fragment_len ==
                   B.length
                     (TLS13.Wire.Spec.serialize_certificate_verify_from_signature
                       (Ghost.reveal cv)) /\
                 SZ.v fragment_len + 17 <= 16640 /\
                 SZ.v network_out_len == SZ.v fragment_len + 22 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                  | Some stored_cv -> stored_cv == Ghost.reveal cv
                  | None -> False) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   SZ.v fragment_len <= Bounds.max_transcript_len /\
                 CS.legal_event
                   'st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Sent;
                     CL.message_value =
                       M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
                   }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_certificate_verify_state
                    'st0
                    (Ghost.reveal cv)
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificateVerify
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SS.connection_exactly s 'st0);
  let resp = SS.process_send_certificate_verify_serialized
    s
    lcv
    #cv
    fragment_len
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SS.connection_exactly s st1 **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SS.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_send_stored_certificate_verify_serialized
  (s:server)
  (#cv:erased M.certificate_verify)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                  B.length 'old_app_out == SZ.v app_out_len /\
                  SZ.v fragment_len ==
                    B.length
                      (TLS13.Wire.Spec.serialize_certificate_verify_from_signature
                        (Ghost.reveal cv)) /\
                  SZ.v fragment_len + 17 <= 16640 /\
                  SZ.v network_out_len == SZ.v fragment_len + 22 /\
                  ST.server_end_to_end_invariant 'st0 /\
                  'st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                  'st0.CS.cs_model.CS.model_config.CS.config_role ==
                    CS.ServerEndpoint /\
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
                  Some?
                    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                  U64.fits
                    ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
                    Some (Ghost.reveal cv) /\
                  B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v fragment_len <= Bounds.max_transcript_len /\
                  CS.legal_event
                    'st0.CS.cs_model
                    (CS.ConnNetworkEvent {
                      CL.message_direction = CL.Sent;
                      CL.message_value =
                        M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
                    }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_certificate_verify_state
                    'st0
                    (Ghost.reveal cv)
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalSendCertificateVerify
                   B.empty
                   network_out_bytes
                   app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SS.connection_exactly s 'st0);
  let resp = SS.process_send_stored_certificate_verify_serialized
    s
    #cv
    fragment_len
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SS.connection_exactly s st1 **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SS.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_send_server_finished_serialized
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 58 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                   Bounds.max_transcript_len)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (match
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic
                 with
                 | Some server_hs ->
                   let fin = {
                     M.verify_data =
                       K.finished_verify_data
                         server_hs.CS.traffic_secret
                         (Tr.hash
                           'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
                   } in
                   st1 ==
                     CM.sent_server_finished_state
                       'st0
                       fin
                       network_out_bytes
                 | None -> True) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendServerFinished
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SS.connection_exactly s 'st0);
  let resp = SS.process_send_server_finished_serialized
    s
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SS.connection_exactly s st1 **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SS.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_derive_shared_secret
  (s:server)
  (shared_src:array U8.t)
  (#shared:erased TLS13.Crypto.Spec.x25519_shared_secret)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to shared_src shared **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length (Ghost.reveal shared) == 32 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CS.legal_event
                    'st0.CS.cs_model
                    (CS.ConnLocalEvent
                      (CS.LocalDeriveSharedSecret (Ghost.reveal shared))))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to shared_src shared **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.derived_shared_secret_state
                    'st0
                    (Ghost.reveal shared) /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalDeriveSharedSecret
                   (Ghost.reveal shared)
                   network_out_bytes
                   app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SK.connection_exactly s 'st0);
  let resp = SK.process_derive_shared_secret
    s
    shared_src
    #shared
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SK.connection_exactly s st1 **
            pts_to shared_src shared **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SK.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_install_server_handshake_write_keys
  (s:server)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to traffic_secret_src material.CS.traffic_secret **
           pts_to traffic_key_src material.CS.traffic_key **
           pts_to traffic_iv_src material.CS.traffic_iv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CS.legal_event
                    'st0.CS.cs_model
                    (CS.ConnLocalEvent
                      (CS.LocalInstallTrafficKeysForRole {
                        CS.install_role = CS.ServerEndpoint;
                        CS.install_payload = {
                          CS.install_epoch = CS.TrafficHandshake;
                          CS.install_direction = CS.TrafficWrite;
                          CS.install_material = Ghost.reveal material;
                        };
                      })))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to traffic_secret_src material.CS.traffic_secret **
          pts_to traffic_key_src material.CS.traffic_key **
          pts_to traffic_iv_src material.CS.traffic_iv **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.installed_traffic_keys_for_role_state 'st0 {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficHandshake;
                      CS.install_direction = CS.TrafficWrite;
                      CS.install_material = Ghost.reveal material;
                    };
                  } /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalInstallServerHandshakeTrafficKeys
                   B.empty
                   network_out_bytes
                   app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SK.connection_exactly s 'st0);
  let resp = SK.process_install_server_handshake_write_keys
    s
    traffic_secret_src
    traffic_key_src
    traffic_iv_src
    #material
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SK.connection_exactly s st1 **
            pts_to traffic_secret_src material.CS.traffic_secret **
            pts_to traffic_key_src material.CS.traffic_key **
            pts_to traffic_iv_src material.CS.traffic_iv **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SK.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_derive_and_install_server_handshake_write_keys
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                   B.length 'old_app_out == SZ.v app_out_len /\
                   ST.server_end_to_end_invariant 'st0 /\
                   'st0.CS.cs_model.CS.model_control ==
                     CS.ControlHandshaking CS.HsServerHelloSent /\
                   'st0.CS.cs_model.CS.model_config.CS.config_role ==
                     CS.ServerEndpoint /\
                   Some?
                     'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
  returns resp:ST.server_response
  ensures exists* network_out_bytes app_out_bytes material.
          connection_exactly
            s
            (CM.installed_traffic_keys_for_role_state 'st0 {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = material;
              };
            }) **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                     'st0
                     (CM.installed_traffic_keys_for_role_state 'st0 {
                       CS.install_role = CS.ServerEndpoint;
                       CS.install_payload = {
                         CS.install_epoch = CS.TrafficHandshake;
                         CS.install_direction = CS.TrafficWrite;
                         CS.install_material = material;
                       };
                     })
                     resp
                     ST.LocalInstallServerHandshakeTrafficKeys
                     B.empty
                     network_out_bytes
                     app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SK.connection_exactly s 'st0);
  let resp = SK.process_derive_and_install_server_handshake_write_keys
    s
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SK.connection_exactly s st1 **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SK.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_install_client_handshake_read_keys
  (s:server)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to traffic_secret_src material.CS.traffic_secret **
           pts_to traffic_key_src material.CS.traffic_key **
           pts_to traffic_iv_src material.CS.traffic_iv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                   B.length 'old_app_out == SZ.v app_out_len /\
                   ST.server_end_to_end_invariant 'st0 /\
                   CS.legal_event
                      'st0.CS.cs_model
                      (CS.ConnLocalEvent
                        (CS.LocalInstallTrafficKeysForRole {
                          CS.install_role = CS.ServerEndpoint;
                          CS.install_payload = {
                            CS.install_epoch = CS.TrafficHandshake;
                            CS.install_direction = CS.TrafficRead;
                            CS.install_material = Ghost.reveal material;
                          };
                        })))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to traffic_secret_src material.CS.traffic_secret **
          pts_to traffic_key_src material.CS.traffic_key **
          pts_to traffic_iv_src material.CS.traffic_iv **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.installed_traffic_keys_for_role_state 'st0 {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficHandshake;
                      CS.install_direction = CS.TrafficRead;
                      CS.install_material = Ghost.reveal material;
                    };
                  } /\
                ST.server_local_event_end_to_end_correct
                     'st0
                     st1
                     resp
                     ST.LocalInstallClientHandshakeTrafficKeys
                     B.empty
                     network_out_bytes
                     app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SK.connection_exactly s 'st0);
  let resp = SK.process_install_client_handshake_read_keys
    s
    traffic_secret_src
    traffic_key_src
    traffic_iv_src
    #material
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SK.connection_exactly s st1 **
            pts_to traffic_secret_src material.CS.traffic_secret **
            pts_to traffic_key_src material.CS.traffic_key **
            pts_to traffic_iv_src material.CS.traffic_iv **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SK.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_derive_and_install_client_handshake_read_keys
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                     B.length 'old_app_out == SZ.v app_out_len /\
                     ST.server_end_to_end_invariant 'st0 /\
                     'st0.CS.cs_model.CS.model_control ==
                       CS.ControlHandshaking CS.HsServerHelloSent /\
                     'st0.CS.cs_model.CS.model_config.CS.config_role ==
                       CS.ServerEndpoint /\
                     Some?
                       'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
  returns resp:ST.server_response
  ensures exists* network_out_bytes app_out_bytes material.
          connection_exactly
            s
            (CM.installed_traffic_keys_for_role_state 'st0 {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = material;
              };
            }) **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                       'st0
                       (CM.installed_traffic_keys_for_role_state 'st0 {
                         CS.install_role = CS.ServerEndpoint;
                         CS.install_payload = {
                           CS.install_epoch = CS.TrafficHandshake;
                           CS.install_direction = CS.TrafficRead;
                           CS.install_material = material;
                         };
                       })
                       resp
                       ST.LocalInstallClientHandshakeTrafficKeys
                       B.empty
                       network_out_bytes
                       app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SK.connection_exactly s 'st0);
  let resp = SK.process_derive_and_install_client_handshake_read_keys
    s
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SK.connection_exactly s st1 **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SK.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_install_server_application_write_keys
  (s:server)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to traffic_secret_src material.CS.traffic_secret **
           pts_to traffic_key_src material.CS.traffic_key **
           pts_to traffic_iv_src material.CS.traffic_iv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CS.legal_event
                        'st0.CS.cs_model
                        (CS.ConnLocalEvent
                          (CS.LocalInstallTrafficKeysForRole {
                            CS.install_role = CS.ServerEndpoint;
                            CS.install_payload = {
                              CS.install_epoch = CS.TrafficApplication;
                              CS.install_direction = CS.TrafficWrite;
                              CS.install_material = Ghost.reveal material;
                            };
                          })))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to traffic_secret_src material.CS.traffic_secret **
          pts_to traffic_key_src material.CS.traffic_key **
          pts_to traffic_iv_src material.CS.traffic_iv **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.installed_traffic_keys_for_role_state 'st0 {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficApplication;
                      CS.install_direction = CS.TrafficWrite;
                      CS.install_material = Ghost.reveal material;
                    };
                  } /\
                ST.server_local_event_end_to_end_correct
                       'st0
                       st1
                       resp
                       ST.LocalInstallServerApplicationTrafficKeys
                       B.empty
                       network_out_bytes
                       app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SK.connection_exactly s 'st0);
  let resp = SK.process_install_server_application_write_keys
    s
    traffic_secret_src
    traffic_key_src
    traffic_iv_src
    #material
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SK.connection_exactly s st1 **
            pts_to traffic_secret_src material.CS.traffic_secret **
            pts_to traffic_key_src material.CS.traffic_key **
            pts_to traffic_iv_src material.CS.traffic_iv **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SK.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_install_client_application_read_keys
  (s:server)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to traffic_secret_src material.CS.traffic_secret **
           pts_to traffic_key_src material.CS.traffic_key **
           pts_to traffic_iv_src material.CS.traffic_iv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CS.legal_event
                        'st0.CS.cs_model
                        (CS.ConnLocalEvent
                          (CS.LocalInstallTrafficKeysForRole {
                            CS.install_role = CS.ServerEndpoint;
                            CS.install_payload = {
                              CS.install_epoch = CS.TrafficApplication;
                              CS.install_direction = CS.TrafficRead;
                              CS.install_material = Ghost.reveal material;
                            };
                          })))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to traffic_secret_src material.CS.traffic_secret **
          pts_to traffic_key_src material.CS.traffic_key **
          pts_to traffic_iv_src material.CS.traffic_iv **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.installed_traffic_keys_for_role_state 'st0 {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficApplication;
                      CS.install_direction = CS.TrafficRead;
                      CS.install_material = Ghost.reveal material;
                    };
                  } /\
                ST.server_local_event_end_to_end_correct
                       'st0
                       st1
                       resp
                       ST.LocalInstallClientApplicationTrafficKeys
                       B.empty
                       network_out_bytes
                       app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SK.connection_exactly s 'st0);
  let resp = SK.process_install_client_application_read_keys
    s
    traffic_secret_src
    traffic_key_src
    traffic_iv_src
    #material
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SK.connection_exactly s st1 **
            pts_to traffic_secret_src material.CS.traffic_secret **
            pts_to traffic_key_src material.CS.traffic_key **
            pts_to traffic_iv_src material.CS.traffic_iv **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SK.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_derive_and_install_server_application_write_keys
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerFinishedSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret)
  returns resp:ST.server_response
  ensures exists* network_out_bytes app_out_bytes material.
          connection_exactly
            s
            (CM.installed_traffic_keys_for_role_state 'st0 {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = material;
              };
            }) **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                        'st0
                        (CM.installed_traffic_keys_for_role_state 'st0 {
                          CS.install_role = CS.ServerEndpoint;
                          CS.install_payload = {
                            CS.install_epoch = CS.TrafficApplication;
                            CS.install_direction = CS.TrafficWrite;
                            CS.install_material = material;
                          };
                        })
                        resp
                        ST.LocalInstallServerApplicationTrafficKeys
                        B.empty
                        network_out_bytes
                        app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SK.connection_exactly s 'st0);
  let resp = SK.process_derive_and_install_server_application_write_keys
    s
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SK.connection_exactly s st1 **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SK.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_derive_and_install_client_application_read_keys
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsClientFinishedReceived /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret)
  returns resp:ST.server_response
  ensures exists* network_out_bytes app_out_bytes material.
          connection_exactly
            s
            (CM.installed_traffic_keys_for_role_state 'st0 {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = material;
              };
            }) **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                        'st0
                        (CM.installed_traffic_keys_for_role_state 'st0 {
                          CS.install_role = CS.ServerEndpoint;
                          CS.install_payload = {
                            CS.install_epoch = CS.TrafficApplication;
                            CS.install_direction = CS.TrafficRead;
                            CS.install_material = material;
                          };
                        })
                        resp
                        ST.LocalInstallClientApplicationTrafficKeys
                        B.empty
                        network_out_bytes
                        app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SK.connection_exactly s 'st0);
  let resp = SK.process_derive_and_install_client_application_read_keys
    s
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SK.connection_exactly s st1 **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SK.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_send_application_data_local_event
  (s:server)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 server_local_event_input_ready
                   'st0
                   ST.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (resp.status == ST.StepOk ==>
                  exists raw_sent.
                    st1 ==
                      CM.sent_application_data_state
                        'st0
                        (Ghost.reveal 'payload_bytes)
                        raw_sent /\
                    Seq.equal
                      raw_sent
                      (ST.response_network_out resp network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendApplicationData
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  let ok =
    CLS.try_send_application_data
      s
      payload
      payload_len
      network_out
      network_out_len;
  if ok {
    with raw_sent network_out_bytes.
      assert (pts_to network_out network_out_bytes);
    assert (CR.connection_exactly
      s
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent));
    fold (connection_exactly
      s
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent));
    assert (pure (B.length network_out_bytes == SZ.v network_out_len));
    assert (pure (SZ.v payload_len + 22 <= B.length network_out_bytes));
    assert (pure (CM.can_send_application_data
      'st0
      (Ghost.reveal 'payload_bytes)
      raw_sent));
    assert (pure (Seq.equal
      raw_sent
      (Seq.slice network_out_bytes 0 (SZ.v payload_len + 22))));
    assert (pure (SZ.fits (SZ.v payload_len + 22)));
    let written_len = SZ.add payload_len 22sz;
    assert (pure (SZ.v written_len == SZ.v payload_len + 22));
    let resp = {
      ST.network_out_len = written_len;
      ST.app_out_len = 0sz;
      ST.status = ST.StepOk;
    };
    Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_len);
    assert (pure (Seq.equal raw_sent (ST.response_network_out resp network_out_bytes)));
    Seq.lemma_len_slice 'old_app_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
    CM.lemma_sent_application_data_state_evolves
      'st0
      (Ghost.reveal 'payload_bytes)
      raw_sent;

    let ev = Ghost.hide (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsApplicationData (Ghost.reveal 'payload_bytes);
    });
    let delta = Ghost.hide {
      CS.delta_event = Ghost.reveal ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = B.empty;
    };
    assert (pure (CS.legal_connection_delta
      'st0
      (Ghost.reveal delta)
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)));
    CSL.lemma_legal_connection_delta_full_log_consistent_for_role
      CS.ServerEndpoint
      'st0
      (Ghost.reveal delta)
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent);
    CSL.lemma_legal_connection_delta_raw_event_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent);
    CSL.lemma_connection_state_protected_raw_segmented_replay
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent);
    CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent);
    CSL.lemma_legal_connection_delta_received_decode_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent);
    CSL.lemma_event_raw_delta_legal_protected_segmented
      'st0.CS.cs_model
      (Ghost.reveal ev)
      raw_sent
      B.empty;
    assert (pure (CS.event_protected_raw_segmented_success
      (Ghost.reveal ev)
      raw_sent
      B.empty));
    assert (pure (CS.connection_state_record_keys_consistent_for_role
      CS.ServerEndpoint
      'st0));
    assert (pure (CS.model_record_keys_consistent_for_role
      CS.ServerEndpoint
      'st0.CS.cs_model));
    assert (pure (CS.record_write_key_schedule_projection_for_role
      CS.ServerEndpoint
      'st0.CS.cs_model));

    assert (pure ((CM.sent_application_data_state
      'st0
      (Ghost.reveal 'payload_bytes)
      raw_sent).CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    assert (pure ((CM.sent_application_data_state
      'st0
      (Ghost.reveal 'payload_bytes)
      raw_sent).CS.cs_model.CS.model_config.CS.config_role ==
      CS.ServerEndpoint));
    assert (pure (Some?
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent).CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (ST.server_state_correct
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)));
    assert (pure (ST.server_raw_to_message_replay_consistent
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)));
    assert (pure (ST.server_end_to_end_invariant
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)));

    assert (pure (ST.legal_response_for_event
      'st0
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)
      resp
      (Ghost.reveal ev)
      raw_sent
      B.empty
      network_out_bytes
      'old_app_out));
    assert (pure (ST.legal_local_response
      'st0
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)
      resp
      ST.LocalSendApplicationData
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal ev)
      raw_sent
      B.empty
      network_out_bytes
      'old_app_out));
    assert (pure (ST.legal_handled_local_response
      'st0
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)
      resp
      ST.LocalSendApplicationData
      (Ghost.reveal 'payload_bytes)
      network_out_bytes
      'old_app_out));
    assert (pure (ST.server_local_event_end_to_end_correct
      'st0
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)
      resp
      ST.LocalSendApplicationData
      (Ghost.reveal 'payload_bytes)
      network_out_bytes
      'old_app_out));
    resp
  } else {
    CF.mark_unexpected_message s;
    fold (connection_exactly s (CM.local_fail_state 'st0 CM.tls_unexpected_message_error));
    let resp = {
      ST.network_out_len = 0sz;
      ST.app_out_len = 0sz;
      ST.status = ST.IllegalTransition;
    };
    Seq.lemma_len_slice 'old_network_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
    Seq.lemma_len_slice 'old_app_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
    CM.lemma_local_fail_state_evolves 'st0 CM.tls_unexpected_message_error;
    let delta = Ghost.hide {
      CS.delta_event =
        CS.ConnLocalEvent (CS.LocalFail CM.tls_unexpected_message_error);
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    };
    CSL.lemma_legal_connection_delta_full_log_consistent_for_role
      CS.ServerEndpoint
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_legal_connection_delta_raw_event_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_connection_state_protected_raw_segmented_replay
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_legal_connection_delta_received_decode_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    assert (pure ((CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    assert (pure ((CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config.CS.config_role ==
      CS.ServerEndpoint));
    assert (pure (Some?
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (ST.server_state_correct
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
    assert (pure (ST.server_raw_to_message_replay_consistent
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
    assert (pure (ST.server_end_to_end_invariant
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
    assert (pure (ST.unexpected_message_response
      'st0
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
      resp
      'old_network_out
      'old_app_out));
    assert (pure (ST.legal_handled_local_response
      'st0
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
      resp
      ST.LocalSendApplicationData
      (Ghost.reveal 'payload_bytes)
      'old_network_out
      'old_app_out));
    assert (pure (ST.server_local_event_end_to_end_correct
      'st0
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
      resp
      ST.LocalSendApplicationData
      (Ghost.reveal 'payload_bytes)
      'old_network_out
      'old_app_out));
    resp
  }
}

fn process_send_close_notify_local_event
  (s:server)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 server_local_event_input_ready
                   'st0
                   ST.LocalSendCloseNotify
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (resp.status == ST.StepOk ==>
                  exists raw_sent.
                    st1 ==
                      CM.sent_close_notify_state
                        'st0
                        raw_sent /\
                    Seq.equal
                      raw_sent
                      (ST.response_network_out resp network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCloseNotify
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  let ok =
    CLS.try_send_close_notify
      s
      network_out
      network_out_len;
  if ok {
    with raw_sent network_out_bytes.
      assert (pts_to network_out network_out_bytes);
    assert (CR.connection_exactly
      s
      (CM.sent_close_notify_state 'st0 raw_sent));
    fold (connection_exactly
      s
      (CM.sent_close_notify_state 'st0 raw_sent));
    assert (pure (B.length network_out_bytes == SZ.v network_out_len));
    assert (pure (24 <= B.length network_out_bytes));
    assert (pure (CM.can_send_close_notify 'st0 raw_sent));
    assert (pure (Seq.equal raw_sent (Seq.slice network_out_bytes 0 24)));
    let resp = {
      ST.network_out_len = 24sz;
      ST.app_out_len = 0sz;
      ST.status = ST.StepOk;
    };
    Seq.lemma_len_slice network_out_bytes 0 24;
    assert (pure (Seq.equal raw_sent (ST.response_network_out resp network_out_bytes)));
    Seq.lemma_len_slice 'old_app_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
    CM.lemma_sent_close_notify_state_evolves 'st0 raw_sent;

    let ev = Ghost.hide (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsAlert T.CloseNotify;
    });
    let delta = Ghost.hide {
      CS.delta_event = Ghost.reveal ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = B.empty;
    };
    assert (pure (CS.legal_connection_delta
      'st0
      (Ghost.reveal delta)
      (CM.sent_close_notify_state 'st0 raw_sent)));
    CSL.lemma_legal_connection_delta_full_log_consistent_for_role
      CS.ServerEndpoint
      'st0
      (Ghost.reveal delta)
      (CM.sent_close_notify_state 'st0 raw_sent);
    CSL.lemma_legal_connection_delta_raw_event_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.sent_close_notify_state 'st0 raw_sent);
    CSL.lemma_connection_state_protected_raw_segmented_replay
      (CM.sent_close_notify_state 'st0 raw_sent);
    CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.sent_close_notify_state 'st0 raw_sent);
    CSL.lemma_legal_connection_delta_received_decode_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.sent_close_notify_state 'st0 raw_sent);
    CSL.lemma_event_raw_delta_legal_protected_segmented
      'st0.CS.cs_model
      (Ghost.reveal ev)
      raw_sent
      B.empty;
    assert (pure (CS.event_protected_raw_segmented_success
      (Ghost.reveal ev)
      raw_sent
      B.empty));
    assert (pure (CS.connection_state_record_keys_consistent_for_role
      CS.ServerEndpoint
      'st0));
    assert (pure (CS.model_record_keys_consistent_for_role
      CS.ServerEndpoint
      'st0.CS.cs_model));
    assert (pure (CS.record_write_key_schedule_projection_for_role
      CS.ServerEndpoint
      'st0.CS.cs_model));

    assert (pure ((CM.sent_close_notify_state 'st0 raw_sent).CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    assert (pure ((CM.sent_close_notify_state 'st0 raw_sent).CS.cs_model.CS.model_config.CS.config_role ==
      CS.ServerEndpoint));
    assert (pure (Some?
      (CM.sent_close_notify_state 'st0 raw_sent).CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (ST.server_state_correct
      (CM.sent_close_notify_state 'st0 raw_sent)));
    assert (pure (ST.server_raw_to_message_replay_consistent
      (CM.sent_close_notify_state 'st0 raw_sent)));
    assert (pure (ST.server_end_to_end_invariant
      (CM.sent_close_notify_state 'st0 raw_sent)));

    assert (pure (ST.legal_response_for_event
      'st0
      (CM.sent_close_notify_state 'st0 raw_sent)
      resp
      (Ghost.reveal ev)
      raw_sent
      B.empty
      network_out_bytes
      'old_app_out));
    assert (pure (ST.legal_local_response
      'st0
      (CM.sent_close_notify_state 'st0 raw_sent)
      resp
      ST.LocalSendCloseNotify
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal ev)
      raw_sent
      B.empty
      network_out_bytes
      'old_app_out));
    assert (pure (ST.legal_handled_local_response
      'st0
      (CM.sent_close_notify_state 'st0 raw_sent)
      resp
      ST.LocalSendCloseNotify
      (Ghost.reveal 'payload_bytes)
      network_out_bytes
      'old_app_out));
    assert (pure (ST.server_local_event_end_to_end_correct
      'st0
      (CM.sent_close_notify_state 'st0 raw_sent)
      resp
      ST.LocalSendCloseNotify
      (Ghost.reveal 'payload_bytes)
      network_out_bytes
      'old_app_out));
    resp
  } else {
    CF.mark_unexpected_message s;
    fold (connection_exactly s (CM.local_fail_state 'st0 CM.tls_unexpected_message_error));
    let resp = {
      ST.network_out_len = 0sz;
      ST.app_out_len = 0sz;
      ST.status = ST.IllegalTransition;
    };
    Seq.lemma_len_slice 'old_network_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
    Seq.lemma_len_slice 'old_app_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
    CM.lemma_local_fail_state_evolves 'st0 CM.tls_unexpected_message_error;
    let delta = Ghost.hide {
      CS.delta_event =
        CS.ConnLocalEvent (CS.LocalFail CM.tls_unexpected_message_error);
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    };
    CSL.lemma_legal_connection_delta_full_log_consistent_for_role
      CS.ServerEndpoint
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_legal_connection_delta_raw_event_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_connection_state_protected_raw_segmented_replay
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_legal_connection_delta_received_decode_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    assert (pure ((CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    assert (pure ((CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config.CS.config_role ==
      CS.ServerEndpoint));
    assert (pure (Some?
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (ST.server_state_correct
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
    assert (pure (ST.server_raw_to_message_replay_consistent
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
    assert (pure (ST.server_end_to_end_invariant
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
    assert (pure (ST.unexpected_message_response
      'st0
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
      resp
      'old_network_out
      'old_app_out));
    assert (pure (ST.legal_handled_local_response
      'st0
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
      resp
      ST.LocalSendCloseNotify
      (Ghost.reveal 'payload_bytes)
      'old_network_out
      'old_app_out));
    assert (pure (ST.server_local_event_end_to_end_correct
      'st0
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
      resp
      ST.LocalSendCloseNotify
      (Ghost.reveal 'payload_bytes)
      'old_network_out
      'old_app_out));
    resp
  }
}

fn process_verify_client_finished
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished /\
                 CM.can_verify_client_finished
                   'st0
                   (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished))
  returns resp:ST.server_response
  ensures exists* network_out_bytes app_out_bytes fin.
          connection_exactly
            s
            (CM.verified_client_finished_state 'st0 fin) **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
                  Some fin /\
                ST.server_local_event_end_to_end_correct
                        'st0
                        (CM.verified_client_finished_state 'st0 fin)
                        resp
                        ST.LocalVerifyClientFinished
                        B.empty
                        network_out_bytes
                        app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SA.connection_exactly s 'st0);
  let resp = SA.process_verify_client_finished
    s
    network_out
    network_out_len
    app_out
    app_out_len;
  with network_out_bytes app_out_bytes fin.
    assert (SA.connection_exactly s (CM.verified_client_finished_state 'st0 fin) **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite
    (SA.connection_exactly s (CM.verified_client_finished_state 'st0 fin))
    as
    (connection_exactly s (CM.verified_client_finished_state 'st0 fin));
  resp
}

fn process_local_unexpected_message
  (s:server)
  (kind:ST.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  kind
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SA.connection_exactly s 'st0);
  let resp = SA.process_local_unexpected_message
    s
    kind
    payload
    payload_len
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SA.connection_exactly s st1 **
            pts_to payload 'payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SA.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_sign_certificate_verify
  (s:server)
  (creds:O.server_credentials)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           O.is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None /\
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
                  | Some selection ->
                    selection.CS.server_selected_signature_scheme ==
                      T.RsaPssRsaeSha256 /\
                    selection.CS.server_selected_credential ==
                      Ghost.reveal 'credential_identity /\
                    CS.signature_scheme_offered
                      'st0.CS.cs_model.CS.model_config.CS.config_signature_schemes
                      T.RsaPssRsaeSha256
                  | None -> False))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          O.is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSignCertificateVerify
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SA.connection_exactly s 'st0);
  let resp = SA.process_sign_certificate_verify
    s
    creds
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SA.connection_exactly s st1 **
            O.is_server_credentials creds 'certificate_chain 'credential_identity **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SA.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_local_event
  (s:server)
  (kind:ST.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 server_local_event_input_ready
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  kind
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  match kind {
    ST.LocalStartServer -> {
      process_start_server_local_event
        s
        kind
        payload
        payload_len
        network_out
        network_out_len
        app_out
        app_out_len
    }
    ST.LocalInstallServerHandshakeTrafficKeys -> {
      let resp =
        process_derive_and_install_server_handshake_write_keys
          s
          network_out
          network_out_len
          app_out
          app_out_len;
      assert (pure (Seq.equal (Ghost.reveal 'payload_bytes) B.empty));
      resp
    }
    ST.LocalInstallClientHandshakeTrafficKeys -> {
      let resp =
        process_derive_and_install_client_handshake_read_keys
          s
          network_out
          network_out_len
          app_out
          app_out_len;
      assert (pure (Seq.equal (Ghost.reveal 'payload_bytes) B.empty));
      resp
    }
    ST.LocalSelectServerParameters -> {
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
    }
    ST.LocalDeriveSharedSecret -> {
      assert (pure (B.length (Ghost.reveal 'payload_bytes) == 32));
      assert (pure (CS.legal_event
        'st0.CS.cs_model
        (CS.ConnLocalEvent
          (CS.LocalDeriveSharedSecret (Ghost.reveal 'payload_bytes)))));
      let shared : erased TLS13.Crypto.Spec.x25519_shared_secret =
        Ghost.hide (Ghost.reveal 'payload_bytes);
      let resp =
        process_derive_shared_secret
          s
          payload
          #shared
          network_out
          network_out_len
          app_out
          app_out_len;
      resp
    }
    ST.LocalInstallClientApplicationTrafficKeys -> {
      let resp =
        process_derive_and_install_client_application_read_keys
          s
          network_out
          network_out_len
          app_out
          app_out_len;
      assert (pure (Seq.equal (Ghost.reveal 'payload_bytes) B.empty));
      resp
    }
    ST.LocalInstallServerApplicationTrafficKeys -> {
      let resp =
        process_derive_and_install_server_application_write_keys
          s
          network_out
          network_out_len
          app_out
          app_out_len;
      assert (pure (Seq.equal (Ghost.reveal 'payload_bytes) B.empty));
      resp
    }
    ST.LocalSignCertificateVerify -> {
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
    }
    ST.LocalVerifyClientFinished -> {
      let resp =
        process_verify_client_finished
          s
          network_out
          network_out_len
          app_out
          app_out_len;
      assert (pure (Seq.equal (Ghost.reveal 'payload_bytes) B.empty));
      resp
    }
    ST.LocalDeliverApplicationData -> {
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
    }
    ST.LocalSendServerHello -> {
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
    }
    ST.LocalSendEncryptedExtensions -> {
      assert (pure (Seq.equal (Ghost.reveal 'payload_bytes) B.empty));
      if (network_out_len = 28sz) {
        process_send_encrypted_extensions_serialized
          s
          network_out
          network_out_len
          app_out
          app_out_len
      } else {
        process_local_unexpected_message
          s
          kind
          payload
          payload_len
          network_out
          network_out_len
          app_out
          app_out_len
      }
    }
    ST.LocalSendCertificate -> {
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
    }
    ST.LocalSendCertificateVerify -> {
      assert (pure (Seq.equal (Ghost.reveal 'payload_bytes) B.empty));
      assert (pure (Some?
        'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
      let cv : erased M.certificate_verify =
        Ghost.hide (Some?.v
          'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
      assert (pure (
        'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
          Some (Ghost.reveal cv)));
      unfold (connection_exactly s 'st0);
      let snapshot = CQ.get_certificate_verify_signature_snapshot s;
      fold (connection_exactly s 'st0);
      assert (pure (SZ.v snapshot.CR.cv_signature_len <= IM.max_signature_len));
      assert (pure (
        SZ.v snapshot.CR.cv_signature_len ==
          B.length (Ghost.reveal cv).M.signature));
      W.lemma_serialize_certificate_verify_from_signature_len (Ghost.reveal cv);
      assert (pure (
        B.length (W.serialize_certificate_verify_from_signature (Ghost.reveal cv)) ==
          8 + SZ.v snapshot.CR.cv_signature_len));
      assert_norm (IM.max_signature_len == 4096);
      assert (pure (SZ.fits (SZ.v snapshot.CR.cv_signature_len + 8)));
      let fragment_len = SZ.add snapshot.CR.cv_signature_len 8sz;
      assert (pure (
        SZ.v fragment_len ==
          B.length (W.serialize_certificate_verify_from_signature (Ghost.reveal cv))));
      assert (pure (SZ.v fragment_len + 17 <= 16640));
      assert (pure (SZ.fits (SZ.v fragment_len + 22)));
      let expected_network_out_len = SZ.add fragment_len 22sz;
      if (network_out_len = expected_network_out_len) {
        assert (pure (SZ.v network_out_len == SZ.v fragment_len + 22));
        process_send_stored_certificate_verify_serialized
          s
          #cv
          fragment_len
          network_out
          network_out_len
          app_out
          app_out_len
      } else {
        process_local_unexpected_message
          s
          kind
          payload
          payload_len
          network_out
          network_out_len
          app_out
          app_out_len
      }
    }
    ST.LocalSendServerFinished -> {
      assert (pure (Seq.equal (Ghost.reveal 'payload_bytes) B.empty));
      if (network_out_len = 58sz) {
        process_send_server_finished_serialized
          s
          network_out
          network_out_len
          app_out
          app_out_len
      } else {
        process_local_unexpected_message
          s
          kind
          payload
          payload_len
          network_out
          network_out_len
          app_out
          app_out_len
      }
    }
    ST.LocalSendApplicationData -> {
      process_send_application_data_local_event
        s
        payload
        payload_len
        network_out
        network_out_len
        app_out
        app_out_len
    }
    ST.LocalSendCloseNotify -> {
      process_send_close_notify_local_event
        s
        payload
        payload_len
        network_out
        network_out_len
        app_out
        app_out_len
    }
    ST.LocalFail -> {
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
    }
  }
}

fn process_local_event_with_credentials
  (s:server)
  (creds:O.server_credentials)
  (kind:ST.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
         O.is_server_credentials creds 'certificate_chain 'credential_identity **
         pts_to payload 'payload_bytes **
         pts_to network_out 'old_network_out **
         pts_to app_out 'old_app_out **
         pure (B.length 'payload_bytes == SZ.v payload_len /\
               B.length 'old_network_out == SZ.v network_out_len /\
               B.length 'old_app_out == SZ.v app_out_len /\
               ST.server_end_to_end_invariant 'st0 /\
               server_local_event_input_ready_with_credentials
                 'st0
                 kind
                 (Ghost.reveal 'payload_bytes)
                 (Ghost.reveal 'certificate_chain)
                 (Ghost.reveal 'credential_identity))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
        connection_exactly s st1 **
        O.is_server_credentials creds 'certificate_chain 'credential_identity **
        pts_to payload 'payload_bytes **
        pts_to network_out network_out_bytes **
        pts_to app_out app_out_bytes **
        pure (B.length network_out_bytes == SZ.v network_out_len /\
              B.length app_out_bytes == SZ.v app_out_len /\
              ST.server_local_event_end_to_end_correct
                'st0
                st1
                resp
                kind
                (Ghost.reveal 'payload_bytes)
                network_out_bytes
                app_out_bytes)
{
  match kind {
    ST.LocalSendCertificate -> {
      assert (pure (Seq.equal (Ghost.reveal 'payload_bytes) B.empty));
      let built = SS.build_certificate_from_credentials creds;
      match built {
        None -> {
          assert_norm (IM.max_certificate_chain_bytes == 32768);
          assert (pure (
            B.length (Ghost.reveal 'certificate_chain) >
              IM.max_certificate_chain_bytes));
          assert (pure (
            13 + B.length (Ghost.reveal 'certificate_chain) + 17 <= 16640));
          assert (pure False);
          {
            ST.network_out_len = 0sz;
            ST.app_out_len = 0sz;
            ST.status = ST.IllegalTransition;
          }
        }
        Some lcert -> {
          assert (pure (SZ.v lcert.IM.certificate_msg_chain_bytes_len ==
            B.length (Ghost.reveal 'certificate_chain)));
          W.lemma_serialize_certificate_from_single_chain_len
            (Ghost.reveal 'certificate_chain);
          assert (pure (
            B.length
              (W.serialize_certificate_from_credential
                { M.chain = [Ghost.reveal 'certificate_chain] }) ==
              13 + B.length (Ghost.reveal 'certificate_chain)));
          assert (pure (
            SZ.fits (SZ.v lcert.IM.certificate_msg_chain_bytes_len + 13)));
          let fragment_len =
            SZ.add lcert.IM.certificate_msg_chain_bytes_len 13sz;
          assert (pure (SZ.v fragment_len ==
            13 + B.length (Ghost.reveal 'certificate_chain)));
          assert (pure (SZ.fits (SZ.v fragment_len + 22)));
          let expected_network_out_len = SZ.add fragment_len 22sz;
          if (network_out_len = expected_network_out_len) {
            assert (pure (SZ.v network_out_len ==
              13 + B.length (Ghost.reveal 'certificate_chain) + 22));
            IM.free_certificate_msg lcert;
            process_send_certificate_from_credentials
              s
              creds
              network_out
              network_out_len
              app_out
              app_out_len
          } else {
            IM.free_certificate_msg lcert;
            process_local_unexpected_message
              s
              kind
              payload
              payload_len
              network_out
              network_out_len
              app_out
              app_out_len
          }
        }
      }
    }
    ST.LocalSignCertificateVerify -> {
      assert (pure (Seq.equal (Ghost.reveal 'payload_bytes) B.empty));
      process_sign_certificate_verify
        s
        creds
        network_out
        network_out_len
        app_out
        app_out_len
    }
    ST.LocalStartServer -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalSelectServerParameters -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalDeriveSharedSecret -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalInstallClientHandshakeTrafficKeys -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalInstallServerHandshakeTrafficKeys -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalInstallClientApplicationTrafficKeys -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalInstallServerApplicationTrafficKeys -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalVerifyClientFinished -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalDeliverApplicationData -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalSendServerHello -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalSendEncryptedExtensions -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalSendCertificateVerify -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalSendServerFinished -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalSendApplicationData -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalSendCloseNotify -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
    ST.LocalFail -> {
      assert (pure (server_local_event_input_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)));
      process_local_event
        s kind payload payload_len network_out network_out_len app_out app_out_len
    }
  }
}

fn process_client_hello
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lch:IM.client_hello)
  (#ch:erased M.client_hello)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           IM.is_valid_client_hello lch ch **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsAwaitingClientHello /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 SZ.v fragment_len <= Bounds.max_client_hello_len /\
                 Seq.equal
                  (Ghost.reveal 'fragment_bytes)
                  (TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch)) /\
                 lch.IM.client_hello_has_server_name == true /\
                 CM.client_hello_server_name_len_for ch ==
                  lch.IM.client_hello_server_name_len /\
                 CM.client_hello_cipher_suites_len_for ch ==
                  lch.IM.client_hello_cipher_suites_len /\
                 CM.client_hello_signature_schemes_len_for ch ==
                  lch.IM.client_hello_signature_schemes_len /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                  B.length (TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch)) <=
                  Bounds.max_transcript_len /\
                 CS.legal_event
                  'st0.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  }) /\
                 CS.event_raw_delta_legal
                  'st0.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  })
                  B.empty
                  (Ghost.reveal 'raw_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.received_client_hello_state
                    'st0
                    (Ghost.reveal ch)
                    (Ghost.reveal 'raw_bytes) /\
                ST.server_network_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  (M.TlsHandshake (M.ClientHello ch))
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SN.connection_exactly s 'st0);
  let resp = SN.process_client_hello
    s
    raw
    raw_len
    fragment
    fragment_len
    lch
    #ch
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SN.connection_exactly s st1 **
            pts_to raw 'raw_bytes **
            pts_to fragment 'fragment_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SN.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_client_finished
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (lfin:IM.finished)
  (#fin:erased M.finished)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           IM.is_valid_finished lfin fin **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CM.can_receive_client_finished
                   'st0
                   (Ghost.reveal fin)
                   (Ghost.reveal 'raw_bytes) /\
                 CS.received_event_nonempty_decode_projection
                   'st0.CS.cs_model
                   (ST.received_message_event
                     (M.TlsHandshake (M.Finished (Ghost.reveal fin))))
                   (Ghost.reveal 'raw_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.received_client_finished_state
                    'st0
                    (Ghost.reveal fin)
                    (Ghost.reveal 'raw_bytes) /\
                ST.server_network_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  (M.TlsHandshake (M.Finished (Ghost.reveal fin)))
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  rewrite (connection_exactly s 'st0) as (SN.connection_exactly s 'st0);
  let resp = SN.process_client_finished
    s
    raw
    raw_len
    lfin
    #fin
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SN.connection_exactly s st1 **
            pts_to raw 'raw_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SN.connection_exactly s st1) as (connection_exactly s st1);
  resp
}

fn process_network_bytes
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0)
  returns buffer_resp:ST.server_buffer_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_network_bytes_end_to_end_correct
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes /\
                (buffer_resp.ST.response.ST.status == ST.StepOk ==>
                  (exists ch raw_received.
                    st1 ==
                      CM.received_client_hello_state
                        'st0
                        ch
                        raw_received /\
                    Seq.equal
                      raw_received
                      (Seq.slice
                        (Ghost.reveal 'raw_bytes)
                        0
                        (SZ.v buffer_resp.ST.consumed_len))) \/
                  (exists fin raw_received.
                    st1 ==
                      CM.received_client_finished_state
                        'st0
                        fin
                        raw_received /\
                    Seq.equal
                      raw_received
                      (Seq.slice
                        (Ghost.reveal 'raw_bytes)
                        0
                        (SZ.v buffer_resp.ST.consumed_len)))) /\
                (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                  buffer_resp.ST.consumed_len == 0sz))
{
  rewrite (connection_exactly s 'st0) as (SN.connection_exactly s 'st0);
  let buffer_resp = SN.process_network_bytes
    s
    raw
    raw_len
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (SN.connection_exactly s st1 **
            pts_to raw 'raw_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (SN.connection_exactly s st1) as (connection_exactly s st1);
  buffer_resp
}
