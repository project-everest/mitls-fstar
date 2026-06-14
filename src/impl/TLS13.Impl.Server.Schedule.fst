module TLS13.Impl.Server.Schedule

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module M = TLS13.Messages
module R = TLS13.Record.Spec
module ST = TLS13.Impl.Server.Types
module Tags = TLS13.Impl.ConnectionState.Tags
module T = TLS13.Types
module U64 = FStar.UInt64
module W = TLS13.Wire.Spec

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
