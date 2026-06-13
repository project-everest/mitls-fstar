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
module M = TLS13.Messages
module O = TLS13.OpenSSL
module R = TLS13.Record.Spec
module Ser = TLS13.Impl.Serializer
module SM = TLS13.StateMachine
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
                 B.length 'credential_identity_bytes == SZ.v credential_identity_len)
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
  unfold (connection_exactly s 'st0);
  CLH.start_server s;
  fold (connection_exactly s (CM.started_server_state 'st0));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let delta = {
    CS.delta_event = CS.ConnLocalEvent CS.LocalStartServer;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  assert (pure (CS.legal_connection_delta
    'st0
    delta
    (CM.started_server_state 'st0)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    delta
    (CM.started_server_state 'st0);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    delta
    (CM.started_server_state 'st0);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.started_server_state 'st0);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    delta
    (CM.started_server_state 'st0);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    delta
    (CM.started_server_state 'st0);

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.started_server_state 'st0).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.started_server_state 'st0).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.started_server_state 'st0).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct (CM.started_server_state 'st0)));
  assert (pure (ST.server_raw_to_message_replay_consistent (CM.started_server_state 'st0)));
  assert (pure (ST.server_end_to_end_invariant (CM.started_server_state 'st0)));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.started_server_state 'st0)
    resp
    (CS.ConnLocalEvent CS.LocalStartServer)
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.started_server_state 'st0)
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    (CS.ConnLocalEvent CS.LocalStartServer)
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.started_server_state 'st0)
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.started_server_state 'st0)
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    'old_network_out
    'old_app_out));
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
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSelectServerParameters
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CLH.select_server_parameters s #selection;
  fold (connection_exactly s (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let delta = Ghost.hide {
    CS.delta_event =
      CS.ConnLocalEvent
        (CS.LocalSelectServerParameters (Ghost.reveal selection));
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  CM.lemma_selected_server_parameters_state_evolves
    'st0
    (Ghost.reveal selection);
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.selected_server_parameters_state 'st0 (Ghost.reveal selection)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.selected_server_parameters_state 'st0 (Ghost.reveal selection)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection))
    resp
    (CS.ConnLocalEvent
      (CS.LocalSelectServerParameters (Ghost.reveal selection)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection))
    resp
    ST.LocalSelectServerParameters
    B.empty
    (CS.ConnLocalEvent
      (CS.LocalSelectServerParameters (Ghost.reveal selection)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection))
    resp
    ST.LocalSelectServerParameters
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.selected_server_parameters_state 'st0 (Ghost.reveal selection))
    resp
    ST.LocalSelectServerParameters
    B.empty
    'old_network_out
    'old_app_out));
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
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendServerHello
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CLH.mark_sent_server_hello
    s
    raw
    fragment
    fragment_len
    lsh
    #sh;
  fold (connection_exactly
    s
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes)));

  let resp = {
    ST.network_out_len = raw_len;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = Ghost.reveal 'raw_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_server_hello_state_evolves
    'st0
    sh
    (Ghost.reveal 'raw_bytes);
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes));

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (SZ.v raw_len <= B.length 'old_network_out));
  assert (pure (ST.response_network_out resp 'old_network_out ==
    Seq.slice 'old_network_out 0 (SZ.v raw_len)));
  assert (pure (Seq.equal
    (ST.response_network_out resp 'old_network_out)
    (Ghost.reveal 'raw_bytes)));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))
    resp
    (Ghost.reveal ev)
    (Ghost.reveal 'raw_bytes)
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))
    resp
    ST.LocalSendServerHello
    B.empty
    (Ghost.reveal ev)
    (Ghost.reveal 'raw_bytes)
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))
    resp
    ST.LocalSendServerHello
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (CS.event_protected_raw_segmented_success
    (Ghost.reveal ev)
    (Ghost.reveal 'raw_bytes)
    B.empty));
  assert (pure (CS.sent_event_seal_projection
    'st0.CS.cs_model
    (Ghost.reveal ev)
    (Ghost.reveal 'raw_bytes)));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_server_hello_state 'st0 sh (Ghost.reveal 'raw_bytes))
    resp
    ST.LocalSendServerHello
    B.empty
    'old_network_out
    'old_app_out));
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
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendServerHello
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  let written_raw =
    Ser.serialize_server_hello_record_from_selection
      #sh
      lsh
      network_out
      network_out_len;
  with network_out_bytes. assert (pts_to network_out network_out_bytes);
  assert (pure (B.length network_out_bytes == 95));
  assert (pure (SZ.v written_raw == 95));
  assert (pure (Seq.equal
    network_out_bytes
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello sh)))));
  assert (pure (CM.can_send_server_hello
    'st0
    sh
    network_out_bytes));

  let mut fragment = [| 0uy; 90sz |];
  let written_fragment =
    Ser.serialize_server_hello_from_selection
      #sh
      lsh
      fragment
      90sz;
  with fragment_bytes. assert (pts_to fragment fragment_bytes);
  assert (pure (B.length fragment_bytes == 90));
  assert (pure (SZ.v written_fragment == 90));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_handshake (M.ServerHello sh))));
  assert (pure (SZ.v written_fragment <= Bounds.max_server_hello_len));

  unfold (connection_exactly s 'st0);
  CLH.mark_sent_server_hello
    s
    network_out
    fragment
    written_fragment
    lsh
    #sh;
  fold (connection_exactly
    s
    (CM.sent_server_hello_state 'st0 sh network_out_bytes));

  let resp = {
    ST.network_out_len = written_raw;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = network_out_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_server_hello_state_evolves
    'st0
    sh
    network_out_bytes;
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh network_out_bytes);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh network_out_bytes);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_server_hello_state 'st0 sh network_out_bytes);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh network_out_bytes);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_hello_state 'st0 sh network_out_bytes);

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_raw);
  Seq.lemma_eq_intro
    network_out_bytes
    (Seq.slice network_out_bytes 0 (SZ.v written_raw));
  assert (pure (ST.response_network_out resp network_out_bytes ==
    Seq.slice network_out_bytes 0 (SZ.v written_raw)));
  assert (pure (Seq.equal
    (ST.response_network_out resp network_out_bytes)
    network_out_bytes));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_server_hello_state 'st0 sh network_out_bytes).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_server_hello_state 'st0 sh network_out_bytes).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_server_hello_state 'st0 sh network_out_bytes).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)
    resp
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)
    resp
    ST.LocalSendServerHello
    B.empty
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)
    resp
    ST.LocalSendServerHello
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (CS.event_protected_raw_segmented_success
    (Ghost.reveal ev)
    network_out_bytes
    B.empty));
  assert (pure (CS.sent_event_seal_projection
    'st0.CS.cs_model
    (Ghost.reveal ev)
    network_out_bytes));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_server_hello_state 'st0 sh network_out_bytes)
    resp
    ST.LocalSendServerHello
    B.empty
    network_out_bytes
    'old_app_out));
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
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendEncryptedExtensions
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  let ee_val = { M.negotiated_alpn = None };
  let ee = Ghost.hide ee_val;
  assert (pure (ee_val.M.negotiated_alpn == None));

  let alpn = V.alloc 0uy 255sz;
  let lee = {
    IM.encrypted_extensions_alpn = alpn;
    IM.encrypted_extensions_alpn_len = 0sz;
    IM.encrypted_extensions_has_alpn = false;
  };
  assert (pure (lee.IM.encrypted_extensions_alpn == alpn));
  with alpn_bytes. assert (V.pts_to alpn alpn_bytes);
  assert (pure (V.is_full_vec alpn));
  assert (pure (V.length alpn == IM.max_alpn_len));
  assert (pure (SZ.v lee.IM.encrypted_extensions_alpn_len <= B.length alpn_bytes));
  rewrite (V.pts_to alpn alpn_bytes)
    as (V.pts_to lee.IM.encrypted_extensions_alpn alpn_bytes);
  fold (IM.is_valid_encrypted_extensions lee ee_val);

  let mut fragment = [| 0uy; 6sz |];
  let written_fragment =
    Ser.serialize_empty_encrypted_extensions
      fragment
      6sz;
  with fragment_bytes. assert (pts_to fragment fragment_bytes);
  assert (pure (B.length fragment_bytes == 6));
  assert (pure (SZ.v written_fragment == 6));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_empty_encrypted_extensions ())));
  let dummy_sh = {
    M.random = Seq.create 32 0uy;
    M.key_share = Seq.create 32 0uy;
    M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
  };
  let dummy_cert = { M.chain = [] };
  let dummy_cv = {
    M.scheme = T.RsaPssRsaeSha256;
    M.signature = B.empty;
  };
  let dummy_fin = { M.verify_data = Seq.create 32 0uy };
  W.lemma_fixed_server_handshake_serializers
    dummy_sh
    dummy_cert
    dummy_cv
    dummy_fin;
  assert (pure (Seq.equal
    (W.serialize_empty_encrypted_extensions ())
    (W.serialize_handshake (M.EncryptedExtensions ee_val))));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_handshake (M.EncryptedExtensions ee_val))));

  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  let written_raw =
    Ser.serialize_protected_handshake_record
      #(M.EncryptedExtensions ee_val)
      s.records.write
      fragment
      written_fragment
      network_out
      network_out_len;
  with network_out_bytes. assert (pts_to network_out network_out_bytes);
  fold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  fold (CR.connection_model_exactly s 'st0.CS.cs_model);
  fold (connection_exactly s 'st0);

  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (B.length network_out_bytes == 28));
  assert (pure (SZ.v written_raw == 28));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_raw);
  Seq.lemma_eq_intro
    network_out_bytes
    (Seq.slice network_out_bytes 0 (SZ.v written_raw));
  assert (pure (CS.raw_records_exactly network_out_bytes T.ApplicationData 1));
  assert (pure (CS.event_raw_delta_legal
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_val);
    })
    network_out_bytes
    B.empty));
  assert (pure (CS.sent_single_protected_message_seal
    'st0.CS.cs_model
    (M.TlsHandshake (M.EncryptedExtensions ee_val))
    network_out_bytes));
  assert (pure (CS.sent_event_seal_projection
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_val);
    })
    network_out_bytes));
  CSL.lemma_event_raw_delta_legal_protected_segmented
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_val);
    })
    network_out_bytes
    B.empty;
  assert (pure (CS.event_protected_raw_segmented_success
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_val);
    })
    network_out_bytes
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
  assert (pure (CM.can_send_encrypted_extensions
    'st0
    ee_val
    network_out_bytes));

  unfold (connection_exactly s 'st0);
  CLH.mark_sent_encrypted_extensions
    s
    network_out
    fragment
    written_fragment
    lee
    #ee;
  fold (connection_exactly
    s
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes));

  let resp = {
    ST.network_out_len = written_raw;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_val);
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = network_out_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_encrypted_extensions_state_evolves
    'st0
    ee_val
    network_out_bytes;
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes);

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (ST.response_network_out resp network_out_bytes ==
    Seq.slice network_out_bytes 0 (SZ.v written_raw)));
  assert (pure (Seq.equal
    (ST.response_network_out resp network_out_bytes)
    network_out_bytes));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes)));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes)
    resp
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes)
    resp
    ST.LocalSendEncryptedExtensions
    B.empty
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes)
    resp
    ST.LocalSendEncryptedExtensions
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_encrypted_extensions_state 'st0 ee_val network_out_bytes)
    resp
    ST.LocalSendEncryptedExtensions
    B.empty
    network_out_bytes
    'old_app_out));
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
                     (W.serialize_certificate_from_credential
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
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificate
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  let fragment = V.alloc 0uy fragment_len;
  with old_fragment_bytes. assert (V.pts_to fragment old_fragment_bytes);
  V.pts_to_len fragment;
  assert (pure (B.length old_fragment_bytes == SZ.v fragment_len));
  V.to_array_pts_to fragment;
  let written_fragment =
    Ser.serialize_certificate_from_credential
      #cert
      lcert
      (V.vec_to_array fragment)
      fragment_len;
  with fragment_bytes. assert (pts_to (V.vec_to_array fragment) fragment_bytes);
  assert (pure (B.length fragment_bytes == SZ.v fragment_len));
  assert (pure (SZ.v written_fragment == SZ.v fragment_len));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_certificate_from_credential (Ghost.reveal cert))));
  W.lemma_fixed_server_handshake_serializers
    {
      M.random = Seq.create 32 0uy;
      M.key_share = Seq.create 32 0uy;
      M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    }
    (Ghost.reveal cert)
    { M.scheme = T.RsaPssRsaeSha256; M.signature = B.empty }
    { M.verify_data = Seq.create 32 0uy };
  assert (pure (Seq.equal
    (W.serialize_certificate_from_credential (Ghost.reveal cert))
    (W.serialize_handshake (M.Certificate (Ghost.reveal cert)))));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_handshake (M.Certificate (Ghost.reveal cert)))));
  assert (pure (
    B.length (W.serialize_handshake (M.Certificate (Ghost.reveal cert))) ==
    SZ.v fragment_len));

  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  let written_raw =
    Ser.serialize_protected_handshake_record
      #(M.Certificate (Ghost.reveal cert))
      s.records.write
      (V.vec_to_array fragment)
      written_fragment
      network_out
      network_out_len;
  with network_out_bytes. assert (pts_to network_out network_out_bytes);
  fold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  fold (CR.connection_model_exactly s 'st0.CS.cs_model);
  fold (connection_exactly s 'st0);

  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (SZ.v written_raw == SZ.v fragment_len + 22));
  assert (pure (SZ.v written_raw == SZ.v network_out_len));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_raw);
  Seq.lemma_eq_intro
    network_out_bytes
    (Seq.slice network_out_bytes 0 (SZ.v written_raw));
  assert (pure (CS.raw_records_exactly network_out_bytes T.ApplicationData 1));
  assert (pure (CS.event_raw_delta_legal
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
    })
    network_out_bytes
    B.empty));
  assert (pure (CS.sent_single_protected_message_seal
    'st0.CS.cs_model
    (M.TlsHandshake (M.Certificate (Ghost.reveal cert)))
    network_out_bytes));
  assert (pure (CS.sent_event_seal_projection
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
    })
    network_out_bytes));
  CSL.lemma_event_raw_delta_legal_protected_segmented
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
    })
    network_out_bytes
    B.empty;
  assert (pure (CS.event_protected_raw_segmented_success
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
    })
    network_out_bytes
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
  assert (pure (CM.can_send_certificate
    'st0
    (Ghost.reveal cert)
    network_out_bytes));

  unfold (connection_exactly s 'st0);
  CLH.mark_sent_certificate
    s
    network_out
    (V.vec_to_array fragment)
    written_fragment
    lcert
    #cert;
  fold (connection_exactly
    s
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes));
  V.to_vec_pts_to fragment;
  V.free fragment;

  let resp = {
    ST.network_out_len = written_raw;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = network_out_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_certificate_state_evolves
    'st0
    (Ghost.reveal cert)
    network_out_bytes;
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes);

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (ST.response_network_out resp network_out_bytes ==
    Seq.slice network_out_bytes 0 (SZ.v written_raw)));
  assert (pure (Seq.equal
    (ST.response_network_out resp network_out_bytes)
    network_out_bytes));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)
    resp
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)
    resp
    ST.LocalSendCertificate
    B.empty
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)
    resp
    ST.LocalSendCertificate
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_certificate_state 'st0 (Ghost.reveal cert) network_out_bytes)
    resp
    ST.LocalSendCertificate
    B.empty
    network_out_bytes
    'old_app_out));
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
                     (W.serialize_certificate_verify_from_signature
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
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificateVerify
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  let fragment = V.alloc 0uy fragment_len;
  with old_fragment_bytes. assert (V.pts_to fragment old_fragment_bytes);
  V.pts_to_len fragment;
  assert (pure (B.length old_fragment_bytes == SZ.v fragment_len));
  V.to_array_pts_to fragment;
  let written_fragment =
    Ser.serialize_certificate_verify_from_signature
      #cv
      lcv
      (V.vec_to_array fragment)
      fragment_len;
  with fragment_bytes. assert (pts_to (V.vec_to_array fragment) fragment_bytes);
  assert (pure (B.length fragment_bytes == SZ.v fragment_len));
  assert (pure (SZ.v written_fragment == SZ.v fragment_len));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_certificate_verify_from_signature (Ghost.reveal cv))));
  W.lemma_fixed_server_handshake_serializers
    {
      M.random = Seq.create 32 0uy;
      M.key_share = Seq.create 32 0uy;
      M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    }
    { M.chain = [] }
    (Ghost.reveal cv)
    { M.verify_data = Seq.create 32 0uy };
  assert (pure (Seq.equal
    (W.serialize_certificate_verify_from_signature (Ghost.reveal cv))
    (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv)))));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv)))));
  assert (pure (
    B.length (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))) ==
    SZ.v fragment_len));
  IM.free_certificate_verify lcv;

  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  let written_raw =
    Ser.serialize_protected_handshake_record
      #(M.CertificateVerify (Ghost.reveal cv))
      s.records.write
      (V.vec_to_array fragment)
      written_fragment
      network_out
      network_out_len;
  with network_out_bytes. assert (pts_to network_out network_out_bytes);
  fold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  fold (CR.connection_model_exactly s 'st0.CS.cs_model);
  fold (connection_exactly s 'st0);

  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (SZ.v written_raw == SZ.v fragment_len + 22));
  assert (pure (SZ.v written_raw == SZ.v network_out_len));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_raw);
  Seq.lemma_eq_intro
    network_out_bytes
    (Seq.slice network_out_bytes 0 (SZ.v written_raw));
  assert (pure (CS.raw_records_exactly network_out_bytes T.ApplicationData 1));
  assert (pure (CS.event_raw_delta_legal
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes
    B.empty));
  assert (pure (CS.sent_single_protected_message_seal
    'st0.CS.cs_model
    (M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv)))
    network_out_bytes));
  assert (pure (CS.sent_event_seal_projection
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes));
  CSL.lemma_event_raw_delta_legal_protected_segmented
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes
    B.empty;
  assert (pure (CS.event_protected_raw_segmented_success
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes
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
  assert (pure (CM.can_send_certificate_verify
    'st0
    (Ghost.reveal cv)
    network_out_bytes));

  unfold (connection_exactly s 'st0);
  CLH.mark_sent_certificate_verify
    s
    network_out
    (V.vec_to_array fragment)
    written_fragment
    #cv;
  fold (connection_exactly
    s
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes));
  V.to_vec_pts_to fragment;
  V.free fragment;

  let resp = {
    ST.network_out_len = written_raw;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = network_out_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_certificate_verify_state_evolves
    'st0
    (Ghost.reveal cv)
    network_out_bytes;
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (ST.response_network_out resp network_out_bytes ==
    Seq.slice network_out_bytes 0 (SZ.v written_raw)));
  assert (pure (Seq.equal
    (ST.response_network_out resp network_out_bytes)
    network_out_bytes));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    ST.LocalSendCertificateVerify
    B.empty
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    ST.LocalSendCertificateVerify
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    ST.LocalSendCertificateVerify
    B.empty
    network_out_bytes
    'old_app_out));
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
                     (W.serialize_certificate_verify_from_signature
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
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificateVerify
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  let fragment = V.alloc 0uy fragment_len;
  with old_fragment_bytes. assert (V.pts_to fragment old_fragment_bytes);
  V.pts_to_len fragment;
  assert (pure (B.length old_fragment_bytes == SZ.v fragment_len));
  V.to_array_pts_to fragment;

  unfold (connection_exactly s 'st0);
  let written_fragment =
    CLH.serialize_stored_certificate_verify_fragment
      s
      #cv
      (V.vec_to_array fragment)
      fragment_len
      #'st0;
  fold (connection_exactly s 'st0);
  with fragment_bytes. assert (pts_to (V.vec_to_array fragment) fragment_bytes);
  assert (pure (B.length fragment_bytes == SZ.v fragment_len));
  assert (pure (SZ.v written_fragment == SZ.v fragment_len));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_certificate_verify_from_signature (Ghost.reveal cv))));
  W.lemma_fixed_server_handshake_serializers
    {
      M.random = Seq.create 32 0uy;
      M.key_share = Seq.create 32 0uy;
      M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    }
    { M.chain = [] }
    (Ghost.reveal cv)
    { M.verify_data = Seq.create 32 0uy };
  assert (pure (Seq.equal
    (W.serialize_certificate_verify_from_signature (Ghost.reveal cv))
    (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv)))));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv)))));
  assert (pure (
    B.length (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))) ==
    SZ.v fragment_len));

  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  let written_raw =
    Ser.serialize_protected_handshake_record
      #(M.CertificateVerify (Ghost.reveal cv))
      s.records.write
      (V.vec_to_array fragment)
      written_fragment
      network_out
      network_out_len;
  with network_out_bytes. assert (pts_to network_out network_out_bytes);
  fold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  fold (CR.connection_model_exactly s 'st0.CS.cs_model);
  fold (connection_exactly s 'st0);

  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (SZ.v written_raw == SZ.v fragment_len + 22));
  assert (pure (SZ.v written_raw == SZ.v network_out_len));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_raw);
  Seq.lemma_eq_intro
    network_out_bytes
    (Seq.slice network_out_bytes 0 (SZ.v written_raw));
  assert (pure (CS.raw_records_exactly network_out_bytes T.ApplicationData 1));
  assert (pure (CS.event_raw_delta_legal
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes
    B.empty));
  assert (pure (CS.sent_single_protected_message_seal
    'st0.CS.cs_model
    (M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv)))
    network_out_bytes));
  assert (pure (CS.sent_event_seal_projection
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes));
  CSL.lemma_event_raw_delta_legal_protected_segmented
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes
    B.empty;
  assert (pure (CS.event_protected_raw_segmented_success
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
    })
    network_out_bytes
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
  assert (pure (CM.can_send_certificate_verify
    'st0
    (Ghost.reveal cv)
    network_out_bytes));

  unfold (connection_exactly s 'st0);
  CLH.mark_sent_certificate_verify
    s
    network_out
    (V.vec_to_array fragment)
    written_fragment
    #cv;
  fold (connection_exactly
    s
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes));
  V.to_vec_pts_to fragment;
  V.free fragment;

  let resp = {
    ST.network_out_len = written_raw;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = network_out_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_certificate_verify_state_evolves
    'st0
    (Ghost.reveal cv)
    network_out_bytes;
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes);

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (ST.response_network_out resp network_out_bytes ==
    Seq.slice network_out_bytes 0 (SZ.v written_raw)));
  assert (pure (Seq.equal
    (ST.response_network_out resp network_out_bytes)
    network_out_bytes));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    ST.LocalSendCertificateVerify
    B.empty
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    ST.LocalSendCertificateVerify
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_certificate_verify_state 'st0 (Ghost.reveal cv) network_out_bytes)
    resp
    ST.LocalSendCertificateVerify
    B.empty
    network_out_bytes
    'old_app_out));
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
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendServerFinished
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.handshake_exactly s.handshake 'st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (CR.sized_bytes_exactly
    s.handshake.transcript
    Bounds.max_transcript_len
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with transcript_storage transcript_len. _;
  let transcript_len_runtime = !s.handshake.transcript.len;
  assert (pure (transcript_len_runtime == transcript_len));
  assert (pure (CR.byte_prefix_matches
    transcript_storage
    transcript_len_runtime
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (Seq.equal
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
  Seq.lemma_eq_intro
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));
  V.to_array_pts_to s.handshake.transcript.bytes;
  let mut transcript_hash = [| 0uy; 32sz |];
  Crypto.sha256_prefix
    (V.vec_to_array s.handshake.transcript.bytes)
    transcript_len_runtime
    transcript_hash;
  V.to_vec_pts_to s.handshake.transcript.bytes;
  with transcript_hash_bytes. assert (pts_to transcript_hash transcript_hash_bytes);
  assert (pure (transcript_hash_bytes ==
    Tr.hash 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  unfold (CR.key_schedule_exactly
    s.handshake.keys
    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (CR.traffic_key_material_exactly
    s.handshake.keys.server_handshake_traffic
    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  with sh_present sh_secret sh_key sh_iv. _;
  CR.lemma_traffic_key_material_match_present_of_some
    sh_present
    sh_secret
    sh_key
    sh_iv
    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic;
  assert (pure (sh_present));
  assert (pure ('st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic ==
    Some {
      CS.traffic_secret = sh_secret;
      CS.traffic_key = sh_key;
      CS.traffic_iv = sh_iv;
    }));

  V.to_array_pts_to s.handshake.keys.server_handshake_traffic.traffic_secret;
  let mut verify_data = [| 0uy; 32sz |];
  KS.finished_verify_data
    (V.vec_to_array s.handshake.keys.server_handshake_traffic.traffic_secret)
    transcript_hash
    verify_data;
  V.to_vec_pts_to s.handshake.keys.server_handshake_traffic.traffic_secret;
  with verify_data_bytes. assert (pts_to verify_data verify_data_bytes);
  assert (pure (verify_data_bytes ==
    K.finished_verify_data
      sh_secret
      (Tr.hash 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

  fold (CR.traffic_key_material_exactly
    s.handshake.keys.server_handshake_traffic
    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  fold (CR.key_schedule_exactly
    s.handshake.keys
    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (CR.sized_bytes_exactly
    s.handshake.transcript
    Bounds.max_transcript_len
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (CR.handshake_exactly s.handshake 'st0.CS.cs_model.CS.model_handshake);
  fold (CR.connection_model_exactly s 'st0.CS.cs_model);
  fold (connection_exactly s 'st0);

  let fin = Ghost.hide ({ M.verify_data = verify_data_bytes });
  let fin_vec = V.alloc 0uy 32sz;
  CR.copy_fixed32_array_to_vec verify_data fin_vec;
  let lfin = { IM.finished_verify_data = fin_vec };
  assert (pure (lfin.IM.finished_verify_data == fin_vec));
  with fin_vec_bytes. assert (V.pts_to fin_vec fin_vec_bytes);
  assert (pure (fin_vec_bytes == verify_data_bytes));
  rewrite (V.pts_to fin_vec fin_vec_bytes)
    as (V.pts_to lfin.IM.finished_verify_data fin_vec_bytes);
  assert (pure (B.length verify_data_bytes == 32));
  assert (pure (Seq.equal fin_vec_bytes (Ghost.reveal fin).M.verify_data));
  fold (IM.is_valid_finished lfin (Ghost.reveal fin));

  let mut fragment = [| 0uy; 36sz |];
  let written_fragment =
    Ser.serialize_server_finished
      #fin
      lfin
      fragment
      36sz;
  with fragment_bytes. assert (pts_to fragment fragment_bytes);
  assert (pure (B.length fragment_bytes == 36));
  assert (pure (SZ.v written_fragment == 36));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_server_finished (Ghost.reveal fin))));
  W.lemma_fixed_server_handshake_serializers
    {
      M.random = Seq.create 32 0uy;
      M.key_share = Seq.create 32 0uy;
      M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    }
    { M.chain = [] }
    { M.scheme = T.RsaPssRsaeSha256; M.signature = B.empty }
    (Ghost.reveal fin);
  assert (pure (Seq.equal
    (W.serialize_server_finished (Ghost.reveal fin))
    (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));

  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  let written_raw =
    Ser.serialize_protected_handshake_record
      #(M.Finished (Ghost.reveal fin))
      s.records.write
      fragment
      written_fragment
      network_out
      network_out_len;
  with network_out_bytes. assert (pts_to network_out network_out_bytes);
  fold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  fold (CR.connection_model_exactly s 'st0.CS.cs_model);
  fold (connection_exactly s 'st0);

  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (B.length network_out_bytes == 58));
  assert (pure (SZ.v written_raw == 58));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_raw);
  Seq.lemma_eq_intro
    network_out_bytes
    (Seq.slice network_out_bytes 0 (SZ.v written_raw));
  assert (pure (CS.raw_records_exactly network_out_bytes T.ApplicationData 1));
  assert (pure (CS.event_raw_delta_legal
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    network_out_bytes
    B.empty));
  assert (pure (CS.sent_single_protected_message_seal
    'st0.CS.cs_model
    (M.TlsHandshake (M.Finished (Ghost.reveal fin)))
    network_out_bytes));
  assert (pure (CS.sent_event_seal_projection
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    network_out_bytes));
  CSL.lemma_event_raw_delta_legal_protected_segmented
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    network_out_bytes
    B.empty;
  assert (pure (CS.event_protected_raw_segmented_success
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    network_out_bytes
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
  assert (pure (H.verify_finished
    sh_secret
    (Tr.hash 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
    (Ghost.reveal fin)));
  assert (pure (CM.can_send_server_finished
    'st0
    (Ghost.reveal fin)
    network_out_bytes));

  unfold (connection_exactly s 'st0);
  CLH.mark_sent_server_finished
    s
    network_out
    fragment
    written_fragment
    lfin
    #fin;
  fold (connection_exactly
    s
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes));

  let resp = {
    ST.network_out_len = written_raw;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = network_out_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_server_finished_state_evolves
    'st0
    (Ghost.reveal fin)
    network_out_bytes;
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes);

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (ST.response_network_out resp network_out_bytes ==
    Seq.slice network_out_bytes 0 (SZ.v written_raw)));
  assert (pure (Seq.equal
    (ST.response_network_out resp network_out_bytes)
    network_out_bytes));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)
    resp
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)
    resp
    ST.LocalSendServerFinished
    B.empty
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)
    resp
    ST.LocalSendServerFinished
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)
    resp
    ST.LocalSendServerFinished
    B.empty
    network_out_bytes
    'old_app_out));
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
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalDeriveSharedSecret
                  (Ghost.reveal shared)
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CLH.derive_shared_secret_from_bytes s shared_src #shared;
  fold (connection_exactly
    s
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let delta = Ghost.hide {
    CS.delta_event =
      CS.ConnLocalEvent
        (CS.LocalDeriveSharedSecret (Ghost.reveal shared));
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  CM.lemma_derived_shared_secret_state_evolves
    'st0
    (Ghost.reveal shared);
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.derived_shared_secret_state 'st0 (Ghost.reveal shared)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.derived_shared_secret_state 'st0 (Ghost.reveal shared)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared))
    resp
    (CS.ConnLocalEvent
      (CS.LocalDeriveSharedSecret (Ghost.reveal shared)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared))
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal shared)
    (CS.ConnLocalEvent
      (CS.LocalDeriveSharedSecret (Ghost.reveal shared)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared))
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal shared)
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared))
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal shared)
    'old_network_out
    'old_app_out));
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
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalInstallServerHandshakeTrafficKeys
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  let install = Ghost.hide {
    CS.install_epoch = CS.TrafficHandshake;
    CS.install_direction = CS.TrafficWrite;
    CS.install_material = Ghost.reveal material;
  };
  let role_install = Ghost.hide {
    CS.install_role = CS.ServerEndpoint;
    CS.install_payload = Ghost.reveal install;
  };

  unfold (connection_exactly s 'st0);
  CLH.install_server_handshake_write_traffic_keys_from_material
    s
    traffic_secret_src
    traffic_key_src
    traffic_iv_src
    #material;
  fold (connection_exactly
    s
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let delta = Ghost.hide {
    CS.delta_event =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install));
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  CM.lemma_installed_traffic_keys_for_role_state_evolves
    'st0
    (Ghost.reveal role_install);
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallServerHandshakeTrafficKeys
    B.empty
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallServerHandshakeTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallServerHandshakeTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
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
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalInstallServerHandshakeTrafficKeys
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CLH.derive_and_install_server_handshake_write_traffic_keys s;
  with material.
    assert (CR.connection_exactly
      s
      (CM.installed_traffic_keys_for_role_state 'st0 {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = material;
        };
      }));
  let install = Ghost.hide {
    CS.install_epoch = CS.TrafficHandshake;
    CS.install_direction = CS.TrafficWrite;
    CS.install_material = material;
  };
  let role_install = Ghost.hide {
    CS.install_role = CS.ServerEndpoint;
    CS.install_payload = Ghost.reveal install;
  };
  fold (connection_exactly
    s
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let delta = Ghost.hide {
    CS.delta_event =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install));
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallServerHandshakeTrafficKeys
    B.empty
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallServerHandshakeTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallServerHandshakeTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
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
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalInstallClientHandshakeTrafficKeys
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  let install = Ghost.hide {
    CS.install_epoch = CS.TrafficHandshake;
    CS.install_direction = CS.TrafficRead;
    CS.install_material = Ghost.reveal material;
  };
  let role_install = Ghost.hide {
    CS.install_role = CS.ServerEndpoint;
    CS.install_payload = Ghost.reveal install;
  };

  unfold (connection_exactly s 'st0);
  CLH.install_client_handshake_read_traffic_keys_from_material
    s
    traffic_secret_src
    traffic_key_src
    traffic_iv_src
    #material;
  fold (connection_exactly
    s
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let delta = Ghost.hide {
    CS.delta_event =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install));
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  CM.lemma_installed_traffic_keys_for_role_state_evolves
    'st0
    (Ghost.reveal role_install);
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallClientHandshakeTrafficKeys
    B.empty
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallClientHandshakeTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallClientHandshakeTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
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
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalInstallClientHandshakeTrafficKeys
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CLH.derive_and_install_client_handshake_read_traffic_keys s;
  with material.
    assert (CR.connection_exactly
      s
      (CM.installed_traffic_keys_for_role_state 'st0 {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = material;
        };
      }));
  let install = Ghost.hide {
    CS.install_epoch = CS.TrafficHandshake;
    CS.install_direction = CS.TrafficRead;
    CS.install_material = material;
  };
  let role_install = Ghost.hide {
    CS.install_role = CS.ServerEndpoint;
    CS.install_payload = Ghost.reveal install;
  };
  fold (connection_exactly
    s
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let delta = Ghost.hide {
    CS.delta_event =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install));
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallClientHandshakeTrafficKeys
    B.empty
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallClientHandshakeTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallClientHandshakeTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
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
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalInstallServerApplicationTrafficKeys
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  let install = Ghost.hide {
    CS.install_epoch = CS.TrafficApplication;
    CS.install_direction = CS.TrafficWrite;
    CS.install_material = Ghost.reveal material;
  };
  let role_install = Ghost.hide {
    CS.install_role = CS.ServerEndpoint;
    CS.install_payload = Ghost.reveal install;
  };

  unfold (connection_exactly s 'st0);
  CLH.install_server_application_write_traffic_keys_from_material
    s
    traffic_secret_src
    traffic_key_src
    traffic_iv_src
    #material;
  fold (connection_exactly
    s
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let delta = Ghost.hide {
    CS.delta_event =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install));
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  CM.lemma_installed_traffic_keys_for_role_state_evolves
    'st0
    (Ghost.reveal role_install);
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallServerApplicationTrafficKeys
    B.empty
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallServerApplicationTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallServerApplicationTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
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
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalInstallClientApplicationTrafficKeys
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  let install = Ghost.hide {
    CS.install_epoch = CS.TrafficApplication;
    CS.install_direction = CS.TrafficRead;
    CS.install_material = Ghost.reveal material;
  };
  let role_install = Ghost.hide {
    CS.install_role = CS.ServerEndpoint;
    CS.install_payload = Ghost.reveal install;
  };

  unfold (connection_exactly s 'st0);
  CLH.install_client_application_read_traffic_keys_from_material
    s
    traffic_secret_src
    traffic_key_src
    traffic_iv_src
    #material;
  fold (connection_exactly
    s
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let delta = Ghost.hide {
    CS.delta_event =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install));
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  CM.lemma_installed_traffic_keys_for_role_state_evolves
    'st0
    (Ghost.reveal role_install);
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallClientApplicationTrafficKeys
    B.empty
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallClientApplicationTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallClientApplicationTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
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
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalInstallServerApplicationTrafficKeys
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CLH.derive_and_install_server_application_write_traffic_keys s;
  with material.
    assert (CR.connection_exactly
      s
      (CM.installed_traffic_keys_for_role_state 'st0 {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = material;
        };
      }));
  let install = Ghost.hide {
    CS.install_epoch = CS.TrafficApplication;
    CS.install_direction = CS.TrafficWrite;
    CS.install_material = material;
  };
  let role_install = Ghost.hide {
    CS.install_role = CS.ServerEndpoint;
    CS.install_payload = Ghost.reveal install;
  };
  fold (connection_exactly
    s
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let delta = Ghost.hide {
    CS.delta_event =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install));
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallServerApplicationTrafficKeys
    B.empty
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallServerApplicationTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallServerApplicationTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
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
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalInstallClientApplicationTrafficKeys
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CLH.derive_and_install_client_application_read_traffic_keys s;
  with material.
    assert (CR.connection_exactly
      s
      (CM.installed_traffic_keys_for_role_state 'st0 {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = material;
        };
      }));
  let install = Ghost.hide {
    CS.install_epoch = CS.TrafficApplication;
    CS.install_direction = CS.TrafficRead;
    CS.install_material = material;
  };
  let role_install = Ghost.hide {
    CS.install_role = CS.ServerEndpoint;
    CS.install_payload = Ghost.reveal install;
  };
  fold (connection_exactly
    s
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let delta = Ghost.hide {
    CS.delta_event =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install));
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallClientApplicationTrafficKeys
    B.empty
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallClientApplicationTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install))
    resp
    ST.LocalInstallClientApplicationTrafficKeys
    B.empty
    'old_network_out
    'old_app_out));
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
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                        'st0
                        st1
                        resp
                        ST.LocalVerifyClientFinished
                        B.empty
                        network_out_bytes
                        app_out_bytes)
{
  let fin = Ghost.hide
    (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  assert (pure ('st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    Some (Ghost.reveal fin)));
  assert (pure (CM.can_verify_client_finished 'st0 (Ghost.reveal fin)));
  W.lemma_serialize_finished_len (Ghost.reveal fin);
  assert (pure (B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
    Bounds.max_transcript_len));
  unfold (connection_exactly s 'st0);
  CLA.mark_verified_stored_client_finished
    s
    #fin;
  fold (connection_exactly
    s
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let delta = Ghost.hide {
    CS.delta_event =
      CS.ConnLocalEvent (CS.LocalVerifyClientFinished (Ghost.reveal fin));
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  CM.lemma_verified_client_finished_state_evolves 'st0 (Ghost.reveal fin);
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.verified_client_finished_state 'st0 (Ghost.reveal fin)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.verified_client_finished_state 'st0 (Ghost.reveal fin)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))
    resp
    (CS.ConnLocalEvent (CS.LocalVerifyClientFinished (Ghost.reveal fin)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))
    resp
    ST.LocalVerifyClientFinished
    B.empty
    (CS.ConnLocalEvent (CS.LocalVerifyClientFinished (Ghost.reveal fin)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))
    resp
    ST.LocalVerifyClientFinished
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))
    resp
    ST.LocalVerifyClientFinished
    B.empty
    'old_network_out
    'old_app_out));
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
  unfold (connection_exactly s 'st0);
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
    kind
    (Ghost.reveal 'payload_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    'old_network_out
    'old_app_out));
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
  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.handshake_exactly s.handshake 'st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (CR.sized_bytes_exactly
    s.handshake.transcript
    Bounds.max_transcript_len
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !s.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (CR.byte_prefix_matches
    old_transcript_storage
    transcript_len
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (Seq.equal
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice old_transcript_storage 0 (SZ.v transcript_len))));
  Seq.lemma_eq_intro
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice old_transcript_storage 0 (SZ.v transcript_len));

  V.to_array_pts_to s.handshake.transcript.bytes;
  let mut transcript_hash = [| 0uy; 32sz |];
  Crypto.sha256_prefix
    (V.vec_to_array s.handshake.transcript.bytes)
    transcript_len
    transcript_hash;
  V.to_vec_pts_to s.handshake.transcript.bytes;
  with transcript_hash_bytes. assert (pts_to transcript_hash transcript_hash_bytes);
  assert (pure (transcript_hash_bytes ==
    Tr.hash 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  let mut certificate_verify_input = [| 0uy; 130sz |];
  Ser.build_server_certificate_verify_input
    transcript_hash
    certificate_verify_input
    130sz;
  with certificate_verify_input_bytes.
    assert (pts_to certificate_verify_input certificate_verify_input_bytes);
  assert (pure (B.length certificate_verify_input_bytes == 130));
  assert (pure (B.length transcript_hash_bytes == 32));
  assert (pure (Seq.equal
    (Ghost.reveal certificate_verify_input_bytes)
    (W.serialize_server_certificate_verify_input (Ghost.reveal transcript_hash_bytes))));
  W.lemma_serialize_server_certificate_verify_input_len32
    (Ghost.reveal transcript_hash_bytes);
  assert (pure (Seq.equal
    (W.serialize_server_certificate_verify_input (Ghost.reveal transcript_hash_bytes))
    (H.certificate_verify_input (Ghost.reveal transcript_hash_bytes))));
  assert (pure (Seq.equal
    (Ghost.reveal certificate_verify_input_bytes)
    (H.certificate_verify_input
      (Tr.hash 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript))));
  Seq.lemma_len_slice certificate_verify_input_bytes 0 130;
  Seq.lemma_eq_intro
    certificate_verify_input_bytes
    (Seq.slice certificate_verify_input_bytes 0 130);

  fold (CR.sized_bytes_exactly
    s.handshake.transcript
    Bounds.max_transcript_len
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (CR.handshake_exactly s.handshake 'st0.CS.cs_model.CS.model_handshake);
  fold (CR.connection_model_exactly s 'st0.CS.cs_model);
  fold (connection_exactly s 'st0);

  assert_norm (IM.max_signature_len == 4096);
  let signature_vec = V.alloc 0uy 4096sz;
  with old_signature_bytes. assert (V.pts_to signature_vec old_signature_bytes);
  assert (pure (V.is_full_vec signature_vec));
  assert (pure (V.length signature_vec == IM.max_signature_len));
  assert (pure (B.length old_signature_bytes == IM.max_signature_len));
  V.to_array_pts_to signature_vec;
  let sign_result =
    O.sign_certificate_verify
      creds
      certificate_verify_input
      130sz
      (V.vec_to_array signature_vec)
      4096sz;
  match sign_result {
    None -> {
      V.to_vec_pts_to signature_vec;
      V.free signature_vec;
      let mut empty_payload = [| 0uy; 0sz |];
      process_local_unexpected_message
        s
        ST.LocalSignCertificateVerify
        empty_payload
        0sz
        network_out
        network_out_len
        app_out
        app_out_len
    }
    Some signature_len -> {
      with signature_bytes.
        assert (pts_to (V.vec_to_array signature_vec) signature_bytes);
      assert (pure (B.length signature_bytes == 4096));
      assert (pure (SZ.v signature_len <= 4096));
      assert (pure (SZ.v signature_len <= B.length signature_bytes));
      Seq.lemma_len_slice signature_bytes 0 (SZ.v signature_len);
      let signature : erased B.bytes =
        Ghost.hide (Seq.slice signature_bytes 0 (SZ.v signature_len));
      assert (pure (Seq.equal
        (Ghost.reveal signature)
        (Seq.slice signature_bytes 0 (SZ.v signature_len))));
      assert (pure (B.length (Ghost.reveal signature) == SZ.v signature_len));
      assert (pure (TLS13.Crypto.Spec.verify_signature
        T.RsaPssRsaeSha256
        (Ghost.reveal 'credential_identity)
        (Seq.slice (Ghost.reveal certificate_verify_input_bytes) 0 130)
        (Ghost.reveal signature)));
      assert (pure (Seq.equal
        (Seq.slice (Ghost.reveal certificate_verify_input_bytes) 0 130)
        (H.certificate_verify_input
          (Tr.hash 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript))));
      assert (pure (TLS13.Crypto.Spec.verify_signature
        T.RsaPssRsaeSha256
        (Ghost.reveal 'credential_identity)
        (H.certificate_verify_input
          (Tr.hash 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript))
        (Ghost.reveal signature)));
      let cv : erased M.certificate_verify = Ghost.hide {
        M.scheme = T.RsaPssRsaeSha256;
        M.signature = Ghost.reveal signature;
      };
      let lcv = {
        IM.certificate_verify_scheme = 0x0804us;
        IM.certificate_verify_signature = signature_vec;
        IM.certificate_verify_signature_len = signature_len;
      };
      V.to_vec_pts_to signature_vec;
      assert (pure (lcv.IM.certificate_verify_signature == signature_vec));
      assert (pure (lcv.IM.certificate_verify_signature_len == signature_len));
      assert (pure (lcv.IM.certificate_verify_scheme == 0x0804us));
      rewrite (V.pts_to signature_vec signature_bytes)
        as (V.pts_to lcv.IM.certificate_verify_signature signature_bytes);
      assert_norm (IM.signature_scheme_matches 0x0804us T.RsaPssRsaeSha256);
      assert (pure (IM.byte_prefix_matches
        signature_bytes
        signature_len
        (Ghost.reveal cv).M.signature));
      fold (IM.is_valid_certificate_verify lcv (Ghost.reveal cv));

      assert (pure (CS.legal_event
        'st0.CS.cs_model
        (CS.ConnLocalEvent (CS.LocalSignCertificateVerify (Ghost.reveal cv)))));
      assert (pure (CM.can_sign_certificate_verify 'st0 (Ghost.reveal cv)));
      unfold (connection_exactly s 'st0);
      CLH.mark_signed_certificate_verify
        s
        lcv
        #cv;
      fold (connection_exactly s (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv)));

      let resp = {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.StepOk;
      };
      let delta = Ghost.hide {
        CS.delta_event =
          CS.ConnLocalEvent (CS.LocalSignCertificateVerify (Ghost.reveal cv));
        CS.delta_raw_sent = B.empty;
        CS.delta_raw_received = B.empty;
      };
      CM.lemma_signed_certificate_verify_state_evolves 'st0 (Ghost.reveal cv);
      assert (pure (CS.legal_connection_delta
        'st0
        (Ghost.reveal delta)
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))));
      CSL.lemma_legal_connection_delta_full_log_consistent_for_role
        CS.ServerEndpoint
        'st0
        (Ghost.reveal delta)
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv));
      CSL.lemma_legal_connection_delta_raw_event_replay_consistent
        'st0
        (Ghost.reveal delta)
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv));
      CSL.lemma_connection_state_protected_raw_segmented_replay
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv));
      CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
        'st0
        (Ghost.reveal delta)
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv));
      CSL.lemma_legal_connection_delta_received_decode_replay_consistent
        'st0
        (Ghost.reveal delta)
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv));
      Seq.lemma_len_slice 'old_network_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
      Seq.lemma_len_slice 'old_app_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
      assert (pure ((CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv)).CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      assert (pure ((CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv)).CS.cs_model.CS.model_config.CS.config_role ==
        CS.ServerEndpoint));
      assert (pure (Some?
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv)).CS.cs_model.CS.model_config.CS.config_server));
      assert (pure (ST.server_state_correct
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))));
      assert (pure (ST.server_raw_to_message_replay_consistent
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))));
      assert (pure (ST.server_end_to_end_invariant
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))));
      assert (pure (ST.legal_response_for_event
        'st0
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))
        resp
        (CS.ConnLocalEvent (CS.LocalSignCertificateVerify (Ghost.reveal cv)))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (ST.legal_local_response
        'st0
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))
        resp
        ST.LocalSignCertificateVerify
        B.empty
        (CS.ConnLocalEvent (CS.LocalSignCertificateVerify (Ghost.reveal cv)))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (ST.legal_handled_local_response
        'st0
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))
        resp
        ST.LocalSignCertificateVerify
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (ST.server_local_event_end_to_end_correct
        'st0
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))
        resp
        ST.LocalSignCertificateVerify
        B.empty
        'old_network_out
        'old_app_out));
      resp
    }
  }
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
                 (W.serialize_handshake (M.ClientHello ch)) /\
               lch.IM.client_hello_has_server_name == true /\
               CM.client_hello_server_name_len_for ch ==
                 lch.IM.client_hello_server_name_len /\
               CM.client_hello_cipher_suites_len_for ch ==
                 lch.IM.client_hello_cipher_suites_len /\
               CM.client_hello_signature_schemes_len_for ch ==
                 lch.IM.client_hello_signature_schemes_len /\
               'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None /\
               B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                 B.length (W.serialize_handshake (M.ClientHello ch)) <=
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
              ST.server_network_event_end_to_end_correct
                'st0
                st1
                resp
                (M.TlsHandshake (M.ClientHello ch))
                (Ghost.reveal 'raw_bytes)
                network_out_bytes
                app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CN.mark_received_client_hello
    s
    raw
    fragment
    fragment_len
    lch
    #ch;
  IM.free_client_hello lch;
  fold (connection_exactly
    s
    (CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  CM.lemma_received_client_hello_state_evolves
    'st0
    ch
    (Ghost.reveal 'raw_bytes);
  assert (pure (CS.legal_connection_delta
    'st0
    (ST.received_message_delta
      (M.TlsHandshake (M.ClientHello ch))
      (Ghost.reveal 'raw_bytes))
    (CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (ST.received_message_delta
      (M.TlsHandshake (M.ClientHello ch))
      (Ghost.reveal 'raw_bytes))
    (CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsHandshake (M.ClientHello ch))
      (Ghost.reveal 'raw_bytes))
    (CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsHandshake (M.ClientHello ch))
      (Ghost.reveal 'raw_bytes))
    (CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsHandshake (M.ClientHello ch))
      (Ghost.reveal 'raw_bytes))
    (CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes))
    resp
    (ST.received_message_event (M.TlsHandshake (M.ClientHello ch)))
    B.empty
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_network_response
    'st0
    (CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes))
    resp
    (M.TlsHandshake (M.ClientHello ch))
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_network_event_end_to_end_correct
    'st0
    (CM.received_client_hello_state 'st0 ch (Ghost.reveal 'raw_bytes))
    resp
    (M.TlsHandshake (M.ClientHello ch))
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  resp
}
