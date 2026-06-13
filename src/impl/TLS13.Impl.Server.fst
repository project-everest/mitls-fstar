module TLS13.Impl.Server

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CM = TLS13.Impl.ConnectionState.Model
module CLH = TLS13.Impl.ConnectionState.LocalHandshake
module CN = TLS13.Impl.ConnectionState.Network
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module IM = TLS13.Impl.Messages
module M = TLS13.Messages
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
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
                  B.empty
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
    B.empty
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
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared))
    resp
    ST.LocalDeriveSharedSecret
    B.empty
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
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
    }
    ST.LocalInstallClientApplicationTrafficKeys -> {
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
    }
    ST.LocalInstallServerApplicationTrafficKeys -> {
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
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
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
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
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
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
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
    }
    ST.LocalSendServerFinished -> {
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
    }
    ST.LocalSendApplicationData -> {
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
    }
    ST.LocalSendCloseNotify -> {
      assert (pure False);
      {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.IllegalTransition;
      }
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
