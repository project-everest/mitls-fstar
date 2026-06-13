module TLS13.Impl.Server

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CM = TLS13.Impl.ConnectionState.Model
module CLH = TLS13.Impl.ConnectionState.LocalHandshake
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

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
  let start_ready = CQ.can_start_server_runtime s;
  fold (connection_exactly s 'st0);
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
  } else {
    {
      ST.next_local_ready = false;
      ST.next_local_kind = ST.LocalFail;
      ST.next_local_payload = ST.LocalPayloadNone;
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
