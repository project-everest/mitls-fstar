module TLS13.Impl.Server

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module ST = TLS13.Impl.Server.Types
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
                CS.connection_state_raw_to_message_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                CS.connection_state_sent_seal_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                CS.connection_state_sent_seal_key_schedule_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                CS.connection_state_received_decode_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                CS.connection_state_received_decode_key_schedule_replay_consistent
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
  CSL.lemma_initial_raw_to_message_replay_consistent
    (CR.server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes));
  CSL.lemma_initial_sent_seal_replay_consistent
    (CR.server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes));
  CSL.lemma_initial_sent_seal_key_schedule_replay_consistent
    (CR.server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes));
  CSL.lemma_initial_received_decode_replay_consistent
    (CR.server_connection_config
      (Ghost.reveal 'certificate_chain_bytes)
      (Ghost.reveal 'credential_identity_bytes));
  CSL.lemma_initial_received_decode_key_schedule_replay_consistent
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
