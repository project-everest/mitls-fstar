module TLS13.Impl.Server.Setup

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module Crypto = TLS13.Crypto
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module CM = TLS13.Impl.ConnectionState.Model
module CLH = TLS13.Impl.ConnectionState.LocalHandshake
module CR = TLS13.Impl.ConnectionState.Repr
module M = TLS13.Messages
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

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
                st1 == CM.started_server_state 'st0 /\
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

  let delta : erased CS.connection_delta = Ghost.hide {
    CS.delta_event = CS.ConnLocalEvent CS.LocalStartServer;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.started_server_state 'st0)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.started_server_state 'st0);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.started_server_state 'st0);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.started_server_state 'st0);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.started_server_state 'st0);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
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
                 CM.can_select_server_parameters 'st0 selection /\
                 // The runtime stores no group tag; since G2 stage S6.8d
                 // CR.server_selection_group_pinned records that the selected
                 // group is the one the stored ClientHello's accepted offer
                 // names, and the runtime reads it off the metadata box.
                 CS.server_selected_kex_group selection == CM.stored_client_hello_kex_group 'st0 /\
                 CR.server_selection_absent
                   'st0.CS.cs_model.CS.model_handshake /\
                 CR.server_selection_private_absent selection)
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

fn process_select_server_parameters_with_private_from_array
  (s:server)
  (server_private_key:array U8.t)
  (#selection:erased CS.server_handshake_selection)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to server_private_key 'server_private_key_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'server_private_key_bytes == 32 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CM.can_select_server_parameters 'st0 selection /\
                 // The runtime stores no group tag; since G2 stage S6.8d
                 // CR.server_selection_group_pinned records that the selected
                 // group is the one the stored ClientHello's accepted offer
                 // names, and the runtime reads it off the metadata box.
                 CS.server_selected_kex_group selection == CM.stored_client_hello_kex_group 'st0 /\
                 CR.server_selection_absent
                   'st0.CS.cs_model.CS.model_handshake /\
                 Some? selection.CS.server_key_share_private /\
                 Some?.v selection.CS.server_key_share_private ==
                   Ghost.reveal 'server_private_key_bytes)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to server_private_key 'server_private_key_bytes **
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
  unfold (connection_exactly s 'st0);
  CLH.select_server_parameters_with_private_from_array
    s
    server_private_key
    #selection;
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

#push-options "--z3rlimit 30"
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
                 CR.server_selection_absent
                   'st0.CS.cs_model.CS.model_handshake /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (let ch =
                    Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello in
                  let cfg =
                    Some?.v 'st0.CS.cs_model.CS.model_config.CS.config_server in
                  let selection = {
                    CS.server_selected_client_hello = ch;
                    CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
                    CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (ch));
                    CS.server_selected_signature_scheme =
                      CryptoSpec.credential_signature_scheme
                        (cfg.CS.server_credential_identity);
                    CS.server_random = Ghost.reveal 'server_random_bytes;
                    CS.server_key_share_private = None;
                    CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
                    CS.server_p256_private = None;
                    CS.server_p256_public = CS.server_p256_absent;
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
                      CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
                      CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (ch));
                      CS.server_selected_signature_scheme =
                        CryptoSpec.credential_signature_scheme
                          (cfg.CS.server_credential_identity);
                      CS.server_random = Ghost.reveal 'server_random_bytes;
                      CS.server_key_share_private = None;
                      CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
                      CS.server_p256_private = None;
                      CS.server_p256_public = CS.server_p256_absent;
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
  let ch =
    Ghost.hide (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  let cfg =
    Ghost.hide (Some?.v 'st0.CS.cs_model.CS.model_config.CS.config_server);
  let selection = Ghost.hide {
    CS.server_selected_client_hello = Ghost.reveal ch;
    CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
    CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (Ghost.reveal ch));
    CS.server_selected_signature_scheme =
      CryptoSpec.credential_signature_scheme
        ((Ghost.reveal cfg).CS.server_credential_identity);
    CS.server_random = Ghost.reveal 'server_random_bytes;
    CS.server_key_share_private = None;
    CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
    CS.server_p256_private = None;
    CS.server_p256_public = CS.server_p256_absent;
    CS.server_selected_credential =
      (Ghost.reveal cfg).CS.server_credential_identity;
  };
  assert (pure (CM.can_select_server_parameters
    'st0
    (Ghost.reveal selection)));
  // Naming every conjunct of process_select_server_parameters' precondition
  // individually.  The precondition grew a group conjunct in G2 stage S4/S5, and
  // discharging it inside the call's whole VC destabilises the surrounding
  // Pulse frame (the same failure mode, and the same remedy, as stage S2).
  assert (pure (CS.server_selected_kex_group (Ghost.reveal selection) ==
    CM.stored_client_hello_kex_group 'st0));
  assert (pure (CR.server_selection_absent 'st0.CS.cs_model.CS.model_handshake));
  assert (pure (CR.server_selection_private_absent (Ghost.reveal selection)));
  assert (pure (ST.server_end_to_end_invariant 'st0));
  let resp =
    process_select_server_parameters
      s
      #selection
      network_out
      network_out_len
      app_out
      app_out_len;
  // Naming the callee's own conclusion.  Relaying it straight into this
  // function's postcondition puts the (now larger) selection vocabulary and the
  // record literal into one VC; naming it first keeps the two apart.
  with st1 nob aob.
    assert (connection_exactly s st1 **
            pts_to network_out nob **
            pts_to app_out aob);
  assert (pure (st1 == CM.selected_server_parameters_state 'st0 (Ghost.reveal selection)));
  assert (pure (B.length nob == SZ.v network_out_len /\
                B.length aob == SZ.v app_out_len));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0 st1 resp ST.LocalSelectServerParameters B.empty nob aob));
  resp
}

#pop-options

fn process_select_default_server_parameters_with_private_from_arrays
  (s:server)
  (server_random:array U8.t)
  (server_private_key:array U8.t)
  (server_key_share:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to server_random 'server_random_bytes **
           pts_to server_private_key 'server_private_key_bytes **
           pts_to server_key_share 'server_key_share_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'server_random_bytes == 32 /\
                 B.length 'server_private_key_bytes == 32 /\
                 B.length 'server_key_share_bytes == 32 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CR.server_selection_absent
                   'st0.CS.cs_model.CS.model_handshake /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (let ch =
                    Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello in
                  let cfg =
                    Some?.v 'st0.CS.cs_model.CS.model_config.CS.config_server in
                  let selection = {
                    CS.server_selected_client_hello = ch;
                    CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
                    CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (ch));
                    CS.server_selected_signature_scheme =
                      CryptoSpec.credential_signature_scheme
                        (cfg.CS.server_credential_identity);
                    CS.server_random = Ghost.reveal 'server_random_bytes;
                    CS.server_key_share_private =
                      Some (Ghost.reveal 'server_private_key_bytes);
                    CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
                    CS.server_p256_private = Some (Ghost.reveal 'server_private_key_bytes);
                    CS.server_p256_public =
                      CryptoSpec.p256_public_from_private (Ghost.reveal 'server_private_key_bytes);
                    CS.server_selected_credential =
                      cfg.CS.server_credential_identity;
                  } in
                  CM.can_select_server_parameters 'st0 selection))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to server_random 'server_random_bytes **
          pts_to server_private_key 'server_private_key_bytes **
          pts_to server_key_share 'server_key_share_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (B.length (Ghost.reveal 'server_random_bytes) == 32 /\
                 B.length (Ghost.reveal 'server_private_key_bytes) == 32 /\
                 B.length (Ghost.reveal 'server_key_share_bytes) == 32 ==>
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                        'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some ch, Some cfg ->
                    let selection = {
                      CS.server_selected_client_hello = ch;
                      CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
                      CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (ch));
                      CS.server_selected_signature_scheme =
                        CryptoSpec.credential_signature_scheme
                          (cfg.CS.server_credential_identity);
                      CS.server_random = Ghost.reveal 'server_random_bytes;
                      CS.server_key_share_private =
                        Some (Ghost.reveal 'server_private_key_bytes);
                      CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
                      CS.server_p256_private = Some (Ghost.reveal 'server_private_key_bytes);
                      CS.server_p256_public =
                        CryptoSpec.p256_public_from_private (Ghost.reveal 'server_private_key_bytes);
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
  let ch =
    Ghost.hide (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  let cfg =
    Ghost.hide (Some?.v 'st0.CS.cs_model.CS.model_config.CS.config_server);
  let selection = Ghost.hide {
    CS.server_selected_client_hello = Ghost.reveal ch;
    CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
    CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (Ghost.reveal ch));
    CS.server_selected_signature_scheme =
      CryptoSpec.credential_signature_scheme
        ((Ghost.reveal cfg).CS.server_credential_identity);
    CS.server_random = Ghost.reveal 'server_random_bytes;
    CS.server_key_share_private = Some (Ghost.reveal 'server_private_key_bytes);
    CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
    CS.server_p256_private = Some (Ghost.reveal 'server_private_key_bytes);
    CS.server_p256_public =
      CryptoSpec.p256_public_from_private (Ghost.reveal 'server_private_key_bytes);
    CS.server_selected_credential =
      (Ghost.reveal cfg).CS.server_credential_identity;
  };
  assert (pure (CM.can_select_server_parameters
    'st0
    (Ghost.reveal selection)));
  // Naming every conjunct of process_select_server_parameters' precondition
  // individually.  The precondition grew a group conjunct in G2 stage S4/S5, and
  // discharging it inside the call's whole VC destabilises the surrounding
  // Pulse frame (the same failure mode, and the same remedy, as stage S2).
  assert (pure (CS.server_selected_kex_group (Ghost.reveal selection) ==
    CM.stored_client_hello_kex_group 'st0));
  assert (pure (CR.server_selection_absent 'st0.CS.cs_model.CS.model_handshake));
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (Some? (Ghost.reveal selection).CS.server_key_share_private));
  assert (pure (Some?.v (Ghost.reveal selection).CS.server_key_share_private ==
    Ghost.reveal 'server_private_key_bytes));
  process_select_server_parameters_with_private_from_array
    s
    server_private_key
    #selection
    network_out
    network_out_len
    app_out
    app_out_len
}

fn process_select_default_server_parameters_with_derived_public_from_private_array
  (s:server)
  (server_random:array U8.t)
  (server_private_key:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to server_random 'server_random_bytes **
           pts_to server_private_key 'server_private_key_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'server_random_bytes == 32 /\
                 B.length 'server_private_key_bytes == 32 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CR.server_selection_absent
                  'st0.CS.cs_model.CS.model_handshake /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (let ch =
                   Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello in
                  let cfg =
                   Some?.v 'st0.CS.cs_model.CS.model_config.CS.config_server in
                  let selection = {
                   CS.server_selected_client_hello = ch;
                   CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
                   CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (ch));
                   CS.server_selected_signature_scheme =
                     CryptoSpec.credential_signature_scheme
                       (cfg.CS.server_credential_identity);
                   CS.server_random = Ghost.reveal 'server_random_bytes;
                   CS.server_key_share_private =
                     Some (Ghost.reveal 'server_private_key_bytes);
                   CS.server_key_share_public =
                     CryptoSpec.x25519_public_from_private
                       (Ghost.reveal 'server_private_key_bytes);
                   CS.server_p256_private = Some (Ghost.reveal 'server_private_key_bytes);
                   CS.server_p256_public =
                     CryptoSpec.p256_public_from_private (Ghost.reveal 'server_private_key_bytes);
                   CS.server_selected_credential =
                     cfg.CS.server_credential_identity;
                  } in
                  CM.can_select_server_parameters 'st0 selection))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to server_random 'server_random_bytes **
          pts_to server_private_key 'server_private_key_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (B.length (Ghost.reveal 'server_random_bytes) == 32 /\
                 B.length (Ghost.reveal 'server_private_key_bytes) == 32 ==>
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                       'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some ch, Some cfg ->
                   let selection = {
                     CS.server_selected_client_hello = ch;
                     CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
                     CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (ch));
                     CS.server_selected_signature_scheme =
                       CryptoSpec.credential_signature_scheme
                         (cfg.CS.server_credential_identity);
                     CS.server_random = Ghost.reveal 'server_random_bytes;
                     CS.server_key_share_private =
                       Some (Ghost.reveal 'server_private_key_bytes);
                     CS.server_key_share_public =
                       CryptoSpec.x25519_public_from_private
                         (Ghost.reveal 'server_private_key_bytes);
                     CS.server_p256_private = Some (Ghost.reveal 'server_private_key_bytes);
                     CS.server_p256_public =
                       CryptoSpec.p256_public_from_private (Ghost.reveal 'server_private_key_bytes);
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
  let mut server_key_share = [| 0uy; 32sz |];
  Crypto.x25519_public_from_private server_private_key server_key_share;
  with server_key_share_bytes. assert (pts_to server_key_share server_key_share_bytes);
  assert (pure (server_key_share_bytes ==
    CryptoSpec.x25519_public_from_private (Ghost.reveal 'server_private_key_bytes)));
  assert (pure (B.length server_key_share_bytes == 32));
  let ch =
    Ghost.hide (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  let cfg =
    Ghost.hide (Some?.v 'st0.CS.cs_model.CS.model_config.CS.config_server);
  let selection = Ghost.hide {
    CS.server_selected_client_hello = Ghost.reveal ch;
    CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
    CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (Ghost.reveal ch));
    CS.server_selected_signature_scheme =
      CryptoSpec.credential_signature_scheme
        ((Ghost.reveal cfg).CS.server_credential_identity);
    CS.server_random = Ghost.reveal 'server_random_bytes;
    CS.server_key_share_private = Some (Ghost.reveal 'server_private_key_bytes);
    CS.server_key_share_public = server_key_share_bytes;
    CS.server_p256_private = Some (Ghost.reveal 'server_private_key_bytes);
    CS.server_p256_public =
      CryptoSpec.p256_public_from_private (Ghost.reveal 'server_private_key_bytes);
    CS.server_selected_credential =
      (Ghost.reveal cfg).CS.server_credential_identity;
  };
  assert (pure (CM.can_select_server_parameters
    'st0
    (Ghost.reveal selection)));
  // Naming every conjunct of process_select_server_parameters' precondition
  // individually.  The precondition grew a group conjunct in G2 stage S4/S5, and
  // discharging it inside the call's whole VC destabilises the surrounding
  // Pulse frame (the same failure mode, and the same remedy, as stage S2).
  assert (pure (CS.server_selected_kex_group (Ghost.reveal selection) ==
    CM.stored_client_hello_kex_group 'st0));
  assert (pure (CR.server_selection_absent 'st0.CS.cs_model.CS.model_handshake));
  assert (pure (ST.server_end_to_end_invariant 'st0));
  let resp = process_select_default_server_parameters_with_private_from_arrays
    s
    server_random
    server_private_key
    server_key_share
    network_out
    network_out_len
    app_out
    app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (connection_exactly s st1 **
            pts_to server_random 'server_random_bytes **
            pts_to server_private_key 'server_private_key_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  assert (pure (st1 ==
    CM.selected_server_parameters_state 'st0 (Ghost.reveal selection)));
  resp
}
