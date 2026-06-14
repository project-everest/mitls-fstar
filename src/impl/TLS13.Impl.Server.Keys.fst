module TLS13.Impl.Server.Keys

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

fn process_derive_shared_secret_from_private_array
  (s:server)
  (server_private_key:array U8.t)
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
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsClientHelloReceived /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
                  | Some selection ->
                    CS.server_selection_key_share_consistent selection /\
                    'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
                      Some selection.CS.server_selected_client_hello /\
                    Some? selection.CS.server_key_share_private /\
                    Some?.v selection.CS.server_key_share_private ==
                      Ghost.reveal 'server_private_key_bytes
                  | None -> False))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to server_private_key 'server_private_key_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalDeriveSharedSecret
                  (Ghost.reveal 'server_private_key_bytes)
                  network_out_bytes
                  app_out_bytes /\
                (resp.ST.status == ST.StepOk ==>
                  (exists shared.
                    st1 == CM.derived_shared_secret_state 'st0 shared /\
                    (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
                     | Some ch ->
                       TLS13.Crypto.Spec.x25519_shared
                         (Ghost.reveal 'server_private_key_bytes)
                         ch.M.key_share == Some shared
                     | None -> False))) /\
                (resp.ST.status == ST.IllegalTransition ==>
                  ST.unexpected_message_response
                    'st0
                    st1
                    resp
                    network_out_bytes
                    app_out_bytes))
{
  unfold (connection_exactly s 'st0);
  let ok =
    CLH.try_derive_server_shared_secret_from_private_array
      s
      server_private_key;
  if ok {
    with shared.
      assert (CR.connection_exactly s (CM.derived_shared_secret_state 'st0 shared) **
              pts_to server_private_key 'server_private_key_bytes);
    let shared_e = Ghost.hide shared;
    fold (connection_exactly s (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e)));
    let resp = {
      ST.network_out_len = 0sz;
      ST.app_out_len = 0sz;
      ST.status = ST.StepOk;
    };

    let delta = Ghost.hide {
      CS.delta_event =
        CS.ConnLocalEvent
          (CS.LocalDeriveSharedSecret (Ghost.reveal shared_e));
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    };
    CM.lemma_derived_shared_secret_state_evolves
      'st0
      (Ghost.reveal shared_e);
    assert (pure (CS.legal_connection_delta
      'st0
      (Ghost.reveal delta)
      (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e))));

    CSL.lemma_legal_connection_delta_full_log_consistent_for_role
      CS.ServerEndpoint
      'st0
      (Ghost.reveal delta)
      (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e));
    CSL.lemma_legal_connection_delta_raw_event_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e));
    CSL.lemma_connection_state_protected_raw_segmented_replay
      (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e));
    CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e));
    CSL.lemma_legal_connection_delta_received_decode_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e));

    Seq.lemma_len_slice 'old_network_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
    Seq.lemma_len_slice 'old_app_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

    assert (pure ((CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e)).CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    assert (pure ((CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e)).CS.cs_model.CS.model_config.CS.config_role ==
      CS.ServerEndpoint));
    assert (pure (Some?
      (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e)).CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (ST.server_state_correct
      (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e))));
    assert (pure (ST.server_raw_to_message_replay_consistent
      (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e))));
    assert (pure (ST.server_end_to_end_invariant
      (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e))));

    assert (pure (ST.legal_response_for_event
      'st0
      (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e))
      resp
      (CS.ConnLocalEvent
        (CS.LocalDeriveSharedSecret (Ghost.reveal shared_e)))
      B.empty
      B.empty
      'old_network_out
      'old_app_out));
    assert (pure (ST.legal_local_response
      'st0
      (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e))
      resp
      ST.LocalDeriveSharedSecret
      (Ghost.reveal 'server_private_key_bytes)
      (CS.ConnLocalEvent
        (CS.LocalDeriveSharedSecret (Ghost.reveal shared_e)))
      B.empty
      B.empty
      'old_network_out
      'old_app_out));
    assert (pure (ST.legal_handled_local_response
      'st0
      (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e))
      resp
      ST.LocalDeriveSharedSecret
      (Ghost.reveal 'server_private_key_bytes)
      'old_network_out
      'old_app_out));
    assert (pure (ST.server_local_event_end_to_end_correct
      'st0
      (CM.derived_shared_secret_state 'st0 (Ghost.reveal shared_e))
      resp
      ST.LocalDeriveSharedSecret
      (Ghost.reveal 'server_private_key_bytes)
      'old_network_out
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
      ST.LocalDeriveSharedSecret
      (Ghost.reveal 'server_private_key_bytes)
      'old_network_out
      'old_app_out));
    assert (pure (ST.server_local_event_end_to_end_correct
      'st0
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
      resp
      ST.LocalDeriveSharedSecret
      (Ghost.reveal 'server_private_key_bytes)
      'old_network_out
      'old_app_out));
    resp
  }
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
  assert (pure (Ghost.reveal role_install == {
    CS.install_role = CS.ServerEndpoint;
    CS.install_payload = {
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = material;
    };
  }));
  rewrite
    (connection_exactly
      s
      (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)))
    as
    (connection_exactly
      s
      (CM.installed_traffic_keys_for_role_state 'st0 {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = material;
        };
      }));
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
  assert (pure (Ghost.reveal role_install == {
    CS.install_role = CS.ServerEndpoint;
    CS.install_payload = {
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = material;
    };
  }));
  rewrite
    (connection_exactly
      s
      (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)))
    as
    (connection_exactly
      s
      (CM.installed_traffic_keys_for_role_state 'st0 {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = material;
        };
      }));
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
  assert (pure (Ghost.reveal role_install == {
    CS.install_role = CS.ServerEndpoint;
    CS.install_payload = {
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = material;
    };
  }));
  rewrite
    (connection_exactly
      s
      (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)))
    as
    (connection_exactly
      s
      (CM.installed_traffic_keys_for_role_state 'st0 {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = material;
        };
      }));
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
  assert (pure (Ghost.reveal role_install == {
    CS.install_role = CS.ServerEndpoint;
    CS.install_payload = {
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = material;
    };
  }));
  rewrite
    (connection_exactly
      s
      (CM.installed_traffic_keys_for_role_state 'st0 (Ghost.reveal role_install)))
    as
    (connection_exactly
      s
      (CM.installed_traffic_keys_for_role_state 'st0 {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = material;
        };
      }));
  resp
}
