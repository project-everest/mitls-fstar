module TLS13.Impl.ConnectionState.LocalHandshake

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box { box, (!), (:=) }
open FStar.List.Tot

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CS = TLS13.Spec.ConnectionState
module H = TLS13.Handshake.Spec
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module KS = TLS13.KeySchedule
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Bounds = TLS13.Impl.ConnectionState.Bounds
module Model = TLS13.Impl.ConnectionState.Model
module Queries = TLS13.Impl.ConnectionState.Queries
module Repr = TLS13.Impl.ConnectionState.Repr
module Tags = TLS13.Impl.ConnectionState.Tags
module Arr = Pulse.Lib.Array
module ArrPts = Pulse.Lib.Array.PtsTo
module R = TLS13.Record.Spec
module Rec = TLS13.Record
module Ser = TLS13.Impl.Serializer
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.StateMachine
module Slice = Pulse.Lib.Slice
module SZ = FStar.SizeT
module T = TLS13.Types
module Tr = TLS13.Transcript
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec
module X = TLS13.X509.Spec

open TLS13.Impl.ConnectionState.Bounds
open TLS13.Impl.ConnectionState.Model
open TLS13.Impl.ConnectionState.Queries
open TLS13.Impl.ConnectionState.Repr

fn try_start_handshake
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* start.
               connection_exactly c (started_handshake_state st0 start) **
               pure (can_start_handshake st0 start /\
                     CS.legal_connection_delta
                       st0
                       {
                         CS.delta_event =
                           CS.ConnLocalEvent (CS.LocalStartHandshake start);
                         CS.delta_raw_sent = B.empty;
                         CS.delta_raw_received = B.empty;
                       }
                       (started_handshake_state st0 start))
           else
             connection_exactly c st0)
{
  let ready = can_start_handshake_runtime c;
  if ready {
    assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlNew));
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_start == None));

    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);
    with role validation_time. _;
    unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
    with old_control_tag old_stage_tag old_failure_present old_failure_code old_failure_alert. _;
    unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    with cv_verified server_finished_verified. _;
    unfold (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    with old_start_present. _;
    let old_has_start = !c.handshake.start.present;
    assert (pure (old_has_start == old_start_present));
    if old_has_start {
      fold (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      fold (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure);
      fold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    } else {
    assert (pure (old_start_present == false));
    rewrite (handshake_start_payload_exactly
      c.handshake.start
      old_start_present
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_payload_exactly
        c.handshake.start
        false
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    unfold (handshake_start_payload_exactly
      c.handshake.start
      false
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    unfold (handshake_start_fields_allocated c.handshake.start);

    let mut client_random = [| 0uy; 32sz |];
    let random_ok = Crypto.random_bytes client_random 32sz;
    with client_random_bytes. assert (ArrPts.pts_to client_random client_random_bytes);
    assert (pure (B.length client_random_bytes == 32));

    let mut private_key = [| 0uy; 32sz |];
    let private_ok = Crypto.random_bytes private_key 32sz;
    with private_key_bytes. assert (ArrPts.pts_to private_key private_key_bytes);
    assert (pure (B.length private_key_bytes == 32));

    let entropy_ok = random_ok && private_ok;
    if entropy_ok {
    assert (pure random_ok);
    assert (pure private_ok);

    let mut public_key = [| 0uy; 32sz |];
    Crypto.x25519_public_from_private private_key public_key;
    with public_key_bytes. assert (ArrPts.pts_to public_key public_key_bytes);
    assert (pure (public_key_bytes ==
      TLS13.Crypto.Spec.x25519_public_from_private private_key_bytes));
    assert (pure (B.length public_key_bytes == 32));

    let start = Ghost.hide ({
      CS.start_server_name =
        st0.CS.cs_model.CS.model_config.CS.config_server_name;
      CS.start_client_random = client_random_bytes;
      CS.start_client_key_share_private = Some private_key_bytes;
      CS.start_client_key_share_public = public_key_bytes;
      CS.start_cipher_suites =
        st0.CS.cs_model.CS.model_config.CS.config_cipher_suites;
      CS.start_signature_schemes =
        st0.CS.cs_model.CS.model_config.CS.config_signature_schemes;
    });

    copy_hostname_sized_bytes
      c.config.server_name
      c.handshake.start.server_name;
    unfold (fixed_bytes_allocated c.handshake.start.client_random 32);
    with old_start_random. assert (V.pts_to c.handshake.start.client_random old_start_random);
    copy_fixed32_array_to_vec
      client_random
      c.handshake.start.client_random;
    fold (fixed_bytes_exactly
      c.handshake.start.client_random
      32
      client_random_bytes);
    lemma_len32_refinement_tautology();
    assert (pure (Some? (Ghost.reveal start).CS.start_client_key_share_private));
    assert (pure (Some?.v (Ghost.reveal start).CS.start_client_key_share_private == private_key_bytes));
    unfold (optional_fixed_bytes_exactly
      c.handshake.start.client_key_share_private
      32
      None);
    with old_private_present old_private_storage. _;
    copy_fixed32_array_to_vec
      private_key
      c.handshake.start.client_key_share_private.bytes;
    c.handshake.start.client_key_share_private.present := true;
    with stored_private. assert (V.pts_to c.handshake.start.client_key_share_private.bytes stored_private);
    assert (pure (stored_private == private_key_bytes));
    assert (pure ((Ghost.reveal start).CS.start_client_key_share_private == Some stored_private));
    assert (pure (optional_fixed_bytes_match
      true
      stored_private
      32
      (Ghost.reveal start).CS.start_client_key_share_private));
    fold (optional_fixed_bytes_exactly
      c.handshake.start.client_key_share_private
      32
      (Ghost.reveal start).CS.start_client_key_share_private);
    unfold (fixed_bytes_allocated c.handshake.start.client_key_share_public 32);
    with old_start_public. assert (V.pts_to c.handshake.start.client_key_share_public old_start_public);
    copy_fixed32_array_to_vec
      public_key
      c.handshake.start.client_key_share_public;
    fold (fixed_bytes_exactly
      c.handshake.start.client_key_share_public
      32
      public_key_bytes);
    assert (pure (SZ.fits max_cipher_suites));
    copy_cipher_suite_list_storage
      c.config.cipher_suites
      c.handshake.start.cipher_suites
      max_cipher_suites
      #(st0.CS.cs_model.CS.model_config.CS.config_cipher_suites);
    assert (pure (SZ.fits max_signature_schemes));
    copy_signature_scheme_list_storage
      c.config.signature_schemes
      c.handshake.start.signature_schemes
      max_signature_schemes
      #(st0.CS.cs_model.CS.model_config.CS.config_signature_schemes);

    assert (pure (CS.start_matches_config
      st0.CS.cs_model.CS.model_config
      (Ghost.reveal start)));
    assert (pure (CS.handshake_start_key_share_consistent (Ghost.reveal start)));
    assert (pure (can_start_handshake st0 (Ghost.reveal start)));
    lemma_option_some_v (Ghost.reveal start).CS.start_client_key_share_private;
    assert (pure ((Ghost.reveal start).CS.start_client_key_share_private ==
      Some (Some?.v (Ghost.reveal start).CS.start_client_key_share_private)));
    assert (pure (Some (Some?.v (Ghost.reveal start).CS.start_client_key_share_private) ==
      (Ghost.reveal start).CS.start_client_key_share_private));

    c.handshake.start.present := true;
    fold (handshake_start_fields_exactly
      c.handshake.start
      (Ghost.reveal start));
    fold (handshake_start_payload_exactly
      c.handshake.start
      true
      (Some (Ghost.reveal start)));
    fold (handshake_start_exactly
      c.handshake.start
      (Some (Ghost.reveal start)));

    c.control.control_tag := 1uy;
    c.control.handshake_stage_tag := 1uy;
    fold (control_exactly
      c.control
      (CS.ControlHandshaking CS.HsStarted)
      st0.CS.cs_model.CS.model_failure);

    fold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
    assert (pure ((started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys));
    unfold (handshake_messages_exactly
      c.handshake.messages
      st0.CS.cs_model.CS.model_handshake);
    fold (handshake_messages_exactly
      c.handshake.messages
      (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake);
    unfold (server_key_share_exactly
      c.handshake.server_key_share
      st0.CS.cs_model.CS.model_handshake);
    fold (server_key_share_exactly
      c.handshake.server_key_share
      (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake);
    rewrite (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
      as (peer_exactly
        c.handshake.validated_peer
        (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    rewrite (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
      as (sized_bytes_exactly
        c.handshake.transcript
        max_transcript_len
        (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
    rewrite (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
      as (handshake_buffers_exactly
        c.handshake.buffers
        (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
    rewrite (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
      as (key_schedule_exactly
        c.handshake.keys
        (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (handshake_exactly
      c.handshake
      (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model.CS.model_handshake);
    fold (connection_model_exactly
      c
      (started_handshake_state st0 (Ghost.reveal start)).CS.cs_model);

    lemma_started_handshake_state_evolves st0 (Ghost.reveal start);
    MR.update c.ghost_state (started_handshake_state st0 (Ghost.reveal start));
    fold (connection_exactly c (started_handshake_state st0 (Ghost.reveal start)));
    true
    } else {
      fold (handshake_start_fields_allocated c.handshake.start);
      fold (handshake_start_payload_exactly
        c.handshake.start
        false
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      fold (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure);
      fold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    }
    }
  } else {
    false
  }
}

fn try_start_server
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (Some? st0.CS.cs_model.CS.model_config.CS.config_server)
  returns ok: bool
  ensures (if ok then
             connection_exactly c (started_server_state st0) **
             pure (can_start_server st0 /\
                   CS.legal_connection_delta
                     st0
                     {
                       CS.delta_event = CS.ConnLocalEvent CS.LocalStartServer;
                       CS.delta_raw_sent = B.empty;
                       CS.delta_raw_received = B.empty;
                     }
                     (started_server_state st0))
           else
             connection_exactly c st0)
{
  let ready = can_start_server_runtime c;
  if ready {
    assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlNew));
    assert (pure (st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure (Some? st0.CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnLocalEvent CS.LocalStartServer)));
    assert (pure (can_start_server st0));

    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
    with old_control_tag old_stage_tag old_failure_present old_failure_code old_failure_alert. _;

    c.control.control_tag := 1uy;
    c.control.handshake_stage_tag := 12uy;

    assert_norm (Tags.handshake_stage_tag_matches 12uy CS.HsAwaitingClientHello);
    assert (pure (Tags.control_state_matches
      1uy
      12uy
      old_failure_present
      old_failure_code
      old_failure_alert
      (CS.ControlHandshaking CS.HsAwaitingClientHello)));
    fold (control_exactly
      c.control
      (CS.ControlHandshaking CS.HsAwaitingClientHello)
      st0.CS.cs_model.CS.model_failure);

    fold (connection_model_exactly
      c
      (started_server_state st0).CS.cs_model);

    lemma_started_server_state_evolves st0;
    MR.update c.ghost_state (started_server_state st0);
    fold (connection_exactly c (started_server_state st0));
    true
  } else {
    false
  }
}

fn start_server
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (can_start_server st0)
  ensures connection_exactly c (started_server_state st0) **
          pure (CS.legal_connection_delta
            st0
            {
              CS.delta_event = CS.ConnLocalEvent CS.LocalStartServer;
              CS.delta_raw_sent = B.empty;
              CS.delta_raw_received = B.empty;
            }
            (started_server_state st0))
{
  assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlNew));
  assert (pure (st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
  assert (pure (Some? st0.CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent CS.LocalStartServer)));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  with old_control_tag old_stage_tag old_failure_present old_failure_code old_failure_alert. _;

  c.control.control_tag := 1uy;
  c.control.handshake_stage_tag := 12uy;

  assert_norm (Tags.handshake_stage_tag_matches 12uy CS.HsAwaitingClientHello);
  assert (pure (Tags.control_state_matches
    1uy
    12uy
    old_failure_present
    old_failure_code
    old_failure_alert
    (CS.ControlHandshaking CS.HsAwaitingClientHello)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsAwaitingClientHello)
    st0.CS.cs_model.CS.model_failure);

  fold (connection_model_exactly
    c
    (started_server_state st0).CS.cs_model);

  lemma_started_server_state_evolves st0;
  MR.update c.ghost_state (started_server_state st0);
  fold (connection_exactly c (started_server_state st0))
}

fn select_server_parameters
  (c:connection_state)
  (#selection:erased CS.server_handshake_selection)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (can_select_server_parameters st0 selection)
  ensures connection_exactly c (selected_server_parameters_state st0 selection) **
          pure (CS.legal_connection_delta
            st0
            {
              CS.delta_event =
                CS.ConnLocalEvent (CS.LocalSelectServerParameters selection);
              CS.delta_raw_sent = B.empty;
              CS.delta_raw_received = B.empty;
            }
            (selected_server_parameters_state st0 selection))
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived));
  assert (pure (st0.CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    Some (Ghost.reveal selection).CS.server_selected_client_hello));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalSelectServerParameters (Ghost.reveal selection)))));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);

  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_control ==
    st0.CS.cs_model.CS.model_control));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_failure ==
    st0.CS.cs_model.CS.model_failure));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_record ==
    st0.CS.cs_model.CS.model_record));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));

  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_messages_exactly
    c.handshake.messages
    (selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake);
  fold (handshake_exactly
    c.handshake
    (selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model.CS.model_handshake);

  fold (connection_model_exactly
    c
    (selected_server_parameters_state st0 (Ghost.reveal selection)).CS.cs_model);

  lemma_selected_server_parameters_state_evolves
    st0
    (Ghost.reveal selection);
  MR.update c.ghost_state (selected_server_parameters_state st0 (Ghost.reveal selection));
  fold (connection_exactly c (selected_server_parameters_state st0 (Ghost.reveal selection)))
}

fn mark_sent_server_hello
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lsh:IM.server_hello)
  (#sh:erased M.server_hello)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to raw 'raw_bytes **
           ArrPts.pts_to fragment 'fragment_bytes **
           IM.is_valid_server_hello lsh sh **
           pure (B.length 'fragment_bytes == SZ.v fragment_len /\
                 Seq.equal
                   (Ghost.reveal 'fragment_bytes)
                   (W.serialize_handshake (M.ServerHello sh)) /\
                 SZ.v fragment_len <= max_server_hello_len /\
                 can_send_server_hello st0 sh (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (sent_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)) **
          ArrPts.pts_to raw 'raw_bytes **
          ArrPts.pts_to fragment 'fragment_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived));
  assert (pure (st0.CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    })));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    })
    (Ghost.reveal 'raw_bytes)
    B.empty));

  W.lemma_serialize_server_hello_len sh;
  assert (pure (B.length (W.serialize_handshake (M.ServerHello sh)) == 90));
  assert (pure (SZ.v fragment_len == 90));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly
    c.handshake.server_key_share
    st0.CS.cs_model.CS.model_handshake);
  unfold (optional_fixed_bytes_exactly
    c.handshake.server_key_share
    32
    (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
     | Some sh -> Some sh.M.key_share
     | None -> None));
  with old_server_key_share_present old_server_key_share_storage. _;

  c.control.handshake_stage_tag := 14uy;

  assert (pure (Tags.control_state_matches
    1uy
    14uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsServerHelloSent)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsServerHelloSent)
    st0.CS.cs_model.CS.model_failure);

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (server_hello_slot_exactly
    c.handshake.messages.server_hello
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
  with stored_server_hello. _;
  drop_ (match stored_server_hello, st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_server_hello old_l old_m
    | _, _ -> pure False);
  c.handshake.messages.server_hello := Some lsh;

  unfold (IM.is_valid_server_hello lsh sh);
  with lsh_random lsh_key_share. _;
  V.to_array_pts_to lsh.IM.server_hello_key_share;
  V.to_array_pts_to c.handshake.server_key_share.bytes;
  Arr.memcpy
    32sz
    (V.vec_to_array lsh.IM.server_hello_key_share)
    (V.vec_to_array c.handshake.server_key_share.bytes);
  V.to_vec_pts_to lsh.IM.server_hello_key_share;
  V.to_vec_pts_to c.handshake.server_key_share.bytes;
  c.handshake.server_key_share.present := true;
  with copied_server_key_share. assert (V.pts_to c.handshake.server_key_share.bytes copied_server_key_share);
  assert (pure (Seq.equal copied_server_key_share (Ghost.reveal sh).M.key_share));
  assert (pure (optional_fixed_bytes_match true copied_server_key_share 32 (Some (Ghost.reveal sh).M.key_share)));
  fold (optional_fixed_bytes_exactly
    c.handshake.server_key_share
    32
    (Some (Ghost.reveal sh).M.key_share));
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (sent_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (IM.is_valid_server_hello lsh sh);

  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  unfold (sized_bytes_exactly
    c.handshake.buffers.server_hello_bytes
    max_server_hello_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes);

  with old_server_hello_storage old_server_hello_len. _;
  V.to_array_pts_to c.handshake.buffers.server_hello_bytes.bytes;
  ArrPts.pts_to_len fragment;
  ArrPts.pts_to_len (V.vec_to_array c.handshake.buffers.server_hello_bytes.bytes);
  Arr.memcpy_l fragment_len fragment (V.vec_to_array c.handshake.buffers.server_hello_bytes.bytes);
  V.to_vec_pts_to c.handshake.buffers.server_hello_bytes.bytes;
  with server_hello_storage. assert (V.pts_to c.handshake.buffers.server_hello_bytes.bytes server_hello_storage);
  Seq.lemma_len_slice server_hello_storage 0 (SZ.v fragment_len);
  assert (pure (Seq.equal
    (Seq.slice server_hello_storage 0 (SZ.v fragment_len))
    (Ghost.reveal 'fragment_bytes)));
  assert (pure (Seq.equal
    (Seq.slice server_hello_storage 0 (SZ.v fragment_len))
    (W.serialize_handshake (M.ServerHello sh))));

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v fragment_len <= max_transcript_len));

  copy_server_hello_prefix_to_transcript
    c.handshake.buffers.server_hello_bytes.bytes
    c.handshake.transcript.bytes
    fragment_len
    transcript_len;

  with copied_server_hello_storage copied_transcript_storage.
    assert (V.pts_to c.handshake.buffers.server_hello_bytes.bytes copied_server_hello_storage **
            V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (copied_server_hello_storage == server_hello_storage));

  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v fragment_len)));
  let new_transcript_len = SZ.add transcript_len fragment_len;
  c.handshake.buffers.server_hello_bytes.len := fragment_len;
  c.handshake.transcript.len := new_transcript_len;

  fold (sized_bytes_exactly
    c.handshake.buffers.server_hello_bytes
    max_server_hello_len
    (W.serialize_handshake (M.ServerHello sh)));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.ServerHello sh))));

  fold (server_hello_slot_exactly
    c.handshake.messages.server_hello
    (Some (Ghost.reveal sh)));
  fold (handshake_messages_exactly
    c.handshake.messages
    (sent_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    (sent_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (handshake_exactly
    c.handshake
    (sent_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (sent_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_sent_server_hello_state_evolves
    st0
    sh
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (sent_server_hello_state st0 sh (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (sent_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)))
}

fn mark_sent_encrypted_extensions
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lee:IM.encrypted_extensions)
  (#ee:erased M.encrypted_extensions)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
         ArrPts.pts_to raw 'raw_bytes **
         ArrPts.pts_to fragment 'fragment_bytes **
         IM.is_valid_encrypted_extensions lee ee **
         pure (B.length 'fragment_bytes == SZ.v fragment_len /\
               Seq.equal
                 (Ghost.reveal 'fragment_bytes)
                 (W.serialize_handshake (M.EncryptedExtensions ee)) /\
               can_send_encrypted_extensions st0 ee (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
          c
          (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)) **
        ArrPts.pts_to raw 'raw_bytes **
        ArrPts.pts_to fragment 'fragment_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerHelloSent));
  assert (pure (st0.CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure ((Ghost.reveal ee).M.negotiated_alpn == None));
  assert (pure (Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
  assert (pure (U64.fits
    (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
    })));
  assert (pure (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
    })
    (Ghost.reveal 'raw_bytes)
    B.empty));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;

  c.control.handshake_stage_tag := 15uy;
  assert (pure (Tags.control_state_matches
    1uy
    15uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsServerEncryptedFlightSent)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsServerEncryptedFlightSent)
    st0.CS.cs_model.CS.model_failure);

  Rec.advance_seq c.records.write;
  rewrite (Rec.is_record_state
    c.records.read
    st0.CS.cs_model.CS.model_record.CS.record_read)
    as (Rec.is_record_state
    c.records.read
    (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record.CS.record_read);
  rewrite (Rec.is_record_state
    c.records.write
    (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write))
    as (Rec.is_record_state
    c.records.write
    (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record.CS.record_write);
  fold (record_layer_exactly
    c.records
    (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_record);

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (encrypted_extensions_slot_exactly
    c.handshake.messages.encrypted_extensions
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions);
  with stored_encrypted_extensions. _;
  drop_ (match stored_encrypted_extensions, st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_encrypted_extensions old_l old_m
    | _, _ -> pure False);
  c.handshake.messages.encrypted_extensions := Some lee;
  fold (encrypted_extensions_slot_exactly
    c.handshake.messages.encrypted_extensions
    (Some (Ghost.reveal ee)));

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v fragment_len <= max_transcript_len));

  copy_array_prefix_to_transcript
    fragment
    c.handshake.transcript.bytes
    fragment_len
    transcript_len;
  with transcript_storage. assert (V.pts_to c.handshake.transcript.bytes transcript_storage);
  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v fragment_len)));
  let new_transcript_len = SZ.add transcript_len fragment_len;
  c.handshake.transcript.len := new_transcript_len;

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (W.serialize_handshake (M.EncryptedExtensions ee))));

  fold (handshake_messages_exactly
    c.handshake.messages
    (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);

  assert (pure ((sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));
  assert (pure (cv_verified ==
    (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure (server_finished_verified ==
    (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (server_key_share_exactly
    c.handshake.server_key_share
    st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake.CS.hs_keys);

  fold (handshake_exactly
    c.handshake
    (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)).CS.cs_model);

  lemma_sent_encrypted_extensions_state_evolves
    st0
    ee
    (Ghost.reveal 'raw_bytes);
  MR.update
    c.ghost_state
    (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes));
  fold (connection_exactly
    c
    (sent_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)))
}

fn try_send_client_hello
  (c:connection_state)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'old_network_out == SZ.v network_out_len)
  returns written: option (n:SZ.t{SZ.v n <= SZ.v network_out_len})
  ensures (match written with
           | Some n ->
             exists* ch raw_sent network_out_bytes.
               connection_exactly c (sent_client_hello_state st0 ch raw_sent) **
               ArrPts.pts_to network_out network_out_bytes **
               pure (B.length network_out_bytes == SZ.v network_out_len /\
                     5 <= SZ.v n /\
                     SZ.v n <= B.length network_out_bytes /\
                     can_send_client_hello st0 ch raw_sent /\
                     W.parse_record (Seq.slice network_out_bytes 0 (SZ.v n)) ==
                       Some
                         (T.Handshake,
                          W.serialize_handshake (M.ClientHello ch),
                          SZ.v n) /\
                     Seq.equal raw_sent (Seq.slice network_out_bytes 0 (SZ.v n)))
           | None ->
             connection_exactly c st0 **
             ArrPts.pts_to network_out 'old_network_out)
{
  let ready = can_send_client_hello_runtime c network_out_len;
  if ready {
    assert (pure (st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsStarted));
    assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_start));
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None));
    assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      <= max_transcript_len - max_client_hello_len));
    assert (pure (517 <= SZ.v network_out_len));

    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    with old_control_tag old_stage_tag old_failure_present
         old_failure_code old_failure_alert. _;
    assert (pure (st0.CS.cs_model.CS.model_failure == None));
    unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    with cv_verified server_finished_verified. _;

    unfold (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    with start_present. _;
    let has_start = !c.handshake.start.present;
    assert (pure (has_start == start_present));
    if has_start {
    assert (pure (start_present == true));
    rewrite (handshake_start_payload_exactly
      c.handshake.start
      start_present
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_payload_exactly
        c.handshake.start
        true
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    unfold (handshake_start_payload_exactly
      c.handshake.start
      true
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    with start_spec. _;
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_start ==
      Some start_spec));
    unfold (handshake_start_fields_exactly c.handshake.start start_spec);
    unfold (sized_bytes_exactly
      c.handshake.start.server_name
      max_hostname_len
      start_spec.CS.start_server_name);
    with old_start_server_name old_start_server_name_len. _;
    unfold (fixed_bytes_exactly
      c.handshake.start.client_random
      32
      start_spec.CS.start_client_random);
    with old_start_random. _;
    unfold (fixed_bytes_exactly
      c.handshake.start.client_key_share_public
      32
      start_spec.CS.start_client_key_share_public);
    with old_start_key_share. _;
    unfold (cipher_suite_list_exactly
      c.handshake.start.cipher_suites
      max_cipher_suites
      start_spec.CS.start_cipher_suites);
    with old_start_cipher_suites old_start_cipher_suites_len. _;
    unfold (signature_scheme_list_exactly
      c.handshake.start.signature_schemes
      max_signature_schemes
      start_spec.CS.start_signature_schemes);
    with old_start_signature_schemes old_start_signature_schemes_len. _;

    unfold (handshake_messages_exactly
      c.handshake.messages
      st0.CS.cs_model.CS.model_handshake);
    unfold (client_hello_slot_exactly
      c.handshake.messages.client_hello_present
      c.handshake.messages.client_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    with old_client_hello_present old_l_random old_l_server_name
         old_l_key_share old_l_cipher_suites old_l_signature_schemes. _;
    assert (pure (old_client_hello_present == false));

    unfold (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
    with parsed. _;
    unfold (sized_bytes_exactly
      c.handshake.buffers.client_hello_bytes
      max_client_hello_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_client_hello_bytes);
    with old_client_hello_bytes old_client_hello_bytes_len. _;

    let start = Ghost.hide start_spec;
    assert (pure (Ghost.reveal start == start_spec));
    let ch = Ghost.hide (client_hello_of_start (Ghost.reveal start));
    assert (pure (Ghost.reveal ch == client_hello_of_start start_spec));
    lemma_client_hello_of_start_matches (Ghost.reveal start);
    assert (pure (CS.client_hello_matches_start start_spec (Ghost.reveal ch)));

    let written =
      Ser.serialize_client_hello_from_start
        #start
        #ch
        c.handshake.start.client_random
        c.handshake.start.server_name.bytes
        c.handshake.start.server_name.len
        c.handshake.start.client_key_share_public
        c.handshake.start.cipher_suites.items
        c.handshake.start.cipher_suites.len
        c.handshake.start.signature_schemes.items
        c.handshake.start.signature_schemes.len
        c.handshake.messages.client_hello_present
        c.handshake.messages.client_hello
        c.handshake.buffers.client_hello_bytes.bytes
        c.handshake.buffers.client_hello_bytes.len
        network_out
        network_out_len;
    with random server_name server_name_len key_share
         cipher_suites cipher_suites_len
         signature_schemes signature_schemes_len
         handshake_bytes network_out_bytes handshake_len. _;

    assert (pure (B.length network_out_bytes == SZ.v network_out_len));
    assert (pure (SZ.v written <= B.length network_out_bytes));
    assert (pure (5 <= SZ.v written));
    assert (pure (Seq.equal
      (CL.raw_slice network_out_bytes 0 (SZ.v written))
      (CS.serialized_cleartext_tls_message
        (M.TlsHandshake (M.ClientHello (Ghost.reveal ch))))));
    assert (pure (CL.raw_slice network_out_bytes 0 (SZ.v written) ==
      Seq.slice network_out_bytes 0 (SZ.v written)));
    let raw_sent = Ghost.hide (Seq.slice network_out_bytes 0 (SZ.v written));
    assert (pure (Seq.equal
      (Ghost.reveal raw_sent)
      (Seq.slice network_out_bytes 0 (SZ.v written))));
    assert (pure (Seq.equal
      (Ghost.reveal raw_sent)
      (CS.serialized_cleartext_tls_message
        (M.TlsHandshake (M.ClientHello (Ghost.reveal ch))))));
    Seq.lemma_eq_intro B.empty B.empty;
    assert (pure (CS.event_raw_delta_legal
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello (Ghost.reveal ch));
      })
      (Ghost.reveal raw_sent)
      B.empty));

    assert (pure (SZ.v handshake_len ==
      B.length (W.serialize_handshake (M.ClientHello (Ghost.reveal ch)))));
    assert (pure (SZ.v handshake_len <= max_client_hello_len));
    assert (pure (SZ.v (server_name_len) <= B.length server_name));
    lemma_client_hello_len_helpers_from_start
      start_spec
      (Ghost.reveal ch)
      server_name
      server_name_len
      cipher_suites
      cipher_suites_len
      signature_schemes
      signature_schemes_len;

    assert (pure (CL.raw_slice server_name 0 (SZ.v server_name_len) ==
      Seq.slice server_name 0 (SZ.v server_name_len)));
    assert (pure (byte_prefix_matches
      server_name
      server_name_len
      start_spec.CS.start_server_name));
    fold (sized_bytes_exactly
      c.handshake.start.server_name
      max_hostname_len
      start_spec.CS.start_server_name);
    fold (fixed_bytes_exactly
      c.handshake.start.client_random
      32
      start_spec.CS.start_client_random);
    fold (fixed_bytes_exactly
      c.handshake.start.client_key_share_public
      32
      start_spec.CS.start_client_key_share_public);
    fold (cipher_suite_list_exactly
      c.handshake.start.cipher_suites
      max_cipher_suites
      start_spec.CS.start_cipher_suites);
    fold (signature_scheme_list_exactly
      c.handshake.start.signature_schemes
      max_signature_schemes
      start_spec.CS.start_signature_schemes);
    fold (handshake_start_fields_exactly c.handshake.start start_spec);
    fold (handshake_start_payload_exactly
      c.handshake.start
      true
      (Some start_spec));
    fold (handshake_start_exactly
      c.handshake.start
      (Some start_spec));

    assert (pure (CS.client_hello_matches_start start_spec (Ghost.reveal ch)));
    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello (Ghost.reveal ch));
      })));
    assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
      B.length (W.serialize_handshake (M.ClientHello (Ghost.reveal ch))) <=
      max_transcript_len));
    assert (pure (can_send_client_hello
      st0
      (Ghost.reveal ch)
      (Ghost.reveal raw_sent)));

    unfold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    with old_transcript_storage old_transcript_len. _;
    let transcript_len = !c.handshake.transcript.len;
    let handshake_len_runtime = !c.handshake.buffers.client_hello_bytes.len;
    assert (pure (transcript_len == old_transcript_len));
    assert (pure (handshake_len_runtime == handshake_len));
    assert (pure (SZ.v transcript_len ==
      B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    assert (pure (SZ.v transcript_len + SZ.v handshake_len_runtime <= max_transcript_len));
    copy_client_hello_prefix_to_transcript
      c.handshake.buffers.client_hello_bytes.bytes
      c.handshake.transcript.bytes
      handshake_len_runtime
      transcript_len;
    with copied_client_hello_bytes copied_transcript_storage.
      assert (V.pts_to c.handshake.buffers.client_hello_bytes.bytes copied_client_hello_bytes **
              V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
    assert (pure (copied_client_hello_bytes == handshake_bytes));
    assert (pure (SZ.fits (SZ.v transcript_len + SZ.v handshake_len_runtime)));
    let new_transcript_len = SZ.add transcript_len handshake_len_runtime;
    c.handshake.transcript.len := new_transcript_len;

    assert (pure (CL.raw_slice handshake_bytes 0 (SZ.v handshake_len) ==
      Seq.slice handshake_bytes 0 (SZ.v handshake_len)));
    assert (pure (byte_prefix_matches
      handshake_bytes
      handshake_len
      (W.serialize_handshake (M.ClientHello (Ghost.reveal ch)))));
    fold (sized_bytes_exactly
      c.handshake.buffers.client_hello_bytes
      max_client_hello_len
      (W.serialize_handshake (M.ClientHello (Ghost.reveal ch))));
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (B.append
        st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
        (W.serialize_handshake (M.ClientHello (Ghost.reveal ch)))));

    fold (client_hello_slot_exactly
      c.handshake.messages.client_hello_present
      c.handshake.messages.client_hello
      (Some (Ghost.reveal ch)));
    fold (handshake_messages_exactly
      c.handshake.messages
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);

    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_start ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_start));
    rewrite (handshake_start_exactly
      c.handshake.start
      (Some start_spec))
      as (handshake_start_exactly
        c.handshake.start
        (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_start);
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
    unfold (server_key_share_exactly
      c.handshake.server_key_share
      st0.CS.cs_model.CS.model_handshake);
    fold (server_key_share_exactly
      c.handshake.server_key_share
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
    rewrite (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
      as (peer_exactly
        c.handshake.validated_peer
        (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_client_hello_bytes ==
      W.serialize_handshake (M.ClientHello (Ghost.reveal ch))));
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_server_hello_bytes));
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes));
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed));
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der));
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input));
    fold (handshake_buffers_exactly
      c.handshake.buffers
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys));
    rewrite (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
      as (key_schedule_exactly
        c.handshake.keys
        (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_keys);
    assert (pure (cv_verified ==
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
    assert (pure (server_finished_verified ==
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
    fold (handshake_exactly
      c.handshake
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);

    c.control.control_tag := 1uy;
    c.control.handshake_stage_tag := 2uy;
    c.control.failure_present := false;
    c.control.failure_code := 0uy;
    c.control.failure_alert := 0uy;
    assert (pure (Tags.control_state_matches
      1uy
      2uy
      false
      0uy
      0uy
      (CS.ControlHandshaking CS.HsClientHelloSent)));
    fold (control_exactly
      c.control
      (CS.ControlHandshaking CS.HsClientHelloSent)
      st0.CS.cs_model.CS.model_failure);

    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config ==
      st0.CS.cs_model.CS.model_config));
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record ==
      st0.CS.cs_model.CS.model_record));
    assert (pure ((sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application ==
      st0.CS.cs_model.CS.model_application));
    rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
      as (connection_config_exactly
        c.config
        (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config);
    rewrite (record_layer_exactly c.records st0.CS.cs_model.CS.model_record)
      as (record_layer_exactly
        c.records
        (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record);
    rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
      as (application_exactly
        c.application
        (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application);
    fold (connection_model_exactly
      c
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)).CS.cs_model);

    lemma_sent_client_hello_state_evolves
      st0
      (Ghost.reveal ch)
      (Ghost.reveal raw_sent);
    MR.update
      c.ghost_state
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent));
    fold (connection_exactly
      c
      (sent_client_hello_state st0 (Ghost.reveal ch) (Ghost.reveal raw_sent)));
    Some written
    } else {
      fold (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      fold (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      None
    }
  } else {
    None
  }
}

fn derive_shared_secret_from_bytes
  (c:connection_state)
  (shared_src:array U8.t)
  (#shared:erased TLS13.Crypto.Spec.x25519_shared_secret)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to shared_src shared **
           pure (B.length (Ghost.reveal shared) == 32 /\
                 CS.legal_event
                   st0.CS.cs_model
                   (CS.ConnLocalEvent
                     (CS.LocalDeriveSharedSecret (Ghost.reveal shared))))
  ensures connection_exactly
            c
            (derived_shared_secret_state st0 (Ghost.reveal shared)) **
          ArrPts.pts_to shared_src shared **
          pure (CS.legal_connection_delta
            st0
            {
              CS.delta_event =
                CS.ConnLocalEvent
                  (CS.LocalDeriveSharedSecret (Ghost.reveal shared));
              CS.delta_raw_sent = B.empty;
              CS.delta_raw_received = B.empty;
            }
            (derived_shared_secret_state st0 (Ghost.reveal shared)))
{
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalDeriveSharedSecret (Ghost.reveal shared)))));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);

  let mut early_out = [| 0uy; 32sz |];
  KS.early_secret_empty early_out;
  let mut handshake_out = [| 0uy; 32sz |];
  KS.handshake_secret early_out shared_src 32sz handshake_out;
  let mut master_out = [| 0uy; 32sz |];
  KS.master_secret handshake_out master_out;

  store_optional_secret c.handshake.keys.shared_secret shared_src #shared;
  store_optional_secret
    c.handshake.keys.early_secret
    early_out
    #(K.early_secret B.empty);
  store_optional_secret
    c.handshake.keys.handshake_secret
    handshake_out
    #(K.handshake_secret (K.early_secret B.empty) (Ghost.reveal shared));
  store_optional_secret
    c.handshake.keys.master_secret
    master_out
    #(K.master_secret (K.handshake_secret (K.early_secret B.empty) (Ghost.reveal shared)));

  fold (key_schedule_exactly
    c.handshake.keys
    (derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake.CS.hs_keys);

  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));

  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  fold (handshake_messages_exactly
    c.handshake.messages
    (derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly
    c.handshake.server_key_share
    st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake);

  fold (handshake_exactly
    c.handshake
    (derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_handshake);

  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_control ==
    st0.CS.cs_model.CS.model_control));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_failure ==
    st0.CS.cs_model.CS.model_failure));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_record ==
    st0.CS.cs_model.CS.model_record));
  assert (pure ((derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  fold (connection_model_exactly
    c
    (derived_shared_secret_state st0 (Ghost.reveal shared)).CS.cs_model);

  lemma_derived_shared_secret_state_evolves st0 (Ghost.reveal shared);
  MR.update c.ghost_state (derived_shared_secret_state st0 (Ghost.reveal shared));
  fold (connection_exactly c (derived_shared_secret_state st0 (Ghost.reveal shared)))
}

fn install_server_handshake_write_traffic_keys_from_material
  (c:connection_state)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to traffic_secret_src material.CS.traffic_secret **
           ArrPts.pts_to traffic_key_src material.CS.traffic_key **
           ArrPts.pts_to traffic_iv_src material.CS.traffic_iv **
           pure (CS.legal_event
             st0.CS.cs_model
             (CS.ConnLocalEvent
               (CS.LocalInstallTrafficKeysForRole {
                 CS.install_role = CS.ServerEndpoint;
                 CS.install_payload = {
                   CS.install_epoch = CS.TrafficHandshake;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = Ghost.reveal material;
                 };
               })))
  ensures connection_exactly
            c
            (installed_traffic_keys_for_role_state st0 {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = Ghost.reveal material;
              };
            }) **
          ArrPts.pts_to traffic_secret_src material.CS.traffic_secret **
          ArrPts.pts_to traffic_key_src material.CS.traffic_key **
          ArrPts.pts_to traffic_iv_src material.CS.traffic_iv **
          pure (CS.legal_connection_delta
            st0
            {
              CS.delta_event =
                CS.ConnLocalEvent
                  (CS.LocalInstallTrafficKeysForRole {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficHandshake;
                      CS.install_direction = CS.TrafficWrite;
                      CS.install_material = Ghost.reveal material;
                    };
                  });
              CS.delta_raw_sent = B.empty;
              CS.delta_raw_received = B.empty;
            }
            (installed_traffic_keys_for_role_state st0 {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = Ghost.reveal material;
              };
            }))
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
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);

  store_traffic_key_material
    c.handshake.keys.server_handshake_traffic
    traffic_secret_src
    traffic_key_src
    traffic_iv_src
    #material;
  fold (key_schedule_exactly
    c.handshake.keys
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_keys);

  Rec.install_handshake_keys_runtime c.records.write traffic_key_src traffic_iv_src;
  assert (pure ((Ghost.reveal install).CS.install_epoch == CS.TrafficHandshake));
  assert (pure ((Ghost.reveal install).CS.install_direction == CS.TrafficWrite));
  assert (pure ((Ghost.reveal install).CS.install_material == Ghost.reveal material));
  assert (pure ((Ghost.reveal role_install).CS.install_role == CS.ServerEndpoint));
  assert (pure ((Ghost.reveal role_install).CS.install_payload == Ghost.reveal install));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_read ==
    st0.CS.cs_model.CS.model_record.CS.record_read));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_write ==
    R.install_keys
      st0.CS.cs_model.CS.model_record.CS.record_write
      R.Handshake
      (Ghost.reveal material).CS.traffic_key
      (Ghost.reveal material).CS.traffic_iv));
  rewrite (Rec.is_record_state c.records.read st0.CS.cs_model.CS.model_record.CS.record_read)
    as (Rec.is_record_state
      c.records.read
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_read);
  rewrite (Rec.is_record_state
    c.records.write
    (R.install_keys
      st0.CS.cs_model.CS.model_record.CS.record_write
      R.Handshake
      (Ghost.reveal material).CS.traffic_key
      (Ghost.reveal material).CS.traffic_iv))
    as (Rec.is_record_state
      c.records.write
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_write);
  fold (record_layer_exactly
    c.records
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record);

  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_messages_exactly
    c.handshake.messages
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake);
  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_start);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
    as (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (handshake_exactly
    c.handshake
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake);

  fold (control_exactly
    c.control
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_control
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_failure);
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model);

  lemma_installed_traffic_keys_for_role_state_evolves st0 (Ghost.reveal role_install);
  MR.update c.ghost_state (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install));
  fold (connection_exactly c (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)));
  rewrite (connection_exactly c (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)))
    as (connection_exactly c (installed_traffic_keys_for_role_state st0 {
      CS.install_role = CS.ServerEndpoint;
      CS.install_payload = {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = Ghost.reveal material;
      };
    }))
}

fn install_client_handshake_read_traffic_keys_from_material
  (c:connection_state)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to traffic_secret_src material.CS.traffic_secret **
           ArrPts.pts_to traffic_key_src material.CS.traffic_key **
           ArrPts.pts_to traffic_iv_src material.CS.traffic_iv **
           pure (CS.legal_event
             st0.CS.cs_model
             (CS.ConnLocalEvent
               (CS.LocalInstallTrafficKeysForRole {
                 CS.install_role = CS.ServerEndpoint;
                 CS.install_payload = {
                   CS.install_epoch = CS.TrafficHandshake;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = Ghost.reveal material;
                 };
               })))
  ensures connection_exactly
            c
            (installed_traffic_keys_for_role_state st0 {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = Ghost.reveal material;
              };
            }) **
          ArrPts.pts_to traffic_secret_src material.CS.traffic_secret **
          ArrPts.pts_to traffic_key_src material.CS.traffic_key **
          ArrPts.pts_to traffic_iv_src material.CS.traffic_iv **
          pure (CS.legal_connection_delta
            st0
            {
              CS.delta_event =
                CS.ConnLocalEvent
                  (CS.LocalInstallTrafficKeysForRole {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficHandshake;
                      CS.install_direction = CS.TrafficRead;
                      CS.install_material = Ghost.reveal material;
                    };
                  });
              CS.delta_raw_sent = B.empty;
              CS.delta_raw_received = B.empty;
            }
            (installed_traffic_keys_for_role_state st0 {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = Ghost.reveal material;
              };
            }))
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
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);

  store_traffic_key_material
    c.handshake.keys.client_handshake_traffic
    traffic_secret_src
    traffic_key_src
    traffic_iv_src
    #material;
  fold (key_schedule_exactly
    c.handshake.keys
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_keys);

  Rec.install_handshake_keys_runtime c.records.read traffic_key_src traffic_iv_src;
  assert (pure ((Ghost.reveal install).CS.install_epoch == CS.TrafficHandshake));
  assert (pure ((Ghost.reveal install).CS.install_direction == CS.TrafficRead));
  assert (pure ((Ghost.reveal install).CS.install_material == Ghost.reveal material));
  assert (pure ((Ghost.reveal role_install).CS.install_role == CS.ServerEndpoint));
  assert (pure ((Ghost.reveal role_install).CS.install_payload == Ghost.reveal install));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_write ==
    st0.CS.cs_model.CS.model_record.CS.record_write));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_read ==
    R.install_keys
      st0.CS.cs_model.CS.model_record.CS.record_read
      R.Handshake
      (Ghost.reveal material).CS.traffic_key
      (Ghost.reveal material).CS.traffic_iv));
  rewrite (Rec.is_record_state c.records.write st0.CS.cs_model.CS.model_record.CS.record_write)
    as (Rec.is_record_state
      c.records.write
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_write);
  rewrite (Rec.is_record_state
    c.records.read
    (R.install_keys
      st0.CS.cs_model.CS.model_record.CS.record_read
      R.Handshake
      (Ghost.reveal material).CS.traffic_key
      (Ghost.reveal material).CS.traffic_iv))
    as (Rec.is_record_state
      c.records.read
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_read);
  fold (record_layer_exactly
    c.records
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record);

  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_messages_exactly
    c.handshake.messages
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake);
  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_start);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
    as (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (handshake_exactly
    c.handshake
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake);

  fold (control_exactly
    c.control
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_control
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_failure);
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model);

  lemma_installed_traffic_keys_for_role_state_evolves st0 (Ghost.reveal role_install);
  MR.update c.ghost_state (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install));
  fold (connection_exactly c (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)));
  rewrite (connection_exactly c (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)))
    as (connection_exactly c (installed_traffic_keys_for_role_state st0 {
      CS.install_role = CS.ServerEndpoint;
      CS.install_payload = {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = Ghost.reveal material;
      };
    }))
}

fn install_server_application_write_traffic_keys_from_material
  (c:connection_state)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to traffic_secret_src material.CS.traffic_secret **
           ArrPts.pts_to traffic_key_src material.CS.traffic_key **
           ArrPts.pts_to traffic_iv_src material.CS.traffic_iv **
           pure (CS.legal_event
             st0.CS.cs_model
             (CS.ConnLocalEvent
               (CS.LocalInstallTrafficKeysForRole {
                 CS.install_role = CS.ServerEndpoint;
                 CS.install_payload = {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = Ghost.reveal material;
                 };
               })))
  ensures connection_exactly
           c
           (installed_traffic_keys_for_role_state st0 {
             CS.install_role = CS.ServerEndpoint;
             CS.install_payload = {
               CS.install_epoch = CS.TrafficApplication;
               CS.install_direction = CS.TrafficWrite;
               CS.install_material = Ghost.reveal material;
             };
           }) **
          ArrPts.pts_to traffic_secret_src material.CS.traffic_secret **
          ArrPts.pts_to traffic_key_src material.CS.traffic_key **
          ArrPts.pts_to traffic_iv_src material.CS.traffic_iv **
          pure (CS.legal_connection_delta
            st0
            {
              CS.delta_event =
                CS.ConnLocalEvent
                  (CS.LocalInstallTrafficKeysForRole {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficApplication;
                      CS.install_direction = CS.TrafficWrite;
                      CS.install_material = Ghost.reveal material;
                    };
                  });
              CS.delta_raw_sent = B.empty;
              CS.delta_raw_received = B.empty;
            }
            (installed_traffic_keys_for_role_state st0 {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = Ghost.reveal material;
              };
            }))
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
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);

  store_traffic_key_material
    c.handshake.keys.server_application_traffic
    traffic_secret_src
    traffic_key_src
    traffic_iv_src
    #material;
  fold (key_schedule_exactly
    c.handshake.keys
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_keys);

  Rec.install_application_keys_runtime c.records.write traffic_key_src traffic_iv_src;
  assert (pure ((Ghost.reveal install).CS.install_epoch == CS.TrafficApplication));
  assert (pure ((Ghost.reveal install).CS.install_direction == CS.TrafficWrite));
  assert (pure ((Ghost.reveal install).CS.install_material == Ghost.reveal material));
  assert (pure ((Ghost.reveal role_install).CS.install_role == CS.ServerEndpoint));
  assert (pure ((Ghost.reveal role_install).CS.install_payload == Ghost.reveal install));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_read ==
    st0.CS.cs_model.CS.model_record.CS.record_read));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_write ==
    R.install_keys
      st0.CS.cs_model.CS.model_record.CS.record_write
      R.Application
      (Ghost.reveal material).CS.traffic_key
      (Ghost.reveal material).CS.traffic_iv));
  rewrite (Rec.is_record_state c.records.read st0.CS.cs_model.CS.model_record.CS.record_read)
    as (Rec.is_record_state
      c.records.read
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_read);
  rewrite (Rec.is_record_state
    c.records.write
    (R.install_keys
      st0.CS.cs_model.CS.model_record.CS.record_write
      R.Application
      (Ghost.reveal material).CS.traffic_key
      (Ghost.reveal material).CS.traffic_iv))
    as (Rec.is_record_state
      c.records.write
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_write);
  fold (record_layer_exactly
    c.records
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record);

  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_messages_exactly
    c.handshake.messages
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake);
  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_start);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
    as (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (handshake_exactly
    c.handshake
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake);

  fold (control_exactly
    c.control
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_control
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_failure);
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model);

  lemma_installed_traffic_keys_for_role_state_evolves st0 (Ghost.reveal role_install);
  MR.update c.ghost_state (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install));
  fold (connection_exactly c (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)));
  rewrite (connection_exactly c (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)))
    as (connection_exactly c (installed_traffic_keys_for_role_state st0 {
      CS.install_role = CS.ServerEndpoint;
      CS.install_payload = {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = Ghost.reveal material;
      };
    }))
}

fn install_client_application_read_traffic_keys_from_material
  (c:connection_state)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to traffic_secret_src material.CS.traffic_secret **
           ArrPts.pts_to traffic_key_src material.CS.traffic_key **
           ArrPts.pts_to traffic_iv_src material.CS.traffic_iv **
           pure (CS.legal_event
             st0.CS.cs_model
             (CS.ConnLocalEvent
               (CS.LocalInstallTrafficKeysForRole {
                 CS.install_role = CS.ServerEndpoint;
                 CS.install_payload = {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = Ghost.reveal material;
                 };
               })))
  ensures connection_exactly
           c
           (installed_traffic_keys_for_role_state st0 {
             CS.install_role = CS.ServerEndpoint;
             CS.install_payload = {
               CS.install_epoch = CS.TrafficApplication;
               CS.install_direction = CS.TrafficRead;
               CS.install_material = Ghost.reveal material;
             };
           }) **
          ArrPts.pts_to traffic_secret_src material.CS.traffic_secret **
          ArrPts.pts_to traffic_key_src material.CS.traffic_key **
          ArrPts.pts_to traffic_iv_src material.CS.traffic_iv **
          pure (CS.legal_connection_delta
            st0
            {
              CS.delta_event =
                CS.ConnLocalEvent
                  (CS.LocalInstallTrafficKeysForRole {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficApplication;
                      CS.install_direction = CS.TrafficRead;
                      CS.install_material = Ghost.reveal material;
                    };
                  });
              CS.delta_raw_sent = B.empty;
              CS.delta_raw_received = B.empty;
            }
            (installed_traffic_keys_for_role_state st0 {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = Ghost.reveal material;
              };
            }))
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
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole (Ghost.reveal role_install)))));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);

  store_traffic_key_material
    c.handshake.keys.client_application_traffic
    traffic_secret_src
    traffic_key_src
    traffic_iv_src
    #material;
  fold (key_schedule_exactly
    c.handshake.keys
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_keys);

  Rec.install_application_keys_runtime c.records.read traffic_key_src traffic_iv_src;
  assert (pure ((Ghost.reveal install).CS.install_epoch == CS.TrafficApplication));
  assert (pure ((Ghost.reveal install).CS.install_direction == CS.TrafficRead));
  assert (pure ((Ghost.reveal install).CS.install_material == Ghost.reveal material));
  assert (pure ((Ghost.reveal role_install).CS.install_role == CS.ServerEndpoint));
  assert (pure ((Ghost.reveal role_install).CS.install_payload == Ghost.reveal install));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_write ==
    st0.CS.cs_model.CS.model_record.CS.record_write));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_read ==
    R.install_keys
      st0.CS.cs_model.CS.model_record.CS.record_read
      R.Application
      (Ghost.reveal material).CS.traffic_key
      (Ghost.reveal material).CS.traffic_iv));
  rewrite (Rec.is_record_state c.records.write st0.CS.cs_model.CS.model_record.CS.record_write)
    as (Rec.is_record_state
      c.records.write
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_write);
  rewrite (Rec.is_record_state
    c.records.read
    (R.install_keys
      st0.CS.cs_model.CS.model_record.CS.record_read
      R.Application
      (Ghost.reveal material).CS.traffic_key
      (Ghost.reveal material).CS.traffic_iv))
    as (Rec.is_record_state
      c.records.read
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record.CS.record_read);
  fold (record_layer_exactly
    c.records
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_record);

  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));

  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_messages_exactly
    c.handshake.messages
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake);
  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_start);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
    as (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (handshake_exactly
    c.handshake
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_handshake);

  fold (control_exactly
    c.control
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_control
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_failure);
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_config);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)).CS.cs_model);

  lemma_installed_traffic_keys_for_role_state_evolves st0 (Ghost.reveal role_install);
  MR.update c.ghost_state (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install));
  fold (connection_exactly c (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)));
  rewrite (connection_exactly c (installed_traffic_keys_for_role_state st0 (Ghost.reveal role_install)))
    as (connection_exactly c (installed_traffic_keys_for_role_state st0 {
      CS.install_role = CS.ServerEndpoint;
      CS.install_payload = {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = Ghost.reveal material;
      };
    }))
}

fn derive_and_install_server_application_write_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerFinishedSent /\
                 st0.CS.cs_model.CS.model_config.CS.config_role ==
                    CS.ServerEndpoint /\
                 Some?
                   st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret)
  ensures exists* material.
            connection_exactly c
              (installed_traffic_keys_for_role_state st0 {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = material;
                };
              }) **
            pure (CS.legal_connection_delta
              st0
              {
                CS.delta_event =
                  CS.ConnLocalEvent
                    (CS.LocalInstallTrafficKeysForRole {
                      CS.install_role = CS.ServerEndpoint;
                      CS.install_payload = {
                        CS.install_epoch = CS.TrafficApplication;
                        CS.install_direction = CS.TrafficWrite;
                        CS.install_material = material;
                      };
                    });
                CS.delta_raw_sent = B.empty;
                CS.delta_raw_received = B.empty;
              }
              (installed_traffic_keys_for_role_state st0 {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = material;
                };
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);

  with transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes transcript_storage);
  with transcript_len.
    assert (Box.pts_to c.handshake.transcript.len transcript_len);
  let transcript_len_runtime = !c.handshake.transcript.len;
  assert (pure (transcript_len_runtime == transcript_len));
  with ms_present.
    assert (Box.pts_to c.handshake.keys.master_secret.present ms_present);
  with ms_secret_storage.
    assert (V.pts_to c.handshake.keys.master_secret.secret ms_secret_storage);
  lemma_optional_fixed_bytes_match_present_of_some
    ms_present
    ms_secret_storage
    32
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret;
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
    Some ms_secret_storage));
  let ms_secret = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  assert (pure (Ghost.reveal ms_secret == ms_secret_storage));

  assert (pure (byte_prefix_matches
    transcript_storage
    transcript_len_runtime
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (Seq.equal
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
  Seq.lemma_eq_intro
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

  V.to_array_pts_to c.handshake.transcript.bytes;
  let mut transcript_hash = [| 0uy; 32sz |];
  Crypto.sha256_prefix
    (V.vec_to_array c.handshake.transcript.bytes)
    transcript_len_runtime
    transcript_hash;
  V.to_vec_pts_to c.handshake.transcript.bytes;
  with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
  assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  V.to_array_pts_to c.handshake.keys.master_secret.secret;
  let mut traffic_secret_out = [| 0uy; 32sz |];
  KS.server_application_traffic_secret
    (V.vec_to_array c.handshake.keys.master_secret.secret)
    transcript_hash
    traffic_secret_out;
  V.to_vec_pts_to c.handshake.keys.master_secret.secret;
  with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
  assert (pure (traffic_secret_bytes ==
    K.server_application_traffic_secret
      (Ghost.reveal ms_secret)
      (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

  let mut traffic_key_out = [| 0uy; 32sz |];
  KS.derive_traffic_key traffic_secret_out traffic_key_out;
  let mut traffic_iv_out = [| 0uy; 12sz |];
  KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
  with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
  with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

  let traffic_secret = Ghost.hide traffic_secret_bytes;
  let material = Ghost.hide (CS.traffic_key_material_for_secret (Ghost.reveal traffic_secret));
  assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
  assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
  assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));

  fold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);

  lemma_server_role_server_application_write_traffic_install_legal
    st0.CS.cs_model
    (Ghost.reveal ms_secret);
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = Ghost.reveal material;
        };
      }))));

  install_server_application_write_traffic_keys_from_material
    c
    traffic_secret_out
    traffic_key_out
    traffic_iv_out
    #material;
}

fn derive_and_install_client_application_read_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsClientFinishedReceived /\
                 st0.CS.cs_model.CS.model_config.CS.config_role ==
                    CS.ServerEndpoint /\
                 Some?
                   st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret)
  ensures exists* material.
            connection_exactly c
              (installed_traffic_keys_for_role_state st0 {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = material;
                };
              }) **
            pure (CS.legal_connection_delta
              st0
              {
                CS.delta_event =
                  CS.ConnLocalEvent
                    (CS.LocalInstallTrafficKeysForRole {
                      CS.install_role = CS.ServerEndpoint;
                      CS.install_payload = {
                        CS.install_epoch = CS.TrafficApplication;
                        CS.install_direction = CS.TrafficRead;
                        CS.install_material = material;
                      };
                    });
                CS.delta_raw_sent = B.empty;
                CS.delta_raw_received = B.empty;
              }
              (installed_traffic_keys_for_role_state st0 {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = material;
                };
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);

  with transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes transcript_storage);
  with transcript_len.
    assert (Box.pts_to c.handshake.transcript.len transcript_len);
  let transcript_len_runtime = !c.handshake.transcript.len;
  assert (pure (transcript_len_runtime == transcript_len));
  with ms_present.
    assert (Box.pts_to c.handshake.keys.master_secret.present ms_present);
  with ms_secret_storage.
    assert (V.pts_to c.handshake.keys.master_secret.secret ms_secret_storage);
  lemma_optional_fixed_bytes_match_present_of_some
    ms_present
    ms_secret_storage
    32
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret;
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
    Some ms_secret_storage));
  let ms_secret = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  assert (pure (Ghost.reveal ms_secret == ms_secret_storage));

  assert (pure (byte_prefix_matches
    transcript_storage
    transcript_len_runtime
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (Seq.equal
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
  Seq.lemma_eq_intro
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

  V.to_array_pts_to c.handshake.transcript.bytes;
  let mut transcript_hash = [| 0uy; 32sz |];
  Crypto.sha256_prefix
    (V.vec_to_array c.handshake.transcript.bytes)
    transcript_len_runtime
    transcript_hash;
  V.to_vec_pts_to c.handshake.transcript.bytes;
  with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
  assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  V.to_array_pts_to c.handshake.keys.master_secret.secret;
  let mut traffic_secret_out = [| 0uy; 32sz |];
  KS.client_application_traffic_secret
    (V.vec_to_array c.handshake.keys.master_secret.secret)
    transcript_hash
    traffic_secret_out;
  V.to_vec_pts_to c.handshake.keys.master_secret.secret;
  with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
  assert (pure (traffic_secret_bytes ==
    K.client_application_traffic_secret
      (Ghost.reveal ms_secret)
      (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

  let mut traffic_key_out = [| 0uy; 32sz |];
  KS.derive_traffic_key traffic_secret_out traffic_key_out;
  let mut traffic_iv_out = [| 0uy; 12sz |];
  KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
  with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
  with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

  let traffic_secret = Ghost.hide traffic_secret_bytes;
  let material = Ghost.hide (CS.traffic_key_material_for_secret (Ghost.reveal traffic_secret));
  assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
  assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
  assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));

  fold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);

  lemma_server_role_client_application_read_traffic_install_legal
    st0.CS.cs_model
    (Ghost.reveal ms_secret);
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = Ghost.reveal material;
        };
      }))));

  install_client_application_read_traffic_keys_from_material
    c
    traffic_secret_out
    traffic_key_out
    traffic_iv_out
    #material;
}

fn derive_and_install_server_handshake_write_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerHelloSent /\
                 st0.CS.cs_model.CS.model_config.CS.config_role ==
                    CS.ServerEndpoint /\
                 Some?
                   st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
  ensures exists* material.
            connection_exactly c
              (installed_traffic_keys_for_role_state st0 {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = material;
                };
              }) **
            pure (CS.legal_connection_delta
              st0
              {
                CS.delta_event =
                  CS.ConnLocalEvent
                    (CS.LocalInstallTrafficKeysForRole {
                      CS.install_role = CS.ServerEndpoint;
                      CS.install_payload = {
                        CS.install_epoch = CS.TrafficHandshake;
                        CS.install_direction = CS.TrafficWrite;
                        CS.install_material = material;
                      };
                    });
                CS.delta_raw_sent = B.empty;
                CS.delta_raw_received = B.empty;
              }
              (installed_traffic_keys_for_role_state st0 {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = material;
                };
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (optional_secret_exactly
    c.handshake.keys.handshake_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);

  with transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes transcript_storage);
  with transcript_len.
    assert (Box.pts_to c.handshake.transcript.len transcript_len);
  let transcript_len_runtime = !c.handshake.transcript.len;
  assert (pure (transcript_len_runtime == transcript_len));
  with hs_present.
    assert (Box.pts_to c.handshake.keys.handshake_secret.present hs_present);
  with hs_secret_storage.
    assert (V.pts_to c.handshake.keys.handshake_secret.secret hs_secret_storage);
  lemma_optional_fixed_bytes_match_present_of_some
    hs_present
    hs_secret_storage
    32
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret;
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
    Some hs_secret_storage));
  let hs_secret = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
  assert (pure (Ghost.reveal hs_secret == hs_secret_storage));

  assert (pure (byte_prefix_matches
    transcript_storage
    transcript_len_runtime
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (Seq.equal
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
  Seq.lemma_eq_intro
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

  V.to_array_pts_to c.handshake.transcript.bytes;
  let mut transcript_hash = [| 0uy; 32sz |];
  Crypto.sha256_prefix
    (V.vec_to_array c.handshake.transcript.bytes)
    transcript_len_runtime
    transcript_hash;
  V.to_vec_pts_to c.handshake.transcript.bytes;
  with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
  assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  V.to_array_pts_to c.handshake.keys.handshake_secret.secret;
  let mut traffic_secret_out = [| 0uy; 32sz |];
  KS.server_handshake_traffic_secret
    (V.vec_to_array c.handshake.keys.handshake_secret.secret)
    transcript_hash
    traffic_secret_out;
  V.to_vec_pts_to c.handshake.keys.handshake_secret.secret;
  with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
  assert (pure (traffic_secret_bytes ==
    K.server_handshake_traffic_secret
      (Ghost.reveal hs_secret)
      (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

  let mut traffic_key_out = [| 0uy; 32sz |];
  KS.derive_traffic_key traffic_secret_out traffic_key_out;
  let mut traffic_iv_out = [| 0uy; 12sz |];
  KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
  with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
  with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

  let traffic_secret = Ghost.hide traffic_secret_bytes;
  let material = Ghost.hide (CS.traffic_key_material_for_secret (Ghost.reveal traffic_secret));
  assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
  assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
  assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));

  fold (optional_secret_exactly
    c.handshake.keys.handshake_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);

  lemma_server_role_server_handshake_write_traffic_install_legal
    st0.CS.cs_model
    (Ghost.reveal hs_secret);
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = Ghost.reveal material;
        };
      }))));

  install_server_handshake_write_traffic_keys_from_material
    c
    traffic_secret_out
    traffic_key_out
    traffic_iv_out
    #material;
}

fn derive_and_install_client_handshake_read_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerHelloSent /\
                 st0.CS.cs_model.CS.model_config.CS.config_role ==
                    CS.ServerEndpoint /\
                 Some?
                   st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
  ensures exists* material.
            connection_exactly c
              (installed_traffic_keys_for_role_state st0 {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = material;
                };
              }) **
            pure (CS.legal_connection_delta
              st0
              {
                CS.delta_event =
                  CS.ConnLocalEvent
                    (CS.LocalInstallTrafficKeysForRole {
                      CS.install_role = CS.ServerEndpoint;
                      CS.install_payload = {
                        CS.install_epoch = CS.TrafficHandshake;
                        CS.install_direction = CS.TrafficRead;
                        CS.install_material = material;
                      };
                    });
                CS.delta_raw_sent = B.empty;
                CS.delta_raw_received = B.empty;
              }
              (installed_traffic_keys_for_role_state st0 {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = material;
                };
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (optional_secret_exactly
    c.handshake.keys.handshake_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);

  with transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes transcript_storage);
  with transcript_len.
    assert (Box.pts_to c.handshake.transcript.len transcript_len);
  let transcript_len_runtime = !c.handshake.transcript.len;
  assert (pure (transcript_len_runtime == transcript_len));
  with hs_present.
    assert (Box.pts_to c.handshake.keys.handshake_secret.present hs_present);
  with hs_secret_storage.
    assert (V.pts_to c.handshake.keys.handshake_secret.secret hs_secret_storage);
  lemma_optional_fixed_bytes_match_present_of_some
    hs_present
    hs_secret_storage
    32
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret;
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
    Some hs_secret_storage));
  let hs_secret = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
  assert (pure (Ghost.reveal hs_secret == hs_secret_storage));

  assert (pure (byte_prefix_matches
    transcript_storage
    transcript_len_runtime
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (Seq.equal
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
  Seq.lemma_eq_intro
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

  V.to_array_pts_to c.handshake.transcript.bytes;
  let mut transcript_hash = [| 0uy; 32sz |];
  Crypto.sha256_prefix
    (V.vec_to_array c.handshake.transcript.bytes)
    transcript_len_runtime
    transcript_hash;
  V.to_vec_pts_to c.handshake.transcript.bytes;
  with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
  assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  V.to_array_pts_to c.handshake.keys.handshake_secret.secret;
  let mut traffic_secret_out = [| 0uy; 32sz |];
  KS.client_handshake_traffic_secret
    (V.vec_to_array c.handshake.keys.handshake_secret.secret)
    transcript_hash
    traffic_secret_out;
  V.to_vec_pts_to c.handshake.keys.handshake_secret.secret;
  with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
  assert (pure (traffic_secret_bytes ==
    K.client_handshake_traffic_secret
      (Ghost.reveal hs_secret)
      (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

  let mut traffic_key_out = [| 0uy; 32sz |];
  KS.derive_traffic_key traffic_secret_out traffic_key_out;
  let mut traffic_iv_out = [| 0uy; 12sz |];
  KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
  with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
  with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

  let traffic_secret = Ghost.hide traffic_secret_bytes;
  let material = Ghost.hide (CS.traffic_key_material_for_secret (Ghost.reveal traffic_secret));
  assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
  assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
  assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));

  fold (optional_secret_exactly
    c.handshake.keys.handshake_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);

  lemma_server_role_client_handshake_read_traffic_install_legal
    st0.CS.cs_model
    (Ghost.reveal hs_secret);
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = Ghost.reveal material;
        };
      }))));

  install_client_handshake_read_traffic_keys_from_material
    c
    traffic_secret_out
    traffic_key_out
    traffic_iv_out
    #material;
}

fn try_derive_shared_secret
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* shared.
               connection_exactly c (derived_shared_secret_state st0 shared) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (derived_shared_secret_state st0 shared))
           else
             connection_exactly c st0)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  let role_ok = config_role_is_client c.config;
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (server_key_share_exactly
    c.handshake.server_key_share
    st0.CS.cs_model.CS.model_handshake);
  unfold (optional_fixed_bytes_exactly
    c.handshake.server_key_share
    32
    (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
     | Some sh -> Some sh.M.key_share
     | None -> None));
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 3uy;

  with start_present. assert (pure True);
  let has_start = !c.handshake.start.present;
  assert (pure (has_start == start_present));

  let has_server_share = !c.handshake.server_key_share.present;
  with server_share_present.
    assert (Box.pts_to c.handshake.server_key_share.present server_share_present);
  with server_share_storage.
    assert (V.pts_to c.handshake.server_key_share.bytes server_share_storage);
  let server_share_storage_e = Ghost.hide server_share_storage;
  assert (pure (has_server_share == server_share_present));

  let ready = role_ok && tag_ok && stage_ok && has_start && has_server_share;

  if ready {
    assert (pure (st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint));
    assert (pure (U8.v tag == 1));
    assert (pure (U8.v stage == 3));
    assert (pure has_start);
    assert (pure has_server_share);
    assert (pure server_share_present);
    lemma_optional_fixed_bytes_match_some
      server_share_present
      server_share_storage
      32
      (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
       | Some sh -> Some sh.M.key_share
       | None -> None);
    lemma_server_key_share_option_some
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello
      server_share_storage;
    let sh = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
    assert (pure (st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerHelloReceived));
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some (Ghost.reveal sh)));
    assert (pure (server_share_storage == (Ghost.reveal sh).M.key_share));

    if has_start {
    unfold (handshake_start_payload_exactly
      c.handshake.start
      has_start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    with start_spec. assert (pure True);
    unfold (handshake_start_fields_exactly c.handshake.start start_spec);
    lemma_len32_refinement_tautology();
    unfold (optional_fixed_bytes_exactly
      c.handshake.start.client_key_share_private
      32
      start_spec.CS.start_client_key_share_private);

    with private_present private_storage. _;
    let private_storage_e = Ghost.hide private_storage;
    let has_private = !c.handshake.start.client_key_share_private.present;
    assert (pure (has_private == private_present));

    if has_private {
      assert (pure private_present);
      lemma_optional_fixed_bytes_match_some
        private_present
        (Ghost.reveal private_storage_e)
        32
        start_spec.CS.start_client_key_share_private;
      assert (pure (start_spec.CS.start_client_key_share_private == Some (Ghost.reveal private_storage_e)));
      let private_spec = private_storage_e;
      assert (pure (B.length (Ghost.reveal private_storage_e) == 32));
      assert (pure (B.length (Ghost.reveal server_share_storage_e) == 32));
      lemma_len32_refinement_tautology();

        V.to_array_pts_to c.handshake.start.client_key_share_private.bytes;
        V.to_array_pts_to c.handshake.server_key_share.bytes;
        let mut shared_out = [| 0uy; 32sz |];
        let crypto_ok =
          Crypto.x25519_shared_runtime
            (V.vec_to_array c.handshake.start.client_key_share_private.bytes)
            (V.vec_to_array c.handshake.server_key_share.bytes)
            shared_out;
        V.to_vec_pts_to c.handshake.start.client_key_share_private.bytes;
        V.to_vec_pts_to c.handshake.server_key_share.bytes;

        if crypto_ok {
          with shared. assert (ArrPts.pts_to shared_out shared);
          ArrPts.pts_to_len shared_out;
          assert (pure (B.length shared == 32));
          assert (pure (Crypto.x25519_shared_call (Ghost.reveal private_storage_e) (Ghost.reveal server_share_storage_e) shared crypto_ok));
          Crypto.lemma_x25519_shared_call_success (Ghost.reveal private_storage_e) (Ghost.reveal server_share_storage_e) shared crypto_ok;
          assert (pure (Some? (TLS13.Crypto.Spec.x25519_shared (Ghost.reveal private_storage_e) (Ghost.reveal server_share_storage_e))));
          assert (pure (Some?.v (TLS13.Crypto.Spec.x25519_shared (Ghost.reveal private_storage_e) (Ghost.reveal server_share_storage_e)) == shared));
          let shared_secret = Ghost.hide (Some?.v (TLS13.Crypto.Spec.x25519_shared (Ghost.reveal private_storage_e) (Ghost.reveal server_share_storage_e)));
          assert (pure (Ghost.reveal shared_secret == shared));
          assert (pure (TLS13.Crypto.Spec.x25519_shared (Ghost.reveal private_storage_e) (Ghost.reveal server_share_storage_e) == Some (Ghost.reveal shared_secret)));
          assert (pure (TLS13.Crypto.Spec.x25519_shared (Ghost.reveal private_spec) (Ghost.reveal sh).M.key_share == Some (Ghost.reveal shared_secret)));
          assert (pure (CS.legal_event
            st0.CS.cs_model
            (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret (Ghost.reveal shared_secret)))));

          let mut early_out = [| 0uy; 32sz |];
          KS.early_secret_empty early_out;
          let mut handshake_out = [| 0uy; 32sz |];
          KS.handshake_secret early_out shared_out 32sz handshake_out;
          let mut master_out = [| 0uy; 32sz |];
          KS.master_secret handshake_out master_out;

          store_optional_secret c.handshake.keys.shared_secret shared_out #shared_secret;
          store_optional_secret
            c.handshake.keys.early_secret
            early_out
            #(K.early_secret B.empty);
          store_optional_secret
            c.handshake.keys.handshake_secret
            handshake_out
            #(K.handshake_secret (K.early_secret B.empty) (Ghost.reveal shared_secret));
          store_optional_secret
            c.handshake.keys.master_secret
            master_out
            #(K.master_secret (K.handshake_secret (K.early_secret B.empty) (Ghost.reveal shared_secret)));

          fold (key_schedule_exactly
            c.handshake.keys
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_handshake.CS.hs_keys);

          fold (optional_fixed_bytes_exactly
            c.handshake.start.client_key_share_private
            32
            start_spec.CS.start_client_key_share_private);
          fold (handshake_start_fields_exactly c.handshake.start start_spec);
          fold (handshake_start_payload_exactly
            c.handshake.start
            has_start
            st0.CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (handshake_start_exactly
            c.handshake.start
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (optional_fixed_bytes_exactly
            c.handshake.server_key_share
            32
            (match (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_handshake.CS.hs_server_hello with
             | Some sh -> Some sh.M.key_share
             | None -> None));
          fold (server_key_share_exactly
            c.handshake.server_key_share
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_handshake);
          fold (handshake_messages_exactly
            c.handshake.messages
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_handshake);
          fold (handshake_exactly
            c.handshake
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_handshake);
          fold (control_exactly
            c.control
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_control
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model.CS.model_failure);
          fold (connection_model_exactly
            c
            (derived_shared_secret_state st0 (Ghost.reveal shared_secret)).CS.cs_model);

          lemma_derived_shared_secret_state_evolves st0 (Ghost.reveal shared_secret);
          MR.update c.ghost_state (derived_shared_secret_state st0 (Ghost.reveal shared_secret));
          fold (connection_exactly c (derived_shared_secret_state st0 (Ghost.reveal shared_secret)));
          true
        } else {
          with shared_old. assert (ArrPts.pts_to shared_out shared_old);
          fold (optional_fixed_bytes_exactly
            c.handshake.start.client_key_share_private
            32
            start_spec.CS.start_client_key_share_private);
          fold (handshake_start_fields_exactly c.handshake.start start_spec);
          fold (handshake_start_payload_exactly
            c.handshake.start
            has_start
            st0.CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (handshake_start_exactly
            c.handshake.start
            st0.CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (optional_fixed_bytes_exactly
            c.handshake.server_key_share
            32
            (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
             | Some sh -> Some sh.M.key_share
             | None -> None));
          fold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
          fold (key_schedule_exactly
            c.handshake.keys
            st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
          fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
          fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
          fold (control_exactly
            c.control
            st0.CS.cs_model.CS.model_control
            st0.CS.cs_model.CS.model_failure);
          fold (connection_model_exactly c st0.CS.cs_model);
          fold (connection_exactly c st0);
          false
        }
    } else {
      fold (optional_fixed_bytes_exactly
        c.handshake.start.client_key_share_private
        32
        start_spec.CS.start_client_key_share_private);
      fold (handshake_start_fields_exactly c.handshake.start start_spec);
      fold (handshake_start_payload_exactly
        c.handshake.start
        has_start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (optional_fixed_bytes_exactly
        c.handshake.server_key_share
        32
        (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
         | Some sh -> Some sh.M.key_share
         | None -> None));
      fold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
      fold (key_schedule_exactly c.handshake.keys st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
      fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      fold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    }
    } else {
      fold (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (optional_fixed_bytes_exactly
        c.handshake.server_key_share
        32
        (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
         | Some sh -> Some sh.M.key_share
         | None -> None));
      fold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
      fold (key_schedule_exactly c.handshake.keys st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
      fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      fold (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    }
  } else {
      fold (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
      fold (optional_fixed_bytes_exactly
        c.handshake.server_key_share
        32
        (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
         | Some sh -> Some sh.M.key_share
         | None -> None));
      fold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
      fold (key_schedule_exactly c.handshake.keys st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
      fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn try_install_client_handshake_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* material.
               connection_exactly c
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficHandshake;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = material;
                 }) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent
                       (CS.LocalInstallTrafficKeys {
                         CS.install_epoch = CS.TrafficHandshake;
                         CS.install_direction = CS.TrafficWrite;
                         CS.install_material = material;
                       });
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficHandshake;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = material;
                 }))
           else
             connection_exactly c st0)
{
  let ready = can_install_handshake_traffic_keys c;
  if ready {
    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
    unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    unfold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    unfold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    unfold (optional_secret_exactly
      c.handshake.keys.handshake_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);

    with transcript_storage.
      assert (V.pts_to c.handshake.transcript.bytes transcript_storage);
    with transcript_len.
      assert (Box.pts_to c.handshake.transcript.len transcript_len);
    let transcript_len_runtime = !c.handshake.transcript.len;
    assert (pure (transcript_len_runtime == transcript_len));
    with hs_present.
      assert (Box.pts_to c.handshake.keys.handshake_secret.present hs_present);
    with hs_secret_storage.
      assert (V.pts_to c.handshake.keys.handshake_secret.secret hs_secret_storage);
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret));
    lemma_optional_fixed_bytes_match_present_of_some
      hs_present
      hs_secret_storage
      32
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret;
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
      Some hs_secret_storage));
    let hs_secret = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
    assert (pure (Ghost.reveal hs_secret == hs_secret_storage));

    assert (pure (byte_prefix_matches
      transcript_storage
      transcript_len_runtime
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    assert (pure (Seq.equal
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
    Seq.lemma_eq_intro
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

    V.to_array_pts_to c.handshake.transcript.bytes;
    let mut transcript_hash = [| 0uy; 32sz |];
    Crypto.sha256_prefix
      (V.vec_to_array c.handshake.transcript.bytes)
      transcript_len_runtime
      transcript_hash;
    V.to_vec_pts_to c.handshake.transcript.bytes;
    with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
    assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

    V.to_array_pts_to c.handshake.keys.handshake_secret.secret;
    let mut traffic_secret_out = [| 0uy; 32sz |];
    KS.client_handshake_traffic_secret
      (V.vec_to_array c.handshake.keys.handshake_secret.secret)
      transcript_hash
      traffic_secret_out;
    V.to_vec_pts_to c.handshake.keys.handshake_secret.secret;
    with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
    assert (pure (traffic_secret_bytes ==
      K.client_handshake_traffic_secret
        (Ghost.reveal hs_secret)
        (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

    let mut traffic_key_out = [| 0uy; 32sz |];
    KS.derive_traffic_key traffic_secret_out traffic_key_out;
    let mut traffic_iv_out = [| 0uy; 12sz |];
    KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
    with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
    with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

    let traffic_secret = Ghost.hide traffic_secret_bytes;
    let material = Ghost.hide (CS.traffic_key_material_for_secret (Ghost.reveal traffic_secret));
    assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));
    let install = Ghost.hide ({
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = Ghost.reveal material;
    });

    lemma_client_handshake_traffic_install_legal
      st0.CS.cs_model
      (Ghost.reveal hs_secret);
    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys (Ghost.reveal install)))));

    store_traffic_key_material
      c.handshake.keys.client_handshake_traffic
      traffic_secret_out
      traffic_key_out
      traffic_iv_out
      #material;
    fold (optional_secret_exactly
      c.handshake.keys.handshake_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_keys);

    Rec.install_handshake_keys_runtime c.records.write traffic_key_out traffic_iv_out;
    assert (pure ((Ghost.reveal install).CS.install_epoch == CS.TrafficHandshake));
    assert (pure ((Ghost.reveal install).CS.install_direction == CS.TrafficWrite));
    assert (pure ((Ghost.reveal install).CS.install_material == Ghost.reveal material));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read ==
      st0.CS.cs_model.CS.model_record.CS.record_read));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write ==
      R.install_keys
        st0.CS.cs_model.CS.model_record.CS.record_write
        R.Handshake
        (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv));
    rewrite (Rec.is_record_state c.records.read st0.CS.cs_model.CS.model_record.CS.record_read)
      as (Rec.is_record_state
        c.records.read
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read);
    rewrite (Rec.is_record_state
      c.records.write
      (R.install_keys
        st0.CS.cs_model.CS.model_record.CS.record_write
        R.Handshake
        (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv))
      as (Rec.is_record_state
        c.records.write
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write);
    fold (record_layer_exactly
      c.records
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record);

    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_start));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    rewrite (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_exactly
        c.handshake.start
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start);
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
    unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_messages_exactly
      c.handshake.messages
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
    fold (server_key_share_exactly
      c.handshake.server_key_share
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    rewrite (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
      as (peer_exactly
        c.handshake.validated_peer
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    rewrite (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
      as (handshake_buffers_exactly
        c.handshake.buffers
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_exactly
      c.handshake
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_failure);
    fold (connection_model_exactly
      c
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model);

    lemma_installed_traffic_keys_state_evolves st0 (Ghost.reveal install);
    assert (pure (CS.connection_state_evolves
      st0
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    assert (pure (CS.connection_state_consistent
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    MR.update c.ghost_state (installed_traffic_keys_state st0 (Ghost.reveal install));
    fold (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)));
    assert (pure (Ghost.reveal install == {
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = Ghost.reveal material;
    }));
    rewrite (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)))
      as (connection_exactly c (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = Ghost.reveal material;
      }));
    assert (pure (CS.legal_connection_delta
      st0
      {
        CS.delta_event =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = Ghost.reveal material;
            });
        CS.delta_raw_sent = B.empty;
        CS.delta_raw_received = B.empty;
      }
      (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = Ghost.reveal material;
      })));
    true
  } else {
    false
  }
}

fn try_install_server_handshake_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* material.
               connection_exactly c
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficHandshake;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = material;
                 }) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent
                       (CS.LocalInstallTrafficKeys {
                         CS.install_epoch = CS.TrafficHandshake;
                         CS.install_direction = CS.TrafficRead;
                         CS.install_material = material;
                       });
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficHandshake;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = material;
                 }))
           else
             connection_exactly c st0)
{
  let ready = can_install_handshake_traffic_keys c;
  if ready {
    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
    unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    unfold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    unfold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    unfold (optional_secret_exactly
      c.handshake.keys.handshake_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);

    with transcript_storage.
      assert (V.pts_to c.handshake.transcript.bytes transcript_storage);
    with transcript_len.
      assert (Box.pts_to c.handshake.transcript.len transcript_len);
    let transcript_len_runtime = !c.handshake.transcript.len;
    assert (pure (transcript_len_runtime == transcript_len));
    with hs_present.
      assert (Box.pts_to c.handshake.keys.handshake_secret.present hs_present);
    with hs_secret_storage.
      assert (V.pts_to c.handshake.keys.handshake_secret.secret hs_secret_storage);
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret));
    lemma_optional_fixed_bytes_match_present_of_some
      hs_present
      hs_secret_storage
      32
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret;
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
      Some hs_secret_storage));
    let hs_secret = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
    assert (pure (Ghost.reveal hs_secret == hs_secret_storage));

    assert (pure (byte_prefix_matches
      transcript_storage
      transcript_len_runtime
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    assert (pure (Seq.equal
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
    Seq.lemma_eq_intro
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

    V.to_array_pts_to c.handshake.transcript.bytes;
    let mut transcript_hash = [| 0uy; 32sz |];
    Crypto.sha256_prefix
      (V.vec_to_array c.handshake.transcript.bytes)
      transcript_len_runtime
      transcript_hash;
    V.to_vec_pts_to c.handshake.transcript.bytes;
    with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
    assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

    V.to_array_pts_to c.handshake.keys.handshake_secret.secret;
    let mut traffic_secret_out = [| 0uy; 32sz |];
    KS.server_handshake_traffic_secret
      (V.vec_to_array c.handshake.keys.handshake_secret.secret)
      transcript_hash
      traffic_secret_out;
    V.to_vec_pts_to c.handshake.keys.handshake_secret.secret;
    with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
    assert (pure (traffic_secret_bytes ==
      K.server_handshake_traffic_secret
        (Ghost.reveal hs_secret)
        (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

    let mut traffic_key_out = [| 0uy; 32sz |];
    KS.derive_traffic_key traffic_secret_out traffic_key_out;
    let mut traffic_iv_out = [| 0uy; 12sz |];
    KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
    with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
    with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

    let traffic_secret = Ghost.hide traffic_secret_bytes;
    let material = Ghost.hide (CS.traffic_key_material_for_secret (Ghost.reveal traffic_secret));
    assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));
    let install = Ghost.hide ({
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = Ghost.reveal material;
    });

    lemma_server_handshake_traffic_install_legal
      st0.CS.cs_model
      (Ghost.reveal hs_secret);
    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys (Ghost.reveal install)))));

    store_traffic_key_material
      c.handshake.keys.server_handshake_traffic
      traffic_secret_out
      traffic_key_out
      traffic_iv_out
      #material;
    fold (optional_secret_exactly
      c.handshake.keys.handshake_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_keys);

    Rec.install_handshake_keys_runtime c.records.read traffic_key_out traffic_iv_out;
    assert (pure ((Ghost.reveal install).CS.install_epoch == CS.TrafficHandshake));
    assert (pure ((Ghost.reveal install).CS.install_direction == CS.TrafficRead));
    assert (pure ((Ghost.reveal install).CS.install_material == Ghost.reveal material));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write ==
      st0.CS.cs_model.CS.model_record.CS.record_write));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read ==
      R.install_keys
        st0.CS.cs_model.CS.model_record.CS.record_read
        R.Handshake
        (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv));
    rewrite (Rec.is_record_state c.records.write st0.CS.cs_model.CS.model_record.CS.record_write)
      as (Rec.is_record_state
        c.records.write
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write);
    rewrite (Rec.is_record_state
      c.records.read
      (R.install_keys
        st0.CS.cs_model.CS.model_record.CS.record_read
        R.Handshake
        (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv))
      as (Rec.is_record_state
        c.records.read
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read);
    fold (record_layer_exactly
      c.records
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record);

    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_start));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    rewrite (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_exactly
        c.handshake.start
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start);
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
    unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_messages_exactly
      c.handshake.messages
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
    fold (server_key_share_exactly
      c.handshake.server_key_share
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    rewrite (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
      as (peer_exactly
        c.handshake.validated_peer
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    rewrite (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
      as (handshake_buffers_exactly
        c.handshake.buffers
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_exactly
      c.handshake
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_failure);
    fold (connection_model_exactly
      c
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model);

    lemma_installed_traffic_keys_state_evolves st0 (Ghost.reveal install);
    assert (pure (CS.connection_state_evolves
      st0
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    assert (pure (CS.connection_state_consistent
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    MR.update c.ghost_state (installed_traffic_keys_state st0 (Ghost.reveal install));
    fold (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)));
    assert (pure (Ghost.reveal install == {
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = Ghost.reveal material;
    }));
    rewrite (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)))
      as (connection_exactly c (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = Ghost.reveal material;
      }));
    assert (pure (CS.legal_connection_delta
      st0
      {
        CS.delta_event =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = Ghost.reveal material;
            });
        CS.delta_raw_sent = B.empty;
        CS.delta_raw_received = B.empty;
      }
      (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = Ghost.reveal material;
      })));
    true
  } else {
    false
  }
}

fn try_install_client_application_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* material.
               connection_exactly c
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = material;
                 }) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent
                       (CS.LocalInstallTrafficKeys {
                         CS.install_epoch = CS.TrafficApplication;
                         CS.install_direction = CS.TrafficWrite;
                         CS.install_material = material;
                       });
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = material;
                 }))
           else
             connection_exactly c st0)
{
  let ready = can_install_application_traffic_keys c;
  if ready {
    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
    unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    unfold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    unfold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    unfold (optional_secret_exactly
      c.handshake.keys.master_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);

    with transcript_storage.
      assert (V.pts_to c.handshake.transcript.bytes transcript_storage);
    with transcript_len.
      assert (Box.pts_to c.handshake.transcript.len transcript_len);
    let transcript_len_runtime = !c.handshake.transcript.len;
    assert (pure (transcript_len_runtime == transcript_len));
    with ms_present.
      assert (Box.pts_to c.handshake.keys.master_secret.present ms_present);
    with ms_secret_storage.
      assert (V.pts_to c.handshake.keys.master_secret.secret ms_secret_storage);
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret));
    lemma_optional_fixed_bytes_match_present_of_some
      ms_present
      ms_secret_storage
      32
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret;
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
      Some ms_secret_storage));
    let ms_secret = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
    assert (pure (Ghost.reveal ms_secret == ms_secret_storage));

    assert (pure (byte_prefix_matches
      transcript_storage
      transcript_len_runtime
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    assert (pure (Seq.equal
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
    Seq.lemma_eq_intro
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

    V.to_array_pts_to c.handshake.transcript.bytes;
    let mut transcript_hash = [| 0uy; 32sz |];
    Crypto.sha256_prefix
      (V.vec_to_array c.handshake.transcript.bytes)
      transcript_len_runtime
      transcript_hash;
    V.to_vec_pts_to c.handshake.transcript.bytes;
    with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
    assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

    V.to_array_pts_to c.handshake.keys.master_secret.secret;
    let mut traffic_secret_out = [| 0uy; 32sz |];
    KS.client_application_traffic_secret
      (V.vec_to_array c.handshake.keys.master_secret.secret)
      transcript_hash
      traffic_secret_out;
    V.to_vec_pts_to c.handshake.keys.master_secret.secret;
    with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
    assert (pure (traffic_secret_bytes ==
      K.client_application_traffic_secret
        (Ghost.reveal ms_secret)
        (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

    let mut traffic_key_out = [| 0uy; 32sz |];
    KS.derive_traffic_key traffic_secret_out traffic_key_out;
    let mut traffic_iv_out = [| 0uy; 12sz |];
    KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
    with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
    with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

    let traffic_secret = Ghost.hide traffic_secret_bytes;
    let material = Ghost.hide (CS.traffic_key_material_for_secret (Ghost.reveal traffic_secret));
    assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));
    let install = Ghost.hide ({
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = Ghost.reveal material;
    });

    lemma_client_application_traffic_install_legal
      st0.CS.cs_model
      (Ghost.reveal ms_secret);
    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys (Ghost.reveal install)))));

    store_traffic_key_material
      c.handshake.keys.client_application_traffic
      traffic_secret_out
      traffic_key_out
      traffic_iv_out
      #material;
    fold (optional_secret_exactly
      c.handshake.keys.master_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_keys);

    assert (pure ((Ghost.reveal install).CS.install_epoch == CS.TrafficApplication));
    assert (pure ((Ghost.reveal install).CS.install_direction == CS.TrafficWrite));
    assert (pure ((Ghost.reveal install).CS.install_material == Ghost.reveal material));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read ==
      st0.CS.cs_model.CS.model_record.CS.record_read));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write ==
      st0.CS.cs_model.CS.model_record.CS.record_write));
    rewrite (Rec.is_record_state c.records.read st0.CS.cs_model.CS.model_record.CS.record_read)
      as (Rec.is_record_state
        c.records.read
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read);
    rewrite (Rec.is_record_state c.records.write st0.CS.cs_model.CS.model_record.CS.record_write)
      as (Rec.is_record_state
        c.records.write
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write);
    fold (record_layer_exactly
      c.records
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record);

    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_start));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    rewrite (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_exactly
        c.handshake.start
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start);
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
    unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_messages_exactly
      c.handshake.messages
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
    fold (server_key_share_exactly
      c.handshake.server_key_share
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    rewrite (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
      as (peer_exactly
        c.handshake.validated_peer
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    rewrite (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
      as (handshake_buffers_exactly
        c.handshake.buffers
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_exactly
      c.handshake
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_failure);
    fold (connection_model_exactly
      c
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model);

    lemma_installed_traffic_keys_state_evolves st0 (Ghost.reveal install);
    assert (pure (CS.connection_state_evolves
      st0
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    assert (pure (CS.connection_state_consistent
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    MR.update c.ghost_state (installed_traffic_keys_state st0 (Ghost.reveal install));
    fold (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)));
    assert (pure (Ghost.reveal install == {
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = Ghost.reveal material;
    }));
    rewrite (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)))
      as (connection_exactly c (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = Ghost.reveal material;
      }));
    assert (pure (CS.legal_connection_delta
      st0
      {
        CS.delta_event =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = Ghost.reveal material;
            });
        CS.delta_raw_sent = B.empty;
        CS.delta_raw_received = B.empty;
      }
      (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = Ghost.reveal material;
      })));
    true
  } else {
    false
  }
}

fn try_install_server_application_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* material.
               connection_exactly c
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = material;
                 }) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent
                       (CS.LocalInstallTrafficKeys {
                         CS.install_epoch = CS.TrafficApplication;
                         CS.install_direction = CS.TrafficRead;
                         CS.install_material = material;
                       });
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = material;
                 }))
           else
             connection_exactly c st0)
{
  let ready = can_install_application_traffic_keys c;
  if ready {
    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
    unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    unfold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    unfold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    unfold (optional_secret_exactly
      c.handshake.keys.master_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);

    with transcript_storage.
      assert (V.pts_to c.handshake.transcript.bytes transcript_storage);
    with transcript_len.
      assert (Box.pts_to c.handshake.transcript.len transcript_len);
    let transcript_len_runtime = !c.handshake.transcript.len;
    assert (pure (transcript_len_runtime == transcript_len));
    with ms_present.
      assert (Box.pts_to c.handshake.keys.master_secret.present ms_present);
    with ms_secret_storage.
      assert (V.pts_to c.handshake.keys.master_secret.secret ms_secret_storage);
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret));
    lemma_optional_fixed_bytes_match_present_of_some
      ms_present
      ms_secret_storage
      32
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret;
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
      Some ms_secret_storage));
    let ms_secret = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
    assert (pure (Ghost.reveal ms_secret == ms_secret_storage));

    assert (pure (byte_prefix_matches
      transcript_storage
      transcript_len_runtime
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    assert (pure (Seq.equal
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
    Seq.lemma_eq_intro
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

    V.to_array_pts_to c.handshake.transcript.bytes;
    let mut transcript_hash = [| 0uy; 32sz |];
    Crypto.sha256_prefix
      (V.vec_to_array c.handshake.transcript.bytes)
      transcript_len_runtime
      transcript_hash;
    V.to_vec_pts_to c.handshake.transcript.bytes;
    with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
    assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

    V.to_array_pts_to c.handshake.keys.master_secret.secret;
    let mut traffic_secret_out = [| 0uy; 32sz |];
    KS.server_application_traffic_secret
      (V.vec_to_array c.handshake.keys.master_secret.secret)
      transcript_hash
      traffic_secret_out;
    V.to_vec_pts_to c.handshake.keys.master_secret.secret;
    with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
    assert (pure (traffic_secret_bytes ==
      K.server_application_traffic_secret
        (Ghost.reveal ms_secret)
        (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

    let mut traffic_key_out = [| 0uy; 32sz |];
    KS.derive_traffic_key traffic_secret_out traffic_key_out;
    let mut traffic_iv_out = [| 0uy; 12sz |];
    KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
    with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
    with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

    let traffic_secret = Ghost.hide traffic_secret_bytes;
    let material = Ghost.hide (CS.traffic_key_material_for_secret (Ghost.reveal traffic_secret));
    assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
    assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));
    let install = Ghost.hide ({
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = Ghost.reveal material;
    });

    lemma_server_application_traffic_install_legal
      st0.CS.cs_model
      (Ghost.reveal ms_secret);
    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys (Ghost.reveal install)))));

    store_traffic_key_material
      c.handshake.keys.server_application_traffic
      traffic_secret_out
      traffic_key_out
      traffic_iv_out
      #material;
    fold (optional_secret_exactly
      c.handshake.keys.master_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_keys);

    Rec.install_application_keys_runtime c.records.read traffic_key_out traffic_iv_out;
    assert (pure ((Ghost.reveal install).CS.install_epoch == CS.TrafficApplication));
    assert (pure ((Ghost.reveal install).CS.install_direction == CS.TrafficRead));
    assert (pure ((Ghost.reveal install).CS.install_material == Ghost.reveal material));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write ==
      st0.CS.cs_model.CS.model_record.CS.record_write));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read ==
      R.install_keys
        st0.CS.cs_model.CS.model_record.CS.record_read
        R.Application
        (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv));
    rewrite (Rec.is_record_state c.records.write st0.CS.cs_model.CS.model_record.CS.record_write)
      as (Rec.is_record_state
        c.records.write
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_write);
    rewrite (Rec.is_record_state
      c.records.read
      (R.install_keys
        st0.CS.cs_model.CS.model_record.CS.record_read
        R.Application
        (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv))
      as (Rec.is_record_state
        c.records.read
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record.CS.record_read);
    fold (record_layer_exactly
      c.records
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_record);

    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_start));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
    rewrite (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_exactly
        c.handshake.start
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_start);
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
    assert (pure ((installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
    unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_messages_exactly
      c.handshake.messages
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
    fold (server_key_share_exactly
      c.handshake.server_key_share
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    rewrite (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
      as (peer_exactly
        c.handshake.validated_peer
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    rewrite (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
      as (handshake_buffers_exactly
        c.handshake.buffers
        (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_exactly
      c.handshake
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_control
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model.CS.model_failure);
    fold (connection_model_exactly
      c
      (installed_traffic_keys_state st0 (Ghost.reveal install)).CS.cs_model);

    lemma_installed_traffic_keys_state_evolves st0 (Ghost.reveal install);
    assert (pure (CS.connection_state_evolves
      st0
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    assert (pure (CS.connection_state_consistent
      (installed_traffic_keys_state st0 (Ghost.reveal install))));
    MR.update c.ghost_state (installed_traffic_keys_state st0 (Ghost.reveal install));
    fold (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)));
    assert (pure (Ghost.reveal install == {
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = Ghost.reveal material;
    }));
    rewrite (connection_exactly c (installed_traffic_keys_state st0 (Ghost.reveal install)))
      as (connection_exactly c (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = Ghost.reveal material;
      }));
    assert (pure (CS.legal_connection_delta
      st0
      {
        CS.delta_event =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = Ghost.reveal material;
            });
        CS.delta_raw_sent = B.empty;
        CS.delta_raw_received = B.empty;
      }
      (installed_traffic_keys_state st0 {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = Ghost.reveal material;
      })));
    true
  } else {
    false
  }
}
