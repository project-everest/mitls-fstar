module TLS13.Impl.Server.Send

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CM = TLS13.Impl.ConnectionState.Model
module CLH = TLS13.Impl.ConnectionState.LocalHandshake
module CR = TLS13.Impl.ConnectionState.Repr
module H = TLS13.Handshake.Spec
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module KS = TLS13.KeySchedule
module M = TLS13.Messages
module O = TLS13.OpenSSL
module R = TLS13.Record.Spec
module Ser = TLS13.Impl.Serializer
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Tr = TLS13.Transcript
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec

noextract
let lemma_server_handshake_write_seal_some
  (st:CS.connection_state)
  (aad:B.bytes)
  (msg:M.tls_message)
  : Lemma
      (requires ST.server_end_to_end_invariant st /\
                st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                (st.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent \/
                 st.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent) /\
                Some?
                  st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic)
      (ensures Some? (R.seal
        st.CS.cs_model.CS.model_record.CS.record_write
        aad
        {
          R.content_type = T.ApplicationData;
          R.fragment = CS.sent_tls_inner_plaintext_fragment msg;
        }))
=
  assert_norm (ST.server_end_to_end_invariant st ==
    (ST.server_state_correct st /\
     ST.server_raw_to_message_replay_consistent st));
  assert (ST.server_state_correct st);
  assert_norm (ST.server_state_correct st ==
    (ST.server_state_core_correct st /\
     CS.connection_state_sent_seal_replay_consistent st /\
     CS.connection_state_received_decode_replay_consistent st));
  assert (ST.server_state_core_correct st);
  assert_norm (ST.server_state_core_correct st ==
    (st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
     Some? st.CS.cs_model.CS.model_config.CS.config_server /\
     (match st.CS.cs_model.CS.model_config.CS.config_server with
      | Some cfg ->
        B.length cfg.CS.server_certificate_chain <=
          Bounds.max_server_certificate_chain_len
      | None -> False) /\
     CS.connection_state_consistent st /\
     CS.connection_state_full_log_consistent_for_role CS.ServerEndpoint st));
  assert (CS.connection_state_consistent st);
  CSL.lemma_server_handshake_write_record_has_keys st;
  assert (CS.connection_state_full_log_consistent_for_role CS.ServerEndpoint st);
  assert (CS.connection_state_layered_log_consistent_for_role CS.ServerEndpoint st);
  assert (CS.connection_state_record_keys_consistent_for_role CS.ServerEndpoint st);
  assert (CS.model_record_keys_consistent_for_role CS.ServerEndpoint st.CS.cs_model);
  assert (CS.record_write_key_schedule_projection_for_role
    CS.ServerEndpoint
    st.CS.cs_model);
  assert (
    match st.CS.cs_model.CS.model_record.CS.record_write.R.key,
          st.CS.cs_model.CS.model_record.CS.record_write.R.static_iv with
    | Some _, Some _ -> True
    | _, _ -> False);
  CM.lemma_seal_some_of_keys
    st.CS.cs_model.CS.model_record.CS.record_write
    aad
    {
      R.content_type = T.ApplicationData;
      R.fragment = CS.sent_tls_inner_plaintext_fragment msg;
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

fn build_server_hello_from_arrays
  (server_random:array U8.t)
  (server_key_share:array U8.t)
  (#sh:erased M.server_hello)
  requires pts_to server_random 'server_random_bytes **
           pts_to server_key_share 'server_key_share_bytes **
           pure (B.length 'server_random_bytes == 32 /\
                B.length 'server_key_share_bytes == 32 /\
                Ghost.reveal sh == {
                  M.random = Ghost.reveal 'server_random_bytes;
                  M.key_share = Ghost.reveal 'server_key_share_bytes;
                  M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
                  M.body = B.empty;
                })
  returns lsh:IM.server_hello
  ensures pts_to server_random 'server_random_bytes **
          pts_to server_key_share 'server_key_share_bytes **
          IM.is_valid_server_hello lsh sh
{
  let random_vec = V.alloc 0uy 32sz;
  let key_share_vec = V.alloc 0uy 32sz;
  CR.copy_fixed32_array_to_vec server_random random_vec;
  CR.copy_fixed32_array_to_vec server_key_share key_share_vec;
  let lsh = {
    IM.server_hello_random = random_vec;
    IM.server_hello_key_share = key_share_vec;
    IM.server_hello_cipher_suite = 0x1303us;
  };
  with random_bytes. assert (V.pts_to random_vec random_bytes);
  with key_share_bytes. assert (V.pts_to key_share_vec key_share_bytes);
  assert (pure (Seq.equal random_bytes (Ghost.reveal 'server_random_bytes)));
  assert (pure (Seq.equal key_share_bytes (Ghost.reveal 'server_key_share_bytes)));
  assert_norm (IM.cipher_suite_matches 0x1303us T.TLS_CHACHA20_POLY1305_SHA256);
  rewrite (V.pts_to random_vec random_bytes)
    as (V.pts_to lsh.IM.server_hello_random random_bytes);
  rewrite (V.pts_to key_share_vec key_share_bytes)
    as (V.pts_to lsh.IM.server_hello_key_share key_share_bytes);
  fold (IM.is_valid_server_hello
    lsh
    (Ghost.reveal sh));
  lsh
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
                   M.body = B.empty;
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
                    M.body = B.empty;
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
  let sh = Ghost.hide {
    M.random = Ghost.reveal 'server_random_bytes;
    M.key_share = Ghost.reveal 'server_key_share_bytes;
    M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    M.body = B.empty;
  };
  let lsh =
    build_server_hello_from_arrays
      server_random
      server_key_share
      #sh;
  process_send_server_hello_serialized
    s
    lsh
    #sh
    network_out
    network_out_len
    app_out
    app_out_len
}

fn process_send_server_hello_with_derived_public_from_private_array
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
                 SZ.v network_out_len == 95 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 (let sh = {
                   M.random = Ghost.reveal 'server_random_bytes;
                   M.key_share =
                     CryptoSpec.x25519_public_from_private
                       (Ghost.reveal 'server_private_key_bytes);
                   M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
                   M.body = B.empty;
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
          pts_to server_private_key 'server_private_key_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (B.length (Ghost.reveal 'server_random_bytes) == 32 /\
                 B.length (Ghost.reveal 'server_private_key_bytes) == 32 ==>
                 (let sh = {
                    M.random = Ghost.reveal 'server_random_bytes;
                    M.key_share =
                      CryptoSpec.x25519_public_from_private
                        (Ghost.reveal 'server_private_key_bytes);
                    M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
                    M.body = B.empty;
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
  let mut server_key_share = [| 0uy; 32sz |];
  Crypto.x25519_public_from_private server_private_key server_key_share;
  with server_key_share_bytes. assert (pts_to server_key_share server_key_share_bytes);
  assert (pure (server_key_share_bytes ==
    CryptoSpec.x25519_public_from_private (Ghost.reveal 'server_private_key_bytes)));
  assert (pure (B.length server_key_share_bytes == 32));
  let sh = Ghost.hide {
    M.random = Ghost.reveal 'server_random_bytes;
    M.key_share = server_key_share_bytes;
    M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    M.body = B.empty;
  };
  assert (pure (CM.can_send_server_hello
    'st0
    (Ghost.reveal sh)
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello (Ghost.reveal sh))))));
  let resp =
    process_send_server_hello_from_arrays
      s
      server_random
      server_key_share
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (connection_exactly s st1 **
            pts_to server_random 'server_random_bytes **
            pts_to server_key_share server_key_share_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  assert (pure (st1 ==
    CM.sent_server_hello_state 'st0 (Ghost.reveal sh) network_out_bytes));
  assert (pure (Seq.equal
    network_out_bytes
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello (Ghost.reveal sh))))));
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
                         (M.EncryptedExtensions { M.negotiated_alpn = None; M.body = B.empty });
                   }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (let ee = { M.negotiated_alpn = None; M.body = B.empty } in
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
  let ee : erased M.encrypted_extensions =
    Ghost.hide { M.negotiated_alpn = None; M.body = B.empty };
  assert (pure ((Ghost.reveal ee).M.negotiated_alpn == None));

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
  fold (IM.is_valid_encrypted_extensions lee (Ghost.reveal ee));

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
  let dummy_sh : erased M.server_hello = Ghost.hide {
    M.random = Seq.create 32 0uy;
    M.key_share = Seq.create 32 0uy;
    M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    M.body = B.empty;
  };
  let dummy_cert : erased M.certificate_msg = Ghost.hide { M.chain = []; M.body = B.empty };
  let dummy_cv : erased M.certificate_verify = Ghost.hide {
    M.scheme = T.RsaPssRsaeSha256;
    M.signature = B.empty;
    M.body = B.empty;
  };
  let dummy_fin : erased M.finished = Ghost.hide { M.verify_data = Seq.create 32 0uy };
  W.lemma_fixed_server_handshake_serializers
    (Ghost.reveal dummy_sh)
    (Ghost.reveal dummy_cert)
    (Ghost.reveal dummy_cv)
    (Ghost.reveal dummy_fin);
  assert (pure (Seq.equal
    (W.serialize_empty_encrypted_extensions ())
    (W.serialize_handshake (M.EncryptedExtensions (Ghost.reveal ee)))));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_handshake (M.EncryptedExtensions (Ghost.reveal ee)))));
  lemma_server_handshake_write_seal_some
    'st0
    (CS.application_data_record_header (SZ.v written_fragment + 17))
    (M.TlsHandshake (M.EncryptedExtensions (Ghost.reveal ee)));

  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.record_layer_exactly s.records 'st0.CS.cs_model.CS.model_record);
  let written_raw =
    Ser.serialize_protected_handshake_record
      #(M.EncryptedExtensions (Ghost.reveal ee))
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
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions (Ghost.reveal ee));
    })
    network_out_bytes
    B.empty));
  assert (pure (CS.sent_single_protected_message_seal
    'st0.CS.cs_model
    (M.TlsHandshake (M.EncryptedExtensions (Ghost.reveal ee)))
    network_out_bytes));
  assert (pure (CS.sent_event_seal_projection
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions (Ghost.reveal ee));
    })
    network_out_bytes));
  CSL.lemma_event_raw_delta_legal_protected_segmented
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions (Ghost.reveal ee));
    })
    network_out_bytes
    B.empty;
  assert (pure (CS.event_protected_raw_segmented_success
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions (Ghost.reveal ee));
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
    (Ghost.reveal ee)
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
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes));

  let resp = {
    ST.network_out_len = written_raw;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let ev = Ghost.hide (CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.EncryptedExtensions (Ghost.reveal ee));
  });
  let delta = Ghost.hide {
    CS.delta_event = Ghost.reveal ev;
    CS.delta_raw_sent = network_out_bytes;
    CS.delta_raw_received = B.empty;
  };

  CM.lemma_sent_encrypted_extensions_state_evolves
    'st0
    (Ghost.reveal ee)
    network_out_bytes;
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes);

  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (ST.response_network_out resp network_out_bytes ==
    Seq.slice network_out_bytes 0 (SZ.v written_raw)));
  assert (pure (Seq.equal
    (ST.response_network_out resp network_out_bytes)
    network_out_bytes));
  assert (pure (ST.response_app_out resp 'old_app_out == Seq.slice 'old_app_out 0 0));
  assert (pure (Seq.equal (ST.response_app_out resp 'old_app_out) B.empty));

  assert (pure ((CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)
    resp
    (Ghost.reveal ev)
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)
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
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)
    resp
    ST.LocalSendEncryptedExtensions
    B.empty
    network_out_bytes
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.sent_encrypted_extensions_state 'st0 (Ghost.reveal ee) network_out_bytes)
    resp
    ST.LocalSendEncryptedExtensions
    B.empty
    network_out_bytes
    'old_app_out));
  resp
}

fn build_certificate_from_credentials
  (creds:O.server_credentials)
  requires O.is_server_credentials creds 'certificate_chain 'credential_identity
  returns result: option IM.certificate_msg
  ensures O.is_server_credentials creds 'certificate_chain 'credential_identity **
          (match result with
           | Some lcert ->
             IM.is_valid_certificate_msg
               lcert
               { M.chain = [Ghost.reveal 'certificate_chain]; M.body = B.empty } **
             pure (
               SZ.v lcert.IM.certificate_msg_chain_bytes_len ==
                 B.length (Ghost.reveal 'certificate_chain) /\
               lcert.IM.certificate_msg_cert_count == 1sz)
           | None ->
             pure (
               B.length (Ghost.reveal 'certificate_chain) >
                 IM.max_certificate_chain_bytes))
{
  assert_norm (IM.max_certificate_chain_bytes == 32768);
  let chain_bytes = V.alloc 0uy 32768sz;
  with old_chain_bytes. assert (V.pts_to chain_bytes old_chain_bytes);
  assert (pure (V.is_full_vec chain_bytes));
  assert (pure (V.length chain_bytes == IM.max_certificate_chain_bytes));
  assert (pure (B.length old_chain_bytes == IM.max_certificate_chain_bytes));
  V.to_array_pts_to chain_bytes;
  let copy_result =
    O.copy_server_certificate_chain
      creds
      (V.vec_to_array chain_bytes)
      32768sz;
  match copy_result {
    None -> {
      V.to_vec_pts_to chain_bytes;
      V.free chain_bytes;
      assert (pure (
        B.length (Ghost.reveal 'certificate_chain) >
          IM.max_certificate_chain_bytes));
      None
    }
    Some certificate_len -> {
      V.to_vec_pts_to chain_bytes;
      with copied_chain_bytes. assert (V.pts_to chain_bytes copied_chain_bytes);
      assert (pure (B.length copied_chain_bytes == IM.max_certificate_chain_bytes));
      assert (pure (SZ.v certificate_len ==
        B.length (Ghost.reveal 'certificate_chain)));
      assert (pure (SZ.v certificate_len <= IM.max_certificate_chain_bytes));
      assert (pure (Seq.equal
        (Seq.slice copied_chain_bytes 0 (SZ.v certificate_len))
        (Ghost.reveal 'certificate_chain)));

      assert_norm (IM.max_certificate_chain_entries == 8);
      let cert_offsets = V.alloc 0sz 8sz;
      let cert_lens = V.alloc 0sz 8sz;
      with old_offsets. assert (V.pts_to cert_offsets old_offsets);
      with old_lens. assert (V.pts_to cert_lens old_lens);
      assert (pure (V.is_full_vec cert_offsets));
      assert (pure (V.is_full_vec cert_lens));
      assert (pure (V.length cert_offsets == IM.max_certificate_chain_entries));
      assert (pure (V.length cert_lens == IM.max_certificate_chain_entries));

      V.to_array_pts_to cert_offsets;
      (V.vec_to_array cert_offsets).(0sz) <- 0sz;
      V.to_vec_pts_to cert_offsets;
      V.to_array_pts_to cert_lens;
      (V.vec_to_array cert_lens).(0sz) <- certificate_len;
      V.to_vec_pts_to cert_lens;

      with offsets. assert (V.pts_to cert_offsets offsets);
      with lens. assert (V.pts_to cert_lens lens);
      assert (pure (Seq.length offsets == IM.max_certificate_chain_entries));
      assert (pure (Seq.length lens == IM.max_certificate_chain_entries));
      assert (pure (Seq.index offsets 0 == 0sz));
      assert (pure (Seq.index lens 0 == certificate_len));

      let lcert = {
        IM.certificate_msg_chain_bytes = chain_bytes;
        IM.certificate_msg_chain_bytes_len = certificate_len;
        IM.certificate_msg_cert_offsets = cert_offsets;
        IM.certificate_msg_cert_lens = cert_lens;
        IM.certificate_msg_cert_count = 1sz;
      };
      rewrite (V.pts_to chain_bytes copied_chain_bytes) as
        (V.pts_to lcert.IM.certificate_msg_chain_bytes copied_chain_bytes);
      rewrite (V.pts_to cert_offsets offsets) as
        (V.pts_to lcert.IM.certificate_msg_cert_offsets offsets);
      rewrite (V.pts_to cert_lens lens) as
        (V.pts_to lcert.IM.certificate_msg_cert_lens lens);
      assert (pure (SZ.v lcert.IM.certificate_msg_chain_bytes_len <=
        B.length copied_chain_bytes));
      assert (pure (SZ.v lcert.IM.certificate_msg_cert_count <= Seq.length offsets));
      assert (pure (SZ.v lcert.IM.certificate_msg_cert_count <= Seq.length lens));
      assert (pure (IM.certificate_chain_matches
        copied_chain_bytes
        (SZ.v certificate_len)
        offsets
        lens
        1
        [Ghost.reveal 'certificate_chain]));
      fold (IM.is_valid_certificate_msg
        lcert
        { M.chain = [Ghost.reveal 'certificate_chain]; M.body = B.empty });
      assert (pure (SZ.v lcert.IM.certificate_msg_chain_bytes_len ==
        B.length (Ghost.reveal 'certificate_chain)));
      assert (pure (lcert.IM.certificate_msg_cert_count == 1sz));
      Some lcert
    }
  }
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
                 B.length (Ghost.reveal cert).M.body == 0 /\
                 lcert.IM.certificate_msg_cert_count == 1sz /\
                 (exists (certificate:B.bytes).
                   (Ghost.reveal cert).M.chain == [certificate]) /\
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
      M.body = B.empty;
    }
    (Ghost.reveal cert)
    { M.scheme = T.RsaPssRsaeSha256; M.signature = B.empty; M.body = B.empty }
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
  lemma_server_handshake_write_seal_some
    'st0
    (CS.application_data_record_header (SZ.v written_fragment + 17))
    (M.TlsHandshake (M.Certificate (Ghost.reveal cert)));

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
                         (M.Certificate { M.chain = [Ghost.reveal 'certificate_chain]; M.body = B.empty });
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
                    { M.chain = [Ghost.reveal 'certificate_chain]; M.body = B.empty }
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
  let built = build_certificate_from_credentials creds;
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
      let cert:erased M.certificate_msg =
        Ghost.hide { M.chain = [Ghost.reveal 'certificate_chain]; M.body = B.empty };
      assert (pure (lcert.IM.certificate_msg_cert_count == 1sz));
      assert (pure (exists (certificate:B.bytes).
        (Ghost.reveal cert).M.chain == [certificate]));
      assert (pure ((Ghost.reveal cert).M.chain <> []));
      assert (pure (SZ.v lcert.IM.certificate_msg_chain_bytes_len ==
        B.length (Ghost.reveal 'certificate_chain)));
      W.lemma_serialize_certificate_from_single_chain_len
        (Ghost.reveal 'certificate_chain);
      assert (pure (
        B.length (W.serialize_certificate_from_credential (Ghost.reveal cert)) ==
          13 + B.length (Ghost.reveal 'certificate_chain)));
      assert (pure (
        13 + B.length (Ghost.reveal 'certificate_chain) <=
          Bounds.max_transcript_len));
      assert (pure (
        SZ.fits (SZ.v lcert.IM.certificate_msg_chain_bytes_len + 13)));
      let fragment_len =
        SZ.add lcert.IM.certificate_msg_chain_bytes_len 13sz;
      assert (pure (SZ.v fragment_len ==
        B.length (W.serialize_certificate_from_credential (Ghost.reveal cert))));
      assert (pure (SZ.v fragment_len + 17 <= 16640));
      assert (pure (SZ.v network_out_len == SZ.v fragment_len + 22));
      assert (pure (B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
        SZ.v fragment_len <= Bounds.max_transcript_len));
      assert (pure (
        match 'st0.CS.cs_model.CS.model_config.CS.config_server with
        | Some cfg -> CS.certificate_msg_matches_server_config cfg (Ghost.reveal cert)
        | None -> False));
      process_send_certificate_serialized
        s
        lcert
        #cert
        fragment_len
        network_out
        network_out_len
        app_out
        app_out_len
    }
  }
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
                 B.length (Ghost.reveal cv).M.body == 0 /\
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
      M.body = B.empty;
    }
    { M.chain = []; M.body = B.empty }
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
  lemma_server_handshake_write_seal_some
    'st0
    (CS.application_data_record_header (SZ.v written_fragment + 17))
    (M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv)));
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
                 B.length (Ghost.reveal cv).M.body == 0 /\
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
      M.body = B.empty;
    }
    { M.chain = []; M.body = B.empty }
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
  lemma_server_handshake_write_seal_some
    'st0
    (CS.application_data_record_header (SZ.v written_fragment + 17))
    (M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv)));

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
      M.body = B.empty;
    }
    { M.chain = []; M.body = B.empty }
    { M.scheme = T.RsaPssRsaeSha256; M.signature = B.empty; M.body = B.empty }
    (Ghost.reveal fin);
  assert (pure (Seq.equal
    (W.serialize_server_finished (Ghost.reveal fin))
    (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  assert (pure (Seq.equal
    fragment_bytes
    (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  lemma_server_handshake_write_seal_some
    'st0
    (CS.application_data_record_header (SZ.v written_fragment + 17))
    (M.TlsHandshake (M.Finished (Ghost.reveal fin)));

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
  assert (pure (Ghost.reveal ev == CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
  }));
  assert (pure (ST.legal_response_for_event
    'st0
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)
    resp
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    network_out_bytes
    B.empty
    network_out_bytes
    'old_app_out));
  assert_norm (ST.local_event_kind_matches
    ST.LocalSendServerFinished
    B.empty
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    }));
  assert (pure (ST.local_payload_matches_app_sent_delta
    ST.LocalSendServerFinished
    B.empty
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })));
  assert (pure (ST.local_event_supported_profile
    ST.LocalSendServerFinished
    B.empty
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })));
  assert (pure (CS.sent_event_seal_projection
    'st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
    network_out_bytes));
  assert (pure (resp.status == ST.StepOk));
  assert (pure (ST.legal_local_response
    'st0
    (CM.sent_server_finished_state 'st0 (Ghost.reveal fin) network_out_bytes)
    resp
    ST.LocalSendServerFinished
    B.empty
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })
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
