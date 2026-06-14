module TLS13.Impl.Server.Send

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CM = TLS13.Impl.ConnectionState.Model
module CLH = TLS13.Impl.ConnectionState.LocalHandshake
module CR = TLS13.Impl.ConnectionState.Repr
module IM = TLS13.Impl.Messages
module M = TLS13.Messages
module O = TLS13.OpenSSL
module R = TLS13.Record.Spec
module Ser = TLS13.Impl.Serializer
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec

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
  let sh = Ghost.hide {
    M.random = Ghost.reveal 'server_random_bytes;
    M.key_share = Ghost.reveal 'server_key_share_bytes;
    M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
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

fn build_certificate_from_credentials
  (creds:O.server_credentials)
  requires O.is_server_credentials creds 'certificate_chain 'credential_identity
  returns result: option IM.certificate_msg
  ensures O.is_server_credentials creds 'certificate_chain 'credential_identity **
          (match result with
           | Some lcert ->
             IM.is_valid_certificate_msg
               lcert
               { M.chain = [Ghost.reveal 'certificate_chain] } **
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
        { M.chain = [Ghost.reveal 'certificate_chain] });
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
        Ghost.hide { M.chain = [Ghost.reveal 'certificate_chain] };
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
