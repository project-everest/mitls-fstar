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
module Ser = TLS13.Impl.Serializer
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
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
