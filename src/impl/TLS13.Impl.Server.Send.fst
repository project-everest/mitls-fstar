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
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
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
