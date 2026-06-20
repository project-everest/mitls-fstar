module TLS13.Impl.Server.Network

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module Arr = Pulse.Lib.Array
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

let lemma_client_hello_sni_len_for
  (storage:B.bytes)
  (len:SZ.t)
  (ch:M.client_hello)
  : Lemma
      (requires IM.optional_byte_prefix_matches true storage len ch.M.server_name /\
                B.length storage < 65536)
      (ensures CM.client_hello_server_name_len_for ch == len)
=
  match ch.M.server_name with
  | Some sn ->
    assert (IM.byte_prefix_matches storage len sn);
    assert (Seq.equal sn (Seq.slice storage 0 (SZ.v len)));
    Seq.lemma_len_slice storage 0 (SZ.v len);
    assert (B.length sn == SZ.v len);
    assert (B.length sn < 65536);
    CM.lemma_bounded_u16_sizet_of_sizet (B.length sn) len;
    assert (CM.client_hello_server_name_len_for ch == len)
  | None ->
    assert False

inline_for_extraction
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
              st1 ==
                CM.received_client_hello_state
                  'st0
                  (Ghost.reveal ch)
                  (Ghost.reveal 'raw_bytes) /\
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

inline_for_extraction
fn process_client_finished
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (lfin:IM.finished)
  (#fin:erased M.finished)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           IM.is_valid_finished lfin fin **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CM.can_receive_client_finished
                   'st0
                   (Ghost.reveal fin)
                   (Ghost.reveal 'raw_bytes) /\
                 CS.received_event_nonempty_decode_projection
                   'st0.CS.cs_model
                   (ST.received_message_event
                     (M.TlsHandshake (M.Finished (Ghost.reveal fin))))
                   (Ghost.reveal 'raw_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.received_client_finished_state
                    'st0
                    (Ghost.reveal fin)
                    (Ghost.reveal 'raw_bytes) /\
                ST.server_network_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  (M.TlsHandshake (M.Finished (Ghost.reveal fin)))
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CN.mark_received_client_finished
    s
    raw
    lfin
    #fin;
  fold (connection_exactly
    s
    (CM.received_client_finished_state
      'st0
      (Ghost.reveal fin)
      (Ghost.reveal 'raw_bytes)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  CM.lemma_received_client_finished_state_evolves
    'st0
    (Ghost.reveal fin)
    (Ghost.reveal 'raw_bytes);
  assert (pure (CS.legal_connection_delta
    'st0
    (ST.received_message_delta
      (M.TlsHandshake (M.Finished (Ghost.reveal fin)))
      (Ghost.reveal 'raw_bytes))
    (CM.received_client_finished_state
      'st0
      (Ghost.reveal fin)
      (Ghost.reveal 'raw_bytes))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (ST.received_message_delta
      (M.TlsHandshake (M.Finished (Ghost.reveal fin)))
      (Ghost.reveal 'raw_bytes))
    (CM.received_client_finished_state
      'st0
      (Ghost.reveal fin)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsHandshake (M.Finished (Ghost.reveal fin)))
      (Ghost.reveal 'raw_bytes))
    (CM.received_client_finished_state
      'st0
      (Ghost.reveal fin)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.received_client_finished_state
      'st0
      (Ghost.reveal fin)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsHandshake (M.Finished (Ghost.reveal fin)))
      (Ghost.reveal 'raw_bytes))
    (CM.received_client_finished_state
      'st0
      (Ghost.reveal fin)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsHandshake (M.Finished (Ghost.reveal fin)))
      (Ghost.reveal 'raw_bytes))
    (CM.received_client_finished_state
      'st0
      (Ghost.reveal fin)
      (Ghost.reveal 'raw_bytes));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.received_client_finished_state 'st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.received_client_finished_state 'st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.received_client_finished_state 'st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.received_client_finished_state 'st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.received_client_finished_state 'st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.received_client_finished_state 'st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.received_client_finished_state 'st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes))
    resp
    (ST.received_message_event (M.TlsHandshake (M.Finished (Ghost.reveal fin))))
    B.empty
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_network_response
    'st0
    (CM.received_client_finished_state 'st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes))
    resp
    (M.TlsHandshake (M.Finished (Ghost.reveal fin)))
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_network_event_end_to_end_correct
    'st0
    (CM.received_client_finished_state 'st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes))
    resp
    (M.TlsHandshake (M.Finished (Ghost.reveal fin)))
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  resp
}

inline_for_extraction
fn process_application_data
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (lapp:IM.application_data)
  (#app_payload:erased B.bytes)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           IM.is_valid_application_data lapp app_payload **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                 CS.application_traffic_available_for_role
                   CS.ServerEndpoint
                   'st0.CS.cs_model.CS.model_handshake
                   CL.Received /\
                 U64.fits ('st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 CT.received_tls_raw_delta_legal
                   'st0
                   (M.TlsApplicationData (Ghost.reveal app_payload))
                   (Ghost.reveal 'raw_bytes) /\
                 CS.received_event_nonempty_decode_projection
                   'st0.CS.cs_model
                   (ST.received_message_event
                     (M.TlsApplicationData (Ghost.reveal app_payload)))
                   (Ghost.reveal 'raw_bytes) /\
                 SZ.v lapp.IM.application_data_len <= SZ.v app_out_len)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.received_application_data_state
                    'st0
                    (Ghost.reveal app_payload)
                    (Ghost.reveal 'raw_bytes) /\
                ST.server_network_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  (M.TlsApplicationData (Ghost.reveal app_payload))
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  unfold (IM.is_valid_application_data lapp app_payload);
  with app_storage. _;
  let data_len = lapp.IM.application_data_len;
  V.pts_to_len lapp.IM.application_data_bytes;
  assert (pure (B.length app_storage == IM.max_record_fragment_len));
  assert (pure (SZ.v data_len <= B.length app_storage));
  assert (pure (SZ.v data_len <= SZ.v app_out_len));

  V.to_array_pts_to lapp.IM.application_data_bytes;
  pts_to_len (V.vec_to_array lapp.IM.application_data_bytes);
  pts_to_len app_out;
  Arr.memcpy_l data_len (V.vec_to_array lapp.IM.application_data_bytes) app_out;
  V.to_vec_pts_to lapp.IM.application_data_bytes;
  with app_out_bytes. assert (pts_to app_out app_out_bytes);
  pts_to_len app_out;
  assert (pure (B.length app_out_bytes == SZ.v app_out_len));
  assert (pure (Seq.equal
    (Ghost.reveal app_payload)
    (Seq.slice app_storage 0 (SZ.v data_len))));
  assert (pure (Seq.equal
    (Seq.slice app_out_bytes 0 (SZ.v data_len))
    (Seq.slice app_storage 0 (SZ.v data_len))));
  assert (pure (Seq.equal
    (Ghost.reveal app_payload)
    (Seq.slice app_out_bytes 0 (SZ.v data_len))));

  V.free lapp.IM.application_data_bytes;
  unfold (connection_exactly s 'st0);
  CN.mark_received_application_data_for_role
    s
    raw
    #CS.ServerEndpoint
    #app_payload;
  fold (connection_exactly
    s
    (CM.received_application_data_state
      'st0
      (Ghost.reveal app_payload)
      (Ghost.reveal 'raw_bytes)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = data_len;
    ST.status = ST.StepOk;
  };

  CM.lemma_received_application_data_state_evolves_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal app_payload)
    (Ghost.reveal 'raw_bytes);
  assert (pure (CS.legal_connection_delta
    'st0
    (ST.received_message_delta
      (M.TlsApplicationData (Ghost.reveal app_payload))
      (Ghost.reveal 'raw_bytes))
    (CM.received_application_data_state
      'st0
      (Ghost.reveal app_payload)
      (Ghost.reveal 'raw_bytes))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (ST.received_message_delta
      (M.TlsApplicationData (Ghost.reveal app_payload))
      (Ghost.reveal 'raw_bytes))
    (CM.received_application_data_state
      'st0
      (Ghost.reveal app_payload)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsApplicationData (Ghost.reveal app_payload))
      (Ghost.reveal 'raw_bytes))
    (CM.received_application_data_state
      'st0
      (Ghost.reveal app_payload)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.received_application_data_state
      'st0
      (Ghost.reveal app_payload)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsApplicationData (Ghost.reveal app_payload))
      (Ghost.reveal 'raw_bytes))
    (CM.received_application_data_state
      'st0
      (Ghost.reveal app_payload)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsApplicationData (Ghost.reveal app_payload))
      (Ghost.reveal 'raw_bytes))
    (CM.received_application_data_state
      'st0
      (Ghost.reveal app_payload)
      (Ghost.reveal 'raw_bytes));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  assert (pure (Seq.equal B.empty (ST.response_network_out resp 'old_network_out)));
  assert (pure (ST.response_app_out resp app_out_bytes ==
    Seq.slice app_out_bytes 0 (SZ.v data_len)));
  assert (pure (Seq.equal
    (Ghost.reveal app_payload)
    (ST.response_app_out resp app_out_bytes)));

  assert (pure ((CM.received_application_data_state 'st0 (Ghost.reveal app_payload) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.received_application_data_state 'st0 (Ghost.reveal app_payload) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.received_application_data_state 'st0 (Ghost.reveal app_payload) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.received_application_data_state 'st0 (Ghost.reveal app_payload) (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.received_application_data_state 'st0 (Ghost.reveal app_payload) (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.received_application_data_state 'st0 (Ghost.reveal app_payload) (Ghost.reveal 'raw_bytes))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.received_application_data_state 'st0 (Ghost.reveal app_payload) (Ghost.reveal 'raw_bytes))
    resp
    (ST.received_message_event (M.TlsApplicationData (Ghost.reveal app_payload)))
    B.empty
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    app_out_bytes));
  assert (pure (ST.legal_network_response
    'st0
    (CM.received_application_data_state 'st0 (Ghost.reveal app_payload) (Ghost.reveal 'raw_bytes))
    resp
    (M.TlsApplicationData (Ghost.reveal app_payload))
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    app_out_bytes));
  assert (pure (ST.server_network_event_end_to_end_correct
    'st0
    (CM.received_application_data_state 'st0 (Ghost.reveal app_payload) (Ghost.reveal 'raw_bytes))
    resp
    (M.TlsApplicationData (Ghost.reveal app_payload))
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    app_out_bytes));
  resp
}

inline_for_extraction
fn process_close_notify
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 ('st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
                  'st0.CS.cs_model.CS.model_control == CS.ControlClosing) /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                 U64.fits ('st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 CT.received_tls_raw_delta_legal
                   'st0
                   (M.TlsAlert T.CloseNotify)
                   (Ghost.reveal 'raw_bytes) /\
                 CS.received_event_nonempty_decode_projection
                   'st0.CS.cs_model
                   (ST.received_message_event
                     (M.TlsAlert T.CloseNotify))
                   (Ghost.reveal 'raw_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.received_close_notify_state
                    'st0
                    (Ghost.reveal 'raw_bytes) /\
                ST.server_network_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  (M.TlsAlert T.CloseNotify)
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CN.mark_received_close_notify_for_role
    s
    raw
    #CS.ServerEndpoint;
  fold (connection_exactly
    s
    (CM.received_close_notify_state
      'st0
      (Ghost.reveal 'raw_bytes)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  CM.lemma_received_close_notify_state_evolves_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal 'raw_bytes);
  assert (pure (CS.legal_connection_delta
    'st0
    (ST.received_message_delta
      (M.TlsAlert T.CloseNotify)
      (Ghost.reveal 'raw_bytes))
    (CM.received_close_notify_state
      'st0
      (Ghost.reveal 'raw_bytes))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (ST.received_message_delta
      (M.TlsAlert T.CloseNotify)
      (Ghost.reveal 'raw_bytes))
    (CM.received_close_notify_state
      'st0
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsAlert T.CloseNotify)
      (Ghost.reveal 'raw_bytes))
    (CM.received_close_notify_state
      'st0
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.received_close_notify_state
      'st0
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsAlert T.CloseNotify)
      (Ghost.reveal 'raw_bytes))
    (CM.received_close_notify_state
      'st0
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsAlert T.CloseNotify)
      (Ghost.reveal 'raw_bytes))
    (CM.received_close_notify_state
      'st0
      (Ghost.reveal 'raw_bytes));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (Seq.equal B.empty (ST.response_network_out resp 'old_network_out)));
  assert (pure (Seq.equal B.empty (ST.response_app_out resp 'old_app_out)));

  assert (pure ((CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes))
    resp
    (ST.received_message_event (M.TlsAlert T.CloseNotify))
    B.empty
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_network_response
    'st0
    (CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes))
    resp
    (M.TlsAlert T.CloseNotify)
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_network_event_end_to_end_correct
    'st0
    (CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes))
    resp
    (M.TlsAlert T.CloseNotify)
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  resp
}

inline_for_extraction
fn process_alert_failure
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (alert_wire:U8.t)
  (#alert:erased T.alert_description)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 Ghost.reveal alert <> T.CloseNotify /\
                 Tags.alert_tag_matches alert_wire (Ghost.reveal alert) /\
                 CT.received_tls_raw_delta_legal
                   'st0
                   (M.TlsAlert (Ghost.reveal alert))
                   (Ghost.reveal 'raw_bytes) /\
                 CS.received_event_nonempty_decode_projection
                   'st0.CS.cs_model
                   (ST.received_message_event
                     (M.TlsAlert (Ghost.reveal alert)))
                   (Ghost.reveal 'raw_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.received_alert_failure_state
                    'st0
                    (Ghost.reveal alert)
                    (Ghost.reveal 'raw_bytes) /\
                resp.ST.status == ST.ConnectionFailed /\
                ST.server_network_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  (M.TlsAlert (Ghost.reveal alert))
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CN.mark_received_alert_failure
    s
    raw
    alert_wire
    #alert;
  fold (connection_exactly
    s
    (CM.received_alert_failure_state
      'st0
      (Ghost.reveal alert)
      (Ghost.reveal 'raw_bytes)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.ConnectionFailed;
  };

  CM.lemma_received_alert_failure_state_evolves
    'st0
    (Ghost.reveal alert)
    (Ghost.reveal 'raw_bytes);
  assert (pure (CS.legal_connection_delta
    'st0
    (ST.received_message_delta
      (M.TlsAlert (Ghost.reveal alert))
      (Ghost.reveal 'raw_bytes))
    (CM.received_alert_failure_state
      'st0
      (Ghost.reveal alert)
      (Ghost.reveal 'raw_bytes))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (ST.received_message_delta
      (M.TlsAlert (Ghost.reveal alert))
      (Ghost.reveal 'raw_bytes))
    (CM.received_alert_failure_state
      'st0
      (Ghost.reveal alert)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsAlert (Ghost.reveal alert))
      (Ghost.reveal 'raw_bytes))
    (CM.received_alert_failure_state
      'st0
      (Ghost.reveal alert)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.received_alert_failure_state
      'st0
      (Ghost.reveal alert)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsAlert (Ghost.reveal alert))
      (Ghost.reveal 'raw_bytes))
    (CM.received_alert_failure_state
      'st0
      (Ghost.reveal alert)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsAlert (Ghost.reveal alert))
      (Ghost.reveal 'raw_bytes))
    (CM.received_alert_failure_state
      'st0
      (Ghost.reveal alert)
      (Ghost.reveal 'raw_bytes));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (Seq.equal B.empty (ST.response_network_out resp 'old_network_out)));
  assert (pure (Seq.equal B.empty (ST.response_app_out resp 'old_app_out)));

  assert (pure ((CM.received_alert_failure_state 'st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.received_alert_failure_state 'st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.received_alert_failure_state 'st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.received_alert_failure_state 'st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.received_alert_failure_state 'st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.received_alert_failure_state 'st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.received_alert_failure_state 'st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes))
    resp
    (ST.received_message_event (M.TlsAlert (Ghost.reveal alert)))
    B.empty
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_network_response
    'st0
    (CM.received_alert_failure_state 'st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes))
    resp
    (M.TlsAlert (Ghost.reveal alert))
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_network_event_end_to_end_correct
    'st0
    (CM.received_alert_failure_state 'st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes))
    resp
    (M.TlsAlert (Ghost.reveal alert))
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  resp
}

inline_for_extraction
fn process_change_cipher_spec
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 (exists stage.
                   'st0.CS.cs_model.CS.model_control == CS.ControlHandshaking stage) /\
                 CT.received_tls_raw_delta_legal
                   'st0
                   M.TlsChangeCipherSpec
                   (Ghost.reveal 'raw_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.received_change_cipher_spec_state
                    'st0
                    (Ghost.reveal 'raw_bytes) /\
                ST.server_network_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  M.TlsChangeCipherSpec
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CN.mark_received_change_cipher_spec s raw;
  fold (connection_exactly
    s
    (CM.received_change_cipher_spec_state
      'st0
      (Ghost.reveal 'raw_bytes)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  CM.lemma_received_change_cipher_spec_state_evolves
    'st0
    (Ghost.reveal 'raw_bytes);
  assert (pure (CS.legal_connection_delta
    'st0
    (ST.received_message_delta
      M.TlsChangeCipherSpec
      (Ghost.reveal 'raw_bytes))
    (CM.received_change_cipher_spec_state
      'st0
      (Ghost.reveal 'raw_bytes))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (ST.received_message_delta
      M.TlsChangeCipherSpec
      (Ghost.reveal 'raw_bytes))
    (CM.received_change_cipher_spec_state
      'st0
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (ST.received_message_delta
      M.TlsChangeCipherSpec
      (Ghost.reveal 'raw_bytes))
    (CM.received_change_cipher_spec_state
      'st0
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.received_change_cipher_spec_state
      'st0
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (ST.received_message_delta
      M.TlsChangeCipherSpec
      (Ghost.reveal 'raw_bytes))
    (CM.received_change_cipher_spec_state
      'st0
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (ST.received_message_delta
      M.TlsChangeCipherSpec
      (Ghost.reveal 'raw_bytes))
    (CM.received_change_cipher_spec_state
      'st0
      (Ghost.reveal 'raw_bytes));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (Seq.equal B.empty (ST.response_network_out resp 'old_network_out)));
  assert (pure (Seq.equal B.empty (ST.response_app_out resp 'old_app_out)));

  assert (pure ((CM.received_change_cipher_spec_state 'st0 (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.received_change_cipher_spec_state 'st0 (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.received_change_cipher_spec_state 'st0 (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.received_change_cipher_spec_state 'st0 (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.received_change_cipher_spec_state 'st0 (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.received_change_cipher_spec_state 'st0 (Ghost.reveal 'raw_bytes))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.received_change_cipher_spec_state 'st0 (Ghost.reveal 'raw_bytes))
    resp
    (ST.received_message_event M.TlsChangeCipherSpec)
    B.empty
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_network_response
    'st0
    (CM.received_change_cipher_spec_state 'st0 (Ghost.reveal 'raw_bytes))
    resp
    M.TlsChangeCipherSpec
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_network_event_end_to_end_correct
    'st0
    (CM.received_change_cipher_spec_state 'st0 (Ghost.reveal 'raw_bytes))
    resp
    M.TlsChangeCipherSpec
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  resp
}

inline_for_extraction
fn process_decode_error
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 == CM.local_fail_state 'st0 CM.tls_decode_error /\
                ST.server_end_to_end_invariant st1 /\
                ST.decode_error_response
                  'st0
                  st1
                  resp
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CF.mark_decode_error s;
  fold (connection_exactly s (CM.local_fail_state 'st0 CM.tls_decode_error));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.DecodeError;
  };

  CM.lemma_local_fail_state_evolves
    'st0
    CM.tls_decode_error;
  assert (pure (CS.legal_connection_delta
    'st0
    {
      CS.delta_event = CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error);
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    }
    (CM.local_fail_state 'st0 CM.tls_decode_error)));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    {
      CS.delta_event = CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error);
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    }
    (CM.local_fail_state 'st0 CM.tls_decode_error);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    {
      CS.delta_event = CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error);
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    }
    (CM.local_fail_state 'st0 CM.tls_decode_error);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.local_fail_state 'st0 CM.tls_decode_error);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    {
      CS.delta_event = CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error);
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    }
    (CM.local_fail_state 'st0 CM.tls_decode_error);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    {
      CS.delta_event = CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error);
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    }
    (CM.local_fail_state 'st0 CM.tls_decode_error);

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (Seq.equal B.empty (ST.response_network_out resp 'old_network_out)));
  assert (pure (Seq.equal B.empty (ST.response_app_out resp 'old_app_out)));

  assert (pure ((CM.local_fail_state 'st0 CM.tls_decode_error).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.local_fail_state 'st0 CM.tls_decode_error).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.local_fail_state 'st0 CM.tls_decode_error).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.local_fail_state 'st0 CM.tls_decode_error)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.local_fail_state 'st0 CM.tls_decode_error)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.local_fail_state 'st0 CM.tls_decode_error)));

  assert (pure (ST.decode_error_response
    'st0
    (CM.local_fail_state 'st0 CM.tls_decode_error)
    resp
    'old_network_out
    'old_app_out));
  resp
}

fn process_network_bytes
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0)
  returns buffer_resp:ST.server_buffer_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_network_bytes_end_to_end_correct
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes /\
                ST.server_network_consumed_input_projection
                   'st0
                   st1
                   buffer_resp
                   (Ghost.reveal 'raw_bytes)
                   network_out_bytes
                   app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  let decoded = P.decode_network_buffer s raw raw_len;
  fold (connection_exactly s 'st0);
  match decoded {
    IM.NetworkBufferNeedMoreInput -> {
      let resp = {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.NeedMoreInput;
      };
      let buffer_resp = {
        ST.response = resp;
        ST.consumed_len = 0sz;
      };
      assert (pure (ST.server_network_bytes_end_to_end_correct
        'st0
        'st0
        buffer_resp
        (Ghost.reveal 'raw_bytes)
        'old_network_out
        'old_app_out));
      assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
        buffer_resp.ST.consumed_len == 0sz));
      buffer_resp
    }
    IM.NetworkBufferDecodeError -> {
      let resp =
        process_decode_error
          s
          raw
          raw_len
          network_out
          network_out_len
          app_out
          app_out_len;
      let buffer_resp = {
        ST.response = resp;
        ST.consumed_len = 0sz;
      };
      with st1 network_out_bytes app_out_bytes.
        assert (connection_exactly s st1 **
                pts_to raw 'raw_bytes **
                pts_to network_out network_out_bytes **
                pts_to app_out app_out_bytes);
      assert (pure (st1 == CM.local_fail_state 'st0 CM.tls_decode_error));
      assert (pure (ST.decode_error_response
        'st0
        st1
        resp
        network_out_bytes
        app_out_bytes));
      assert (pure (ST.server_network_bytes_end_to_end_correct
        'st0
        st1
        buffer_resp
        (Ghost.reveal 'raw_bytes)
        network_out_bytes
        app_out_bytes));
      assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
        buffer_resp.ST.consumed_len == 0sz));
      assert (pure (ST.server_network_consumed_input_projection
        'st0
        st1
        buffer_resp
        (Ghost.reveal 'raw_bytes)
        network_out_bytes
        app_out_bytes));
      buffer_resp
    }
    IM.NetworkBufferOk decoded_buffer -> {
      with raw_record_bytes fragment_bytes.
        assert (V.pts_to decoded_buffer.IM.decoded_buffer_raw_record raw_record_bytes **
                V.pts_to decoded_buffer.IM.decoded_buffer_fragment fragment_bytes);
      V.to_array_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
      V.to_array_pts_to decoded_buffer.IM.decoded_buffer_fragment;
      match decoded_buffer.IM.decoded_buffer_parsed {
        None -> {
          let resp =
            process_decode_error
              s
              (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record)
              decoded_buffer.IM.decoded_buffer_raw_record_len
              network_out
              network_out_len
              app_out
              app_out_len;
          let buffer_resp = {
            ST.response = resp;
            ST.consumed_len = decoded_buffer.IM.decoded_buffer_consumed_len;
          };
          with st1 network_out_bytes app_out_bytes.
            assert (connection_exactly s st1 **
                    pts_to (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record) raw_record_bytes **
                    pts_to network_out network_out_bytes **
                    pts_to app_out app_out_bytes);
          assert (pure (st1 == CM.local_fail_state 'st0 CM.tls_decode_error));
          assert (pure (ST.decode_error_response
            'st0
            st1
            resp
            network_out_bytes
            app_out_bytes));
          assert (pure (SZ.v decoded_buffer.IM.decoded_buffer_consumed_len <=
            B.length (Ghost.reveal 'raw_bytes)));
          assert (pure (ST.server_network_bytes_end_to_end_correct
            'st0
            st1
            buffer_resp
            (Ghost.reveal 'raw_bytes)
            network_out_bytes
            app_out_bytes));
          assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
            buffer_resp.ST.consumed_len == 0sz));
          assert (pure (ST.server_network_consumed_input_projection
            'st0
            st1
            buffer_resp
            (Ghost.reveal 'raw_bytes)
            network_out_bytes
            app_out_bytes));
          V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
          V.free decoded_buffer.IM.decoded_buffer_fragment;
          V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
          V.free decoded_buffer.IM.decoded_buffer_raw_record;
          buffer_resp
        }
        Some l -> {
          match l {
            IM.LTlsHandshake lhs -> {
              with m. assert (pure True);
              unfold (IM.is_valid_tls_message (IM.LTlsHandshake lhs) m);
              with mhs. _;
              assert (pure (m == M.TlsHandshake mhs));
              match lhs {
                IM.LClientHello lch -> {
              unfold (IM.is_valid_handshake_msg (IM.LClientHello lch) mhs);
              with ch. _;
              assert (pure (mhs == M.ClientHello ch));
              assert (pure (m == M.TlsHandshake (M.ClientHello ch)));
              assert (pure (CT.parsed_message_wire_success_for
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (IM.LTlsHandshake (IM.LClientHello lch))
                (M.TlsHandshake (M.ClientHello ch))));
              assert (pure (CT.wire_parse_success
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (M.TlsHandshake (M.ClientHello ch))));
              assert (pure (CT.received_tls_raw_delta_legal
                'st0
                (M.TlsHandshake (M.ClientHello ch))
                raw_record_bytes));
              unfold (IM.is_valid_client_hello lch ch);
              with random server_name key_share cipher_suites signature_schemes. _;
              CM.lemma_cipher_suites_match_length
                cipher_suites
                (SZ.v lch.IM.client_hello_cipher_suites_len)
                ch.M.cipher_suites;
              assert (pure (List.length ch.M.cipher_suites ==
                SZ.v lch.IM.client_hello_cipher_suites_len));
              assert (pure (List.length ch.M.cipher_suites < 65536));
              CM.lemma_bounded_u16_sizet_of_sizet
                (List.length ch.M.cipher_suites)
                lch.IM.client_hello_cipher_suites_len;
              assert (pure (CM.client_hello_cipher_suites_len_for ch ==
                lch.IM.client_hello_cipher_suites_len));
              CM.lemma_signature_schemes_match_length
                signature_schemes
                (SZ.v lch.IM.client_hello_signature_schemes_len)
                ch.M.signature_schemes;
              assert (pure (List.length ch.M.signature_schemes ==
                SZ.v lch.IM.client_hello_signature_schemes_len));
              assert (pure (List.length ch.M.signature_schemes < 65536));
              CM.lemma_bounded_u16_sizet_of_sizet
                (List.length ch.M.signature_schemes)
                lch.IM.client_hello_signature_schemes_len;
              assert (pure (CM.client_hello_signature_schemes_len_for ch ==
                lch.IM.client_hello_signature_schemes_len));
              let has_sni = lch.IM.client_hello_has_server_name;
              if has_sni {
                assert (pure (lch.IM.client_hello_has_server_name == true));
                assert (pure (IM.optional_byte_prefix_matches
                    true
                    server_name
                    lch.IM.client_hello_server_name_len
                    ch.M.server_name));
                assert (pure (B.length server_name == IM.max_server_name_len));
                assert (pure (B.length server_name < 65536));
                lemma_client_hello_sni_len_for
                    server_name
                    lch.IM.client_hello_server_name_len
                    ch;
                assert (pure (SZ.fits Bounds.max_client_hello_len));
                let max_client_hello_len_sz =
                  SZ.uint_to_t Bounds.max_client_hello_len;
                let fragment_fits =
                  CM.sizet_lte_plain
                    decoded_buffer.IM.decoded_buffer_fragment_len
                    max_client_hello_len_sz;
                CM.lemma_sizet_lte_plain
                  decoded_buffer.IM.decoded_buffer_fragment_len
                  max_client_hello_len_sz;
                fold (IM.is_valid_client_hello lch ch);
                if fragment_fits {
                  assert (pure (SZ.v decoded_buffer.IM.decoded_buffer_fragment_len <=
                    Bounds.max_client_hello_len));
                  unfold (connection_exactly s 'st0);
                  let ready =
                    CQ.can_receive_client_hello
                      s
                      decoded_buffer.IM.decoded_buffer_fragment_len
                      #ch
                      #'st0;
                  fold (connection_exactly s 'st0);
                  if ready {
                    let resp =
                      process_client_hello
                        s
                        (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record)
                        decoded_buffer.IM.decoded_buffer_raw_record_len
                        (V.vec_to_array decoded_buffer.IM.decoded_buffer_fragment)
                        decoded_buffer.IM.decoded_buffer_fragment_len
                        lch
                        #ch
                        network_out
                        network_out_len
                        app_out
                        app_out_len;
                    let buffer_resp = {
                      ST.response = resp;
                      ST.consumed_len = decoded_buffer.IM.decoded_buffer_consumed_len;
                    };
                    with st1 network_out_bytes app_out_bytes.
                      assert (connection_exactly s st1 **
                              pts_to (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record) raw_record_bytes **
                              pts_to (V.vec_to_array decoded_buffer.IM.decoded_buffer_fragment) fragment_bytes **
                              pts_to network_out network_out_bytes **
                              pts_to app_out app_out_bytes);
                    assert (pure (SZ.v decoded_buffer.IM.decoded_buffer_consumed_len <=
                      B.length (Ghost.reveal 'raw_bytes)));
                    assert (pure (ST.server_network_bytes_end_to_end_correct
                      'st0
                      st1
                      buffer_resp
                      (Ghost.reveal 'raw_bytes)
                      network_out_bytes
                      app_out_bytes));
                    assert (pure (st1 ==
                      CM.received_client_hello_state
                        'st0
                        ch
                        raw_record_bytes));
                    assert (pure (Seq.equal
                      raw_record_bytes
                      (Seq.slice
                        (Ghost.reveal 'raw_bytes)
                        0
                        (SZ.v buffer_resp.ST.consumed_len))));
                    assert (pure (Seq.equal
                      raw_record_bytes
                      (ST.server_network_consumed_prefix
                        buffer_resp
                        (Ghost.reveal 'raw_bytes))));
                    assert (pure (ST.server_decoded_message_event_projection
                      'st0
                      st1
                      resp
                      (M.TlsHandshake (M.ClientHello ch))
                      raw_record_bytes
                      network_out_bytes
                      app_out_bytes));
                    assert (pure (ST.server_network_step_ok_received_decode_projection
                      'st0
                      st1
                      buffer_resp
                      (Ghost.reveal 'raw_bytes)
                      network_out_bytes
                      app_out_bytes));
                    assert (pure (buffer_resp.ST.response.ST.status == ST.StepOk ==>
                      (exists ch raw_received.
                        st1 ==
                          CM.received_client_hello_state
                            'st0
                            ch
                            raw_received /\
                        Seq.equal
                          raw_received
                          (Seq.slice
                            (Ghost.reveal 'raw_bytes)
                            0
                            (SZ.v buffer_resp.ST.consumed_len))) \/
                      (exists fin raw_received.
                        st1 ==
                          CM.received_client_finished_state
                            'st0
                            fin
                            raw_received /\
                        Seq.equal
                          raw_received
                          (Seq.slice
                            (Ghost.reveal 'raw_bytes)
                            0
                            (SZ.v buffer_resp.ST.consumed_len)))));
                    assert (pure (ST.server_network_step_ok_consumed_prefix
                      'st0
                      st1
                      buffer_resp
                      (Ghost.reveal 'raw_bytes)));
                    assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                      buffer_resp.ST.consumed_len == 0sz));
                    assert (pure (ST.server_network_consumed_input_projection
                      'st0
                      st1
                      buffer_resp
                      (Ghost.reveal 'raw_bytes)
                      network_out_bytes
                      app_out_bytes));
                    V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
                    V.free decoded_buffer.IM.decoded_buffer_fragment;
                    V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
                    V.free decoded_buffer.IM.decoded_buffer_raw_record;
                    buffer_resp
                  } else {
                    IM.free_client_hello lch;
                    V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
                    V.free decoded_buffer.IM.decoded_buffer_fragment;
                    V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
                    V.free decoded_buffer.IM.decoded_buffer_raw_record;
                    let resp = {
                      ST.network_out_len = 0sz;
                      ST.app_out_len = 0sz;
                      ST.status = ST.IllegalTransition;
                    };
                    let buffer_resp = {
                      ST.response = resp;
                      ST.consumed_len = 0sz;
                    };
                    assert (pure (ST.server_network_bytes_end_to_end_correct
                      'st0
                      'st0
                      buffer_resp
                      (Ghost.reveal 'raw_bytes)
                      'old_network_out
                      'old_app_out));
                    assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                      buffer_resp.ST.consumed_len == 0sz));
                    buffer_resp
                  }
                } else {
                  IM.free_client_hello lch;
                  V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
                  V.free decoded_buffer.IM.decoded_buffer_fragment;
                  V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
                  V.free decoded_buffer.IM.decoded_buffer_raw_record;
                  let resp = {
                    ST.network_out_len = 0sz;
                    ST.app_out_len = 0sz;
                    ST.status = ST.IllegalTransition;
                  };
                  let buffer_resp = {
                    ST.response = resp;
                    ST.consumed_len = 0sz;
                  };
                  assert (pure (ST.server_network_bytes_end_to_end_correct
                    'st0
                    'st0
                    buffer_resp
                    (Ghost.reveal 'raw_bytes)
                    'old_network_out
                    'old_app_out));
                  assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                    buffer_resp.ST.consumed_len == 0sz));
                  buffer_resp
                }
              } else {
                fold (IM.is_valid_client_hello lch ch);
                IM.free_client_hello lch;
                V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
                V.free decoded_buffer.IM.decoded_buffer_fragment;
                V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
                V.free decoded_buffer.IM.decoded_buffer_raw_record;
                let resp = {
                  ST.network_out_len = 0sz;
                  ST.app_out_len = 0sz;
                  ST.status = ST.IllegalTransition;
                };
                let buffer_resp = {
                  ST.response = resp;
                  ST.consumed_len = 0sz;
                };
                assert (pure (ST.server_network_bytes_end_to_end_correct
                  'st0
                  'st0
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  'old_network_out
                  'old_app_out));
                assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                  buffer_resp.ST.consumed_len == 0sz));
                buffer_resp
              }
            }
            IM.LServerHello lsh -> {
              IM.free_handshake_msg (IM.LServerHello lsh);
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
              V.free decoded_buffer.IM.decoded_buffer_fragment;
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
              V.free decoded_buffer.IM.decoded_buffer_raw_record;
              let resp = {
                ST.network_out_len = 0sz;
                ST.app_out_len = 0sz;
                ST.status = ST.IllegalTransition;
              };
              let buffer_resp = {
                ST.response = resp;
                ST.consumed_len = 0sz;
              };
              assert (pure (ST.server_network_bytes_end_to_end_correct
                'st0
                'st0
                buffer_resp
                (Ghost.reveal 'raw_bytes)
                'old_network_out
                'old_app_out));
              assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                buffer_resp.ST.consumed_len == 0sz));
              buffer_resp
            }
            IM.LEncryptedExtensions lee -> {
              IM.free_handshake_msg (IM.LEncryptedExtensions lee);
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
              V.free decoded_buffer.IM.decoded_buffer_fragment;
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
              V.free decoded_buffer.IM.decoded_buffer_raw_record;
              let resp = {
                ST.network_out_len = 0sz;
                ST.app_out_len = 0sz;
                ST.status = ST.IllegalTransition;
              };
              let buffer_resp = {
                ST.response = resp;
                ST.consumed_len = 0sz;
              };
              assert (pure (ST.server_network_bytes_end_to_end_correct
                'st0
                'st0
                buffer_resp
                (Ghost.reveal 'raw_bytes)
                'old_network_out
                'old_app_out));
              assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                buffer_resp.ST.consumed_len == 0sz));
              buffer_resp
            }
            IM.LCertificate lcert -> {
              IM.free_handshake_msg (IM.LCertificate lcert);
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
              V.free decoded_buffer.IM.decoded_buffer_fragment;
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
              V.free decoded_buffer.IM.decoded_buffer_raw_record;
              let resp = {
                ST.network_out_len = 0sz;
                ST.app_out_len = 0sz;
                ST.status = ST.IllegalTransition;
              };
              let buffer_resp = {
                ST.response = resp;
                ST.consumed_len = 0sz;
              };
              assert (pure (ST.server_network_bytes_end_to_end_correct
                'st0
                'st0
                buffer_resp
                (Ghost.reveal 'raw_bytes)
                'old_network_out
                'old_app_out));
              assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                buffer_resp.ST.consumed_len == 0sz));
              buffer_resp
            }
            IM.LCertificateVerify lcv -> {
              IM.free_handshake_msg (IM.LCertificateVerify lcv);
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
              V.free decoded_buffer.IM.decoded_buffer_fragment;
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
              V.free decoded_buffer.IM.decoded_buffer_raw_record;
              let resp = {
                ST.network_out_len = 0sz;
                ST.app_out_len = 0sz;
                ST.status = ST.IllegalTransition;
              };
              let buffer_resp = {
                ST.response = resp;
                ST.consumed_len = 0sz;
              };
              assert (pure (ST.server_network_bytes_end_to_end_correct
                'st0
                'st0
                buffer_resp
                (Ghost.reveal 'raw_bytes)
                'old_network_out
                'old_app_out));
              assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                buffer_resp.ST.consumed_len == 0sz));
              buffer_resp
            }
            IM.LFinished lfin -> {
              unfold (IM.is_valid_handshake_msg (IM.LFinished lfin) mhs);
              with fin. _;
              assert (pure (mhs == M.Finished fin));
              assert (pure (m == M.TlsHandshake (M.Finished fin)));
              assert (pure (CT.parsed_message_wire_success_for
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (IM.LTlsHandshake (IM.LFinished lfin))
                (M.TlsHandshake (M.Finished fin))));
              assert (pure (CT.wire_parse_success
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (M.TlsHandshake (M.Finished fin))));
              assert (pure (CT.received_tls_raw_delta_legal
                'st0
                (M.TlsHandshake (M.Finished fin))
                raw_record_bytes));
              CT.lemma_parsed_message_network_input_projection
                'st0
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (IM.LTlsHandshake (IM.LFinished lfin))
                (M.TlsHandshake (M.Finished fin))
                raw_record_bytes;
              assert (pure (CT.network_input_message_projection
                'st0
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (M.TlsHandshake (M.Finished fin))
                raw_record_bytes));
              assert (pure (CS.network_message_is_cleartext
                CL.Received
                (M.TlsHandshake (M.Finished fin)) == false));
              assert (pure (CT.protected_record_decodes_to_message
                'st0
                raw_record_bytes
                (M.TlsHandshake (M.Finished fin))));
              CT.lemma_protected_record_decodes_to_received_single_decode
                'st0
                raw_record_bytes
                (M.TlsHandshake (M.Finished fin));
              assert (pure (CS.received_event_nonempty_decode_projection
                'st0.CS.cs_model
                (ST.received_message_event
                  (M.TlsHandshake (M.Finished fin)))
                raw_record_bytes));
              unfold (connection_exactly s 'st0);
              let ready =
                CQ.can_receive_client_finished
                  s
                  #fin
                  #'st0;
              fold (connection_exactly s 'st0);
              if ready {
                assert (pure (CM.can_receive_client_finished
                  'st0
                  fin
                  raw_record_bytes));
                let resp =
                  process_client_finished
                    s
                    (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record)
                    decoded_buffer.IM.decoded_buffer_raw_record_len
                    lfin
                    #fin
                    network_out
                    network_out_len
                    app_out
                    app_out_len;
                let buffer_resp = {
                  ST.response = resp;
                  ST.consumed_len = decoded_buffer.IM.decoded_buffer_consumed_len;
                };
                with st1 network_out_bytes app_out_bytes.
                  assert (connection_exactly s st1 **
                          pts_to (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record) raw_record_bytes **
                          pts_to network_out network_out_bytes **
                          pts_to app_out app_out_bytes);
                assert (pure (SZ.v decoded_buffer.IM.decoded_buffer_consumed_len <=
                  B.length (Ghost.reveal 'raw_bytes)));
                assert (pure (ST.server_network_bytes_end_to_end_correct
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes));
                assert (pure (st1 ==
                  CM.received_client_finished_state
                    'st0
                    fin
                    raw_record_bytes));
                assert (pure (Seq.equal
                  raw_record_bytes
                  (Seq.slice
                    (Ghost.reveal 'raw_bytes)
                    0
                    (SZ.v buffer_resp.ST.consumed_len))));
                assert (pure (Seq.equal
                  raw_record_bytes
                  (ST.server_network_consumed_prefix
                    buffer_resp
                    (Ghost.reveal 'raw_bytes))));
                assert (pure (ST.server_decoded_message_event_projection
                  'st0
                  st1
                  resp
                  (M.TlsHandshake (M.Finished fin))
                  raw_record_bytes
                  network_out_bytes
                  app_out_bytes));
                ST.lemma_server_state_correct_record_read_key_schedule_projection
                  'st0;
                assert (pure (CS.record_read_key_schedule_projection_for_role
                  CS.ServerEndpoint
                  'st0.CS.cs_model));
                assert (pure (ST.server_protected_record_decode_uses_scheduled_read_key
                  'st0
                  raw_record_bytes));
                assert (pure (ST.server_protected_record_decode_correct
                  'st0
                  raw_record_bytes
                  (M.TlsHandshake (M.Finished fin))));
                assert (pure (ST.server_network_step_ok_received_decode_projection
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes));
                assert (pure (buffer_resp.ST.response.ST.status == ST.StepOk ==>
                  (exists ch raw_received.
                    st1 ==
                      CM.received_client_hello_state
                        'st0
                        ch
                        raw_received /\
                    Seq.equal
                      raw_received
                      (Seq.slice
                        (Ghost.reveal 'raw_bytes)
                        0
                        (SZ.v buffer_resp.ST.consumed_len))) \/
                  (exists fin raw_received.
                    st1 ==
                      CM.received_client_finished_state
                        'st0
                        fin
                        raw_received /\
                    Seq.equal
                      raw_received
                      (Seq.slice
                        (Ghost.reveal 'raw_bytes)
                        0
                        (SZ.v buffer_resp.ST.consumed_len)))));
                assert (pure (ST.server_network_step_ok_consumed_prefix
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)));
                assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                  buffer_resp.ST.consumed_len == 0sz));
                assert (pure (ST.server_network_consumed_input_projection
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes));
                V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
                V.free decoded_buffer.IM.decoded_buffer_fragment;
                V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
                V.free decoded_buffer.IM.decoded_buffer_raw_record;
                buffer_resp
              } else {
                IM.free_finished lfin;
                V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
                V.free decoded_buffer.IM.decoded_buffer_fragment;
                V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
                V.free decoded_buffer.IM.decoded_buffer_raw_record;
                let resp = {
                  ST.network_out_len = 0sz;
                  ST.app_out_len = 0sz;
                  ST.status = ST.IllegalTransition;
                };
                let buffer_resp = {
                  ST.response = resp;
                  ST.consumed_len = 0sz;
                };
                assert (pure (ST.server_network_bytes_end_to_end_correct
                  'st0
                  'st0
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  'old_network_out
                  'old_app_out));
                assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                  buffer_resp.ST.consumed_len == 0sz));
                buffer_resp
              }
            }
            IM.LHelloRetryRequest -> {
              IM.free_handshake_msg IM.LHelloRetryRequest;
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
              V.free decoded_buffer.IM.decoded_buffer_fragment;
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
              V.free decoded_buffer.IM.decoded_buffer_raw_record;
              let resp = {
                ST.network_out_len = 0sz;
                ST.app_out_len = 0sz;
                ST.status = ST.IllegalTransition;
              };
              let buffer_resp = {
                ST.response = resp;
                ST.consumed_len = 0sz;
              };
              assert (pure (ST.server_network_bytes_end_to_end_correct
                'st0
                'st0
                buffer_resp
                (Ghost.reveal 'raw_bytes)
                'old_network_out
                'old_app_out));
              assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                buffer_resp.ST.consumed_len == 0sz));
              buffer_resp
            }
          }
        }
          IM.LTlsApplicationData lapp -> {
            with m. assert (pure True);
            unfold (IM.is_valid_tls_message (IM.LTlsApplicationData lapp) m);
            with mapp. _;
            assert (pure (m == M.TlsApplicationData mapp));
            assert (pure (CT.parsed_message_wire_success_for
              decoded_buffer.IM.decoded_buffer_content_type
              fragment_bytes
              (IM.LTlsApplicationData lapp)
              (M.TlsApplicationData mapp)));
            assert (pure (CT.wire_parse_success
              decoded_buffer.IM.decoded_buffer_content_type
              fragment_bytes
              (M.TlsApplicationData mapp)));
            assert (pure (CT.received_tls_raw_delta_legal
              'st0
              (M.TlsApplicationData mapp)
              raw_record_bytes));
            CT.lemma_parsed_message_network_input_projection
              'st0
              decoded_buffer.IM.decoded_buffer_content_type
              fragment_bytes
              (IM.LTlsApplicationData lapp)
              (M.TlsApplicationData mapp)
              raw_record_bytes;
            assert (pure (CT.network_input_message_projection
              'st0
              decoded_buffer.IM.decoded_buffer_content_type
              fragment_bytes
              (M.TlsApplicationData mapp)
              raw_record_bytes));
            assert (pure (CS.network_message_is_cleartext
              CL.Received
              (M.TlsApplicationData mapp) == false));
            assert (pure (CT.protected_record_decodes_to_message
              'st0
              raw_record_bytes
              (M.TlsApplicationData mapp)));
            CT.lemma_protected_record_decodes_to_received_single_decode
              'st0
              raw_record_bytes
              (M.TlsApplicationData mapp);
            assert (pure (CS.received_event_nonempty_decode_projection
              'st0.CS.cs_model
              (ST.received_message_event
                (M.TlsApplicationData mapp))
              raw_record_bytes));
            unfold (connection_exactly s 'st0);
            let ready =
              CQ.can_receive_endpoint_application_data
                s
                #'st0;
            fold (connection_exactly s 'st0);
            let app_fits =
              CM.sizet_lte_plain
                lapp.IM.application_data_len
                app_out_len;
            CM.lemma_sizet_lte_plain
              lapp.IM.application_data_len
              app_out_len;
            if ready {
              if app_fits {
                assert (pure ('st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
                assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
                assert (pure (CS.application_traffic_available_for_role
                  CS.ServerEndpoint
                  'st0.CS.cs_model.CS.model_handshake
                  CL.Received));
                assert (pure (U64.fits ('st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
                assert (pure (SZ.v lapp.IM.application_data_len <= SZ.v app_out_len));
                let resp =
                  process_application_data
                    s
                    (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record)
                    decoded_buffer.IM.decoded_buffer_raw_record_len
                    lapp
                    #mapp
                    network_out
                    network_out_len
                    app_out
                    app_out_len;
                let buffer_resp = {
                  ST.response = resp;
                  ST.consumed_len = decoded_buffer.IM.decoded_buffer_consumed_len;
                };
                with st1 network_out_bytes app_out_bytes.
                  assert (connection_exactly s st1 **
                          pts_to (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record) raw_record_bytes **
                          pts_to network_out network_out_bytes **
                          pts_to app_out app_out_bytes);
                assert (pure (SZ.v decoded_buffer.IM.decoded_buffer_consumed_len <=
                  B.length (Ghost.reveal 'raw_bytes)));
                assert (pure (ST.server_network_bytes_end_to_end_correct
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes));
                assert (pure (st1 ==
                  CM.received_application_data_state
                    'st0
                    mapp
                    raw_record_bytes));
                assert (pure (Seq.equal
                  raw_record_bytes
                  (Seq.slice
                    (Ghost.reveal 'raw_bytes)
                    0
                    (SZ.v buffer_resp.ST.consumed_len))));
                assert (pure (Seq.equal
                  raw_record_bytes
                  (ST.server_network_consumed_prefix
                    buffer_resp
                    (Ghost.reveal 'raw_bytes))));
                assert (pure (ST.server_decoded_message_event_projection
                  'st0
                  st1
                  resp
                  (M.TlsApplicationData mapp)
                  raw_record_bytes
                  network_out_bytes
                  app_out_bytes));
                ST.lemma_server_state_correct_record_read_key_schedule_projection
                  'st0;
                assert (pure (CS.record_read_key_schedule_projection_for_role
                  CS.ServerEndpoint
                  'st0.CS.cs_model));
                assert (pure (ST.server_protected_record_decode_uses_scheduled_read_key
                  'st0
                  raw_record_bytes));
                assert (pure (ST.server_protected_record_decode_correct
                  'st0
                  raw_record_bytes
                  (M.TlsApplicationData mapp)));
                assert (pure (ST.server_network_step_ok_received_decode_projection
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes));
                assert (pure (exists bytes raw_received.
                  st1 ==
                    CM.received_application_data_state
                      'st0
                      bytes
                      raw_received /\
                  Seq.equal
                    raw_received
                    (ST.server_network_consumed_prefix
                      buffer_resp
                      (Ghost.reveal 'raw_bytes))));
                assert (pure (ST.server_network_step_ok_consumed_prefix
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)));
                assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                  buffer_resp.ST.consumed_len == 0sz));
                assert (pure (ST.server_network_consumed_input_projection
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes));
                V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
                V.free decoded_buffer.IM.decoded_buffer_fragment;
                V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
                V.free decoded_buffer.IM.decoded_buffer_raw_record;
                buffer_resp
              } else {
                IM.free_application_data lapp;
                V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
                V.free decoded_buffer.IM.decoded_buffer_fragment;
                V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
                V.free decoded_buffer.IM.decoded_buffer_raw_record;
                let resp = {
                  ST.network_out_len = 0sz;
                  ST.app_out_len = 0sz;
                  ST.status = ST.IllegalTransition;
                };
                let buffer_resp = {
                  ST.response = resp;
                  ST.consumed_len = 0sz;
                };
                assert (pure (ST.server_network_bytes_end_to_end_correct
                  'st0
                  'st0
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  'old_network_out
                  'old_app_out));
                assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                  buffer_resp.ST.consumed_len == 0sz));
                buffer_resp
              }
            } else {
              IM.free_application_data lapp;
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
              V.free decoded_buffer.IM.decoded_buffer_fragment;
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
              V.free decoded_buffer.IM.decoded_buffer_raw_record;
              let resp = {
                ST.network_out_len = 0sz;
                ST.app_out_len = 0sz;
                ST.status = ST.IllegalTransition;
              };
              let buffer_resp = {
                ST.response = resp;
                ST.consumed_len = 0sz;
              };
              assert (pure (ST.server_network_bytes_end_to_end_correct
                'st0
                'st0
                buffer_resp
                (Ghost.reveal 'raw_bytes)
                'old_network_out
                'old_app_out));
              assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                buffer_resp.ST.consumed_len == 0sz));
              buffer_resp
            }
          }
          IM.LTlsAlert alert -> {
            with m. assert (pure True);
            unfold (IM.is_valid_tls_message (IM.LTlsAlert alert) m);
            with malert. _;
            assert (pure (IM.alert_description_matches alert malert));
            assert (pure (m == M.TlsAlert malert));
            let parsed_alert =
              Ghost.hide (IM.alert_description_of_wire_or_unexpected alert);
            IM.lemma_alert_description_of_wire_matches alert malert;
            assert (pure (Ghost.reveal parsed_alert == malert));
            let close_notify = alert = 0uy;
            if close_notify {
              assert (pure (U8.v alert == 0));
              assert (pure (Ghost.reveal parsed_alert == T.CloseNotify));
              assert (pure (IM.alert_description_matches alert T.CloseNotify));
              assert (pure (CT.parsed_message_wire_success_for
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (IM.LTlsAlert alert)
                (M.TlsAlert T.CloseNotify)));
              assert (pure (CT.wire_parse_success
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (M.TlsAlert T.CloseNotify)));
              assert (pure (CT.received_tls_raw_delta_legal
                'st0
                (M.TlsAlert T.CloseNotify)
                raw_record_bytes));
              CT.lemma_parsed_message_network_input_projection
                'st0
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (IM.LTlsAlert alert)
                (M.TlsAlert T.CloseNotify)
                raw_record_bytes;
              assert (pure (CT.network_input_message_projection
                'st0
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (M.TlsAlert T.CloseNotify)
                raw_record_bytes));
              assert (pure (CS.network_message_is_cleartext
                CL.Received
                (M.TlsAlert T.CloseNotify) == false));
              assert (pure (CT.protected_record_decodes_to_message
                'st0
                raw_record_bytes
                (M.TlsAlert T.CloseNotify)));
              CT.lemma_protected_record_decodes_to_received_single_decode
                'st0
                raw_record_bytes
                (M.TlsAlert T.CloseNotify);
              assert (pure (CS.received_event_nonempty_decode_projection
                'st0.CS.cs_model
                (ST.received_message_event
                  (M.TlsAlert T.CloseNotify))
                raw_record_bytes));
              unfold (connection_exactly s 'st0);
              let ready =
                CQ.can_receive_endpoint_close_notify
                  s
                  #'st0;
              fold (connection_exactly s 'st0);
              if ready {
                assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
                assert (pure ('st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
                  'st0.CS.cs_model.CS.model_control == CS.ControlClosing));
                assert (pure (U64.fits ('st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
                let resp =
                  process_close_notify
                    s
                    (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record)
                    decoded_buffer.IM.decoded_buffer_raw_record_len
                    network_out
                    network_out_len
                    app_out
                    app_out_len;
                let buffer_resp = {
                  ST.response = resp;
                  ST.consumed_len = decoded_buffer.IM.decoded_buffer_consumed_len;
                };
                with st1 network_out_bytes app_out_bytes.
                  assert (connection_exactly s st1 **
                          pts_to (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record) raw_record_bytes **
                          pts_to network_out network_out_bytes **
                          pts_to app_out app_out_bytes);
                assert (pure (SZ.v decoded_buffer.IM.decoded_buffer_consumed_len <=
                  B.length (Ghost.reveal 'raw_bytes)));
                assert (pure (ST.server_network_bytes_end_to_end_correct
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes));
                assert (pure (st1 ==
                  CM.received_close_notify_state
                    'st0
                    raw_record_bytes));
                assert (pure (Seq.equal
                  raw_record_bytes
                  (Seq.slice
                    (Ghost.reveal 'raw_bytes)
                    0
                    (SZ.v buffer_resp.ST.consumed_len))));
                assert (pure (Seq.equal
                  raw_record_bytes
                  (ST.server_network_consumed_prefix
                    buffer_resp
                    (Ghost.reveal 'raw_bytes))));
                assert (pure (ST.server_decoded_message_event_projection
                  'st0
                  st1
                  resp
                  (M.TlsAlert T.CloseNotify)
                  raw_record_bytes
                  network_out_bytes
                  app_out_bytes));
                ST.lemma_server_state_correct_record_read_key_schedule_projection
                  'st0;
                assert (pure (CS.record_read_key_schedule_projection_for_role
                  CS.ServerEndpoint
                  'st0.CS.cs_model));
                assert (pure (ST.server_protected_record_decode_uses_scheduled_read_key
                  'st0
                  raw_record_bytes));
                assert (pure (ST.server_protected_record_decode_correct
                  'st0
                  raw_record_bytes
                  (M.TlsAlert T.CloseNotify)));
                assert (pure (ST.server_network_step_ok_received_decode_projection
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes));
                assert (pure (exists raw_received.
                  st1 ==
                    CM.received_close_notify_state
                      'st0
                      raw_received /\
                  Seq.equal
                    raw_received
                    (ST.server_network_consumed_prefix
                      buffer_resp
                      (Ghost.reveal 'raw_bytes))));
                assert (pure (ST.server_network_step_ok_consumed_prefix
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)));
                assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                  buffer_resp.ST.consumed_len == 0sz));
                assert (pure (ST.server_network_consumed_input_projection
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes));
                V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
                V.free decoded_buffer.IM.decoded_buffer_fragment;
                V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
                V.free decoded_buffer.IM.decoded_buffer_raw_record;
                buffer_resp
              } else {
                V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
                V.free decoded_buffer.IM.decoded_buffer_fragment;
                V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
                V.free decoded_buffer.IM.decoded_buffer_raw_record;
                let resp = {
                  ST.network_out_len = 0sz;
                  ST.app_out_len = 0sz;
                  ST.status = ST.IllegalTransition;
                };
                let buffer_resp = {
                  ST.response = resp;
                  ST.consumed_len = 0sz;
                };
                assert (pure (ST.server_network_bytes_end_to_end_correct
                  'st0
                  'st0
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  'old_network_out
                  'old_app_out));
                assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                  buffer_resp.ST.consumed_len == 0sz));
                buffer_resp
              }
            } else {
              assert (pure (U8.v alert <> 0));
              IM.lemma_alert_description_nonzero_not_close_notify
                alert
                (Ghost.reveal parsed_alert);
              assert (pure (Ghost.reveal parsed_alert <> T.CloseNotify));
              assert (pure (CT.parsed_message_wire_success_for
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (IM.LTlsAlert alert)
                (M.TlsAlert (Ghost.reveal parsed_alert))));
              assert (pure (CT.wire_parse_success
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (M.TlsAlert (Ghost.reveal parsed_alert))));
              assert (pure (CT.received_tls_raw_delta_legal
                'st0
                (M.TlsAlert (Ghost.reveal parsed_alert))
                raw_record_bytes));
              CT.lemma_parsed_message_network_input_projection
                'st0
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (IM.LTlsAlert alert)
                (M.TlsAlert (Ghost.reveal parsed_alert))
                raw_record_bytes;
              assert (pure (CT.network_input_message_projection
                'st0
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (M.TlsAlert (Ghost.reveal parsed_alert))
                raw_record_bytes));
              assert (pure (CS.network_message_is_cleartext
                CL.Received
                (M.TlsAlert (Ghost.reveal parsed_alert)) == false));
              assert (pure (CT.protected_record_decodes_to_message
                'st0
                raw_record_bytes
                (M.TlsAlert (Ghost.reveal parsed_alert))));
              CT.lemma_protected_record_decodes_to_received_single_decode
                'st0
                raw_record_bytes
                (M.TlsAlert (Ghost.reveal parsed_alert));
              assert (pure (CS.received_event_nonempty_decode_projection
                'st0.CS.cs_model
                (ST.received_message_event
                  (M.TlsAlert (Ghost.reveal parsed_alert)))
                raw_record_bytes));
              let resp =
                process_alert_failure
                  s
                  (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record)
                  decoded_buffer.IM.decoded_buffer_raw_record_len
                  alert
                  #parsed_alert
                  network_out
                  network_out_len
                  app_out
                  app_out_len;
              let buffer_resp = {
                ST.response = resp;
                ST.consumed_len = decoded_buffer.IM.decoded_buffer_consumed_len;
              };
              with st1 network_out_bytes app_out_bytes.
                assert (connection_exactly s st1 **
                        pts_to (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record) raw_record_bytes **
                        pts_to network_out network_out_bytes **
                        pts_to app_out app_out_bytes);
              assert (pure (SZ.v decoded_buffer.IM.decoded_buffer_consumed_len <=
                B.length (Ghost.reveal 'raw_bytes)));
              assert (pure (ST.server_network_bytes_end_to_end_correct
                'st0
                st1
                buffer_resp
                (Ghost.reveal 'raw_bytes)
                network_out_bytes
                app_out_bytes));
              assert (pure (st1 ==
                CM.received_alert_failure_state
                  'st0
                  (Ghost.reveal parsed_alert)
                  raw_record_bytes));
              assert (pure (ST.server_network_step_ok_consumed_prefix
                'st0
                st1
                buffer_resp
                (Ghost.reveal 'raw_bytes)));
              assert (pure (ST.server_network_step_ok_received_decode_projection
                'st0
                st1
                buffer_resp
                (Ghost.reveal 'raw_bytes)
                network_out_bytes
                app_out_bytes));
              assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                buffer_resp.ST.consumed_len == 0sz));
              assert (pure (ST.server_network_consumed_input_projection
                'st0
                st1
                buffer_resp
                (Ghost.reveal 'raw_bytes)
                network_out_bytes
                app_out_bytes));
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
              V.free decoded_buffer.IM.decoded_buffer_fragment;
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
              V.free decoded_buffer.IM.decoded_buffer_raw_record;
              buffer_resp
            }
          }
          IM.LTlsChangeCipherSpec -> {
            with m. unfold (IM.is_valid_tls_message IM.LTlsChangeCipherSpec m);
            assert (pure (m == M.TlsChangeCipherSpec));
            assert (pure (CT.parsed_message_wire_success_for
              decoded_buffer.IM.decoded_buffer_content_type
              fragment_bytes
              IM.LTlsChangeCipherSpec
              M.TlsChangeCipherSpec));
            assert (pure (CT.wire_parse_success
              decoded_buffer.IM.decoded_buffer_content_type
              fragment_bytes
              M.TlsChangeCipherSpec));
            assert (pure (CT.received_tls_raw_delta_legal
              'st0
              M.TlsChangeCipherSpec
              raw_record_bytes));
            CT.lemma_parsed_message_network_input_projection
              'st0
              decoded_buffer.IM.decoded_buffer_content_type
              fragment_bytes
              IM.LTlsChangeCipherSpec
              M.TlsChangeCipherSpec
              raw_record_bytes;
            assert (pure (CT.network_input_message_projection
              'st0
              decoded_buffer.IM.decoded_buffer_content_type
              fragment_bytes
              M.TlsChangeCipherSpec
              raw_record_bytes));
            assert (pure (CS.network_message_is_cleartext
              CL.Received
              M.TlsChangeCipherSpec == true));
            unfold (connection_exactly s 'st0);
            let handshaking =
              CQ.is_handshaking
                s
                #'st0;
            fold (connection_exactly s 'st0);
            if handshaking {
              assert (pure (exists stage.
                'st0.CS.cs_model.CS.model_control == CS.ControlHandshaking stage));
              let resp =
                process_change_cipher_spec
                  s
                  (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record)
                  decoded_buffer.IM.decoded_buffer_raw_record_len
                  network_out
                  network_out_len
                  app_out
                  app_out_len;
              let buffer_resp = {
                ST.response = resp;
                ST.consumed_len = decoded_buffer.IM.decoded_buffer_consumed_len;
              };
              with st1 network_out_bytes app_out_bytes.
                assert (connection_exactly s st1 **
                        pts_to (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record) raw_record_bytes **
                        pts_to network_out network_out_bytes **
                        pts_to app_out app_out_bytes);
              assert (pure (SZ.v decoded_buffer.IM.decoded_buffer_consumed_len <=
                B.length (Ghost.reveal 'raw_bytes)));
              assert (pure (ST.server_network_bytes_end_to_end_correct
                'st0
                st1
                buffer_resp
                (Ghost.reveal 'raw_bytes)
                network_out_bytes
                app_out_bytes));
              assert (pure (st1 ==
                CM.received_change_cipher_spec_state
                  'st0
                  raw_record_bytes));
              assert (pure (Seq.equal
                raw_record_bytes
                (Seq.slice
                  (Ghost.reveal 'raw_bytes)
                  0
                  (SZ.v buffer_resp.ST.consumed_len))));
              assert (pure (Seq.equal
                raw_record_bytes
                (ST.server_network_consumed_prefix
                  buffer_resp
                  (Ghost.reveal 'raw_bytes))));
              assert (pure (ST.server_decoded_message_event_projection
                'st0
                st1
                resp
                M.TlsChangeCipherSpec
                raw_record_bytes
                network_out_bytes
                app_out_bytes));
              assert (pure (ST.server_network_step_ok_received_decode_projection
                'st0
                st1
                buffer_resp
                (Ghost.reveal 'raw_bytes)
                network_out_bytes
                app_out_bytes));
              assert (pure (exists raw_received.
                st1 ==
                  CM.received_change_cipher_spec_state
                    'st0
                    raw_received /\
                Seq.equal
                  raw_received
                  (ST.server_network_consumed_prefix
                    buffer_resp
                    (Ghost.reveal 'raw_bytes))));
              assert (pure (ST.server_network_step_ok_consumed_prefix
                'st0
                st1
                buffer_resp
                (Ghost.reveal 'raw_bytes)));
              assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                buffer_resp.ST.consumed_len == 0sz));
              assert (pure (ST.server_network_consumed_input_projection
                'st0
                st1
                buffer_resp
                (Ghost.reveal 'raw_bytes)
                network_out_bytes
                app_out_bytes));
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
              V.free decoded_buffer.IM.decoded_buffer_fragment;
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
              V.free decoded_buffer.IM.decoded_buffer_raw_record;
              buffer_resp
            } else {
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
              V.free decoded_buffer.IM.decoded_buffer_fragment;
              V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
              V.free decoded_buffer.IM.decoded_buffer_raw_record;
              let resp = {
                ST.network_out_len = 0sz;
                ST.app_out_len = 0sz;
                ST.status = ST.IllegalTransition;
              };
              let buffer_resp = {
                ST.response = resp;
                ST.consumed_len = 0sz;
              };
              assert (pure (ST.server_network_bytes_end_to_end_correct
                'st0
                'st0
                buffer_resp
                (Ghost.reveal 'raw_bytes)
                'old_network_out
                'old_app_out));
              assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                buffer_resp.ST.consumed_len == 0sz));
              buffer_resp
            }
          }
          IM.LTlsIgnoredPostHandshake lignored -> {
            IM.free_tls_message (IM.LTlsIgnoredPostHandshake lignored);
            V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
            V.free decoded_buffer.IM.decoded_buffer_fragment;
            V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
            V.free decoded_buffer.IM.decoded_buffer_raw_record;
            let resp = {
              ST.network_out_len = 0sz;
              ST.app_out_len = 0sz;
              ST.status = ST.IllegalTransition;
            };
            let buffer_resp = {
              ST.response = resp;
              ST.consumed_len = 0sz;
            };
            assert (pure (ST.server_network_bytes_end_to_end_correct
              'st0
              'st0
              buffer_resp
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out));
            assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
              buffer_resp.ST.consumed_len == 0sz));
            buffer_resp
          }
          IM.LTlsKeyUpdate lreq -> {
            IM.free_tls_message (IM.LTlsKeyUpdate lreq);
            V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
            V.free decoded_buffer.IM.decoded_buffer_fragment;
            V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
            V.free decoded_buffer.IM.decoded_buffer_raw_record;
            let resp = {
              ST.network_out_len = 0sz;
              ST.app_out_len = 0sz;
              ST.status = ST.IllegalTransition;
            };
            let buffer_resp = {
              ST.response = resp;
              ST.consumed_len = 0sz;
            };
            assert (pure (ST.server_network_bytes_end_to_end_correct
              'st0
              'st0
              buffer_resp
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out));
            assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
              buffer_resp.ST.consumed_len == 0sz));
            buffer_resp
          }
        }
      }
    }
  }
}
}
