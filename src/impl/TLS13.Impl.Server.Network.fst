module TLS13.Impl.Server.Network

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
                (buffer_resp.ST.response.ST.status == ST.StepOk ==>
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
                        (SZ.v buffer_resp.ST.consumed_len)))) /\
                (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                  buffer_resp.ST.consumed_len == 0sz))
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
      let resp = {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.DecodeError;
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
    IM.NetworkBufferOk decoded_buffer -> {
      with raw_record_bytes fragment_bytes.
        assert (V.pts_to decoded_buffer.IM.decoded_buffer_raw_record raw_record_bytes **
                V.pts_to decoded_buffer.IM.decoded_buffer_fragment fragment_bytes);
      V.to_array_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
      V.to_array_pts_to decoded_buffer.IM.decoded_buffer_fragment;
      match decoded_buffer.IM.decoded_buffer_parsed {
        None -> {
          V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
          V.free decoded_buffer.IM.decoded_buffer_fragment;
          V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
          V.free decoded_buffer.IM.decoded_buffer_raw_record;
          let resp = {
            ST.network_out_len = 0sz;
            ST.app_out_len = 0sz;
            ST.status = ST.DecodeError;
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
              assert (pure (Seq.equal
                fragment_bytes
                (W.serialize_handshake (M.ClientHello ch))));
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
                    assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                      buffer_resp.ST.consumed_len == 0sz));
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
                assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                  buffer_resp.ST.consumed_len == 0sz));
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
            IM.free_tls_message (IM.LTlsApplicationData lapp);
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
          IM.LTlsAlert alert -> {
            IM.free_tls_message (IM.LTlsAlert alert);
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
          IM.LTlsChangeCipherSpec -> {
            IM.free_tls_message IM.LTlsChangeCipherSpec;
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
