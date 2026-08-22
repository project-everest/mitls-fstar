module TLS13.Impl.Server.Network

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module Arr = Pulse.Lib.Array
module AC = TLS13.Impl.ArrayCopy
module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CS = TLS13.Spec.StateMachine
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
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GFin = TLS13.Wire.Generated.Finished
module O = TLS13.OpenSSL
module P = TLS13.Impl.Parser
module R = TLS13.Record.Spec
module Ser = TLS13.Impl.Serializer
module SC = TLS13.Impl.Serializer.Common
module SM = TLS13.Spec.StateMachine.ClientTrace
module ST = TLS13.Impl.Server.Types
module Tags = TLS13.Impl.ConnectionState.Tags
module T = TLS13.Types
module Trace = TLS13.Trace
module Tr = TLS13.Transcript
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec

(* The server_name extension is optional (RFC 6066), and absent whenever a client
   connects to a bare IP literal, so this is stated for both cases: [present]
   always reflects whether the message carried an SNI, and the stored length is
   only meaningful when it did. *)
let lemma_client_hello_sni_len_for
  (present:bool)
  (storage:B.bytes)
  (len:SZ.t)
  (ch:GCH.clientHello)
  : Lemma
      (requires IM.optional_byte_prefix_matches present storage len (Sem.clientHello_server_name ch) /\
                B.length storage < 65536)
      (ensures present == CM.client_hello_has_sni ch /\
               (present ==> CM.client_hello_server_name_len_for ch == len))
=
  if present then
    match Sem.clientHello_server_name ch with
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
  else
    assert (Sem.clientHello_server_name ch == None)

inline_for_extraction
fn process_client_hello
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lch:IM.client_hello)
  (#ch:erased GCH.clientHello)
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
               lch.IM.client_hello_has_server_name == CM.client_hello_has_sni ch /\
               (lch.IM.client_hello_has_server_name ==>
                  CM.client_hello_server_name_len_for ch ==
                    lch.IM.client_hello_server_name_len) /\
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
  (#fin:erased GFin.finished)
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
                 TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection
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
                 CT.received_tls_raw_delta_legal_unbuffered
                   'st0
                   (M.TlsApplicationData (Ghost.reveal app_payload))
                   (Ghost.reveal 'raw_bytes) /\
                 TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection
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
  AC.copy_prefix
    data_len
    (V.vec_to_array lapp.IM.application_data_bytes)
    16640sz
    app_out
    app_out_len;
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

  assert (pure (SZ.v resp.ST.network_out_len == B.length B.empty));
  assert (pure (SZ.v resp.ST.app_out_len <= B.length app_out_bytes));
  Seq.lemma_eq_elim B.empty (ST.response_network_out resp 'old_network_out);
  assert (pure (Seq.equal
    (ST.response_network_out resp 'old_network_out)
    B.empty));
  Seq.lemma_eq_elim
    (Ghost.reveal app_payload)
    (ST.response_app_out resp app_out_bytes);
  CL.lemma_concat_bytes_singleton (Ghost.reveal app_payload);
  Seq.lemma_eq_elim
    (Ghost.reveal app_payload)
    (CL.concat_bytes [Ghost.reveal app_payload]);
  assert (pure (ST.response_app_out_matches_event
    resp
    (ST.received_message_event (M.TlsApplicationData (Ghost.reveal app_payload)))
    app_out_bytes));
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
                 CT.received_tls_raw_delta_legal_unbuffered
                   'st0
                   (M.TlsAlert T.Close_notify)
                   (Ghost.reveal 'raw_bytes) /\
                 TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection
                   'st0.CS.cs_model
                   (ST.received_message_event
                     (M.TlsAlert T.Close_notify))
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
                  (M.TlsAlert T.Close_notify)
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
      (M.TlsAlert T.Close_notify)
      (Ghost.reveal 'raw_bytes))
    (CM.received_close_notify_state
      'st0
      (Ghost.reveal 'raw_bytes))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (ST.received_message_delta
      (M.TlsAlert T.Close_notify)
      (Ghost.reveal 'raw_bytes))
    (CM.received_close_notify_state
      'st0
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsAlert T.Close_notify)
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
      (M.TlsAlert T.Close_notify)
      (Ghost.reveal 'raw_bytes))
    (CM.received_close_notify_state
      'st0
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsAlert T.Close_notify)
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
    (ST.received_message_event (M.TlsAlert T.Close_notify))
    B.empty
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_network_response
    'st0
    (CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes))
    resp
    (M.TlsAlert T.Close_notify)
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_network_event_end_to_end_correct
    'st0
    (CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes))
    resp
    (M.TlsAlert T.Close_notify)
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  resp
}

fn process_key_update
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (requested:bool)
  (#req:erased M.key_update_request)
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
                 'st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
                 (requested ==> reveal req == M.UpdateRequested) /\
                 (requested == false ==> reveal req == M.UpdateNotRequested) /\
                 U64.fits ('st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 CT.received_tls_raw_delta_legal_unbuffered
                   'st0
                   (M.TlsKeyUpdate (reveal req))
                   (Ghost.reveal 'raw_bytes) /\
                 TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection
                   'st0.CS.cs_model
                   (ST.received_message_event
                     (M.TlsKeyUpdate (reveal req)))
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
                  CM.server_received_key_update_state
                    'st0
                    (reveal req)
                    (Ghost.reveal 'raw_bytes) /\
                ST.server_network_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  (M.TlsKeyUpdate (reveal req))
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CN.mark_server_received_key_update
    s
    raw
    requested
    #req;
  fold (connection_exactly
    s
    (CM.server_received_key_update_state
      'st0
      (reveal req)
      (Ghost.reveal 'raw_bytes)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  CM.lemma_server_received_key_update_state_evolves
    'st0
    (reveal req)
    (Ghost.reveal 'raw_bytes);
  assert (pure (CS.legal_connection_delta
    'st0
    (ST.received_message_delta
      (M.TlsKeyUpdate (reveal req))
      (Ghost.reveal 'raw_bytes))
    (CM.server_received_key_update_state
      'st0
      (reveal req)
      (Ghost.reveal 'raw_bytes))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (ST.received_message_delta
      (M.TlsKeyUpdate (reveal req))
      (Ghost.reveal 'raw_bytes))
    (CM.server_received_key_update_state
      'st0
      (reveal req)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsKeyUpdate (reveal req))
      (Ghost.reveal 'raw_bytes))
    (CM.server_received_key_update_state
      'st0
      (reveal req)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.server_received_key_update_state
      'st0
      (reveal req)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsKeyUpdate (reveal req))
      (Ghost.reveal 'raw_bytes))
    (CM.server_received_key_update_state
      'st0
      (reveal req)
      (Ghost.reveal 'raw_bytes));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (ST.received_message_delta
      (M.TlsKeyUpdate (reveal req))
      (Ghost.reveal 'raw_bytes))
    (CM.server_received_key_update_state
      'st0
      (reveal req)
      (Ghost.reveal 'raw_bytes));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  assert (pure (Seq.equal B.empty (ST.response_network_out resp 'old_network_out)));
  assert (pure (Seq.equal B.empty (ST.response_app_out resp 'old_app_out)));

  assert (pure ((CM.server_received_key_update_state 'st0 (reveal req) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.server_received_key_update_state 'st0 (reveal req) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.server_received_key_update_state 'st0 (reveal req) (Ghost.reveal 'raw_bytes)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.server_received_key_update_state 'st0 (reveal req) (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.server_received_key_update_state 'st0 (reveal req) (Ghost.reveal 'raw_bytes))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.server_received_key_update_state 'st0 (reveal req) (Ghost.reveal 'raw_bytes))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.server_received_key_update_state 'st0 (reveal req) (Ghost.reveal 'raw_bytes))
    resp
    (ST.received_message_event (M.TlsKeyUpdate (reveal req)))
    B.empty
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_network_response
    'st0
    (CM.server_received_key_update_state 'st0 (reveal req) (Ghost.reveal 'raw_bytes))
    resp
    (M.TlsKeyUpdate (reveal req))
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_network_event_end_to_end_correct
    'st0
    (CM.server_received_key_update_state 'st0 (reveal req) (Ghost.reveal 'raw_bytes))
    resp
    (M.TlsKeyUpdate (reveal req))
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
                 Ghost.reveal alert <> T.Close_notify /\
                 Tags.alert_tag_matches alert_wire (Ghost.reveal alert) /\
                 CT.received_tls_raw_delta_legal_unbuffered
                   'st0
                   (M.TlsAlert (Ghost.reveal alert))
                   (Ghost.reveal 'raw_bytes) /\
                 TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection
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
                 CT.received_tls_raw_delta_legal_unbuffered
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

(* G3: a CLEARTEXT record's raw bytes, viewed as a [ConnCleartextHandshake]
   delta.  [decoder_fragment_relation] leaves the outer content type existential
   and only says the dispatcher's [content_type] byte matches it; pinning that
   byte to 0x16 collapses the existential to [T.Handshake] -- in particular it
   rules out the [Application_data] arm, which is the protected reading. *)
let lemma_cleartext_record_raw_delta_legal
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires
        (exists outer_ct.
          IM.content_type_matches content_type outer_ct /\
          W.parse_record_wire raw_received ==
            Some (outer_ct, fragment, B.length raw_received)) /\
        IM.content_type_matches content_type T.Handshake)
      (ensures
        W.parse_record_wire raw_received ==
          Some (T.Handshake, fragment, B.length raw_received))
= ()

(** G3: set a cleartext handshake record's fragment aside instead of failing.

    A ClientHello can be larger than one record's fragment, in which case the
    first record's bytes parse as no message at all.  Before G3 that reached
    [process_decode_error] and the connection died; here the record is instead
    CONSUMED and its fragment stored, so a later record can complete the
    message.  This is the cleartext twin of the client's
    [try_buffer_protected_handshake_record], and returns [None] -- meaning
    "not my business, carry on to the decode error" -- whenever any of the
    conditions of [CS.legal_cleartext_handshake_step] cannot be discharged:

      - the connection is not a server awaiting a ClientHello (or a client
        awaiting a ServerHello), which [CQ.can_buffer_cleartext_handshake]
        decides;
      - the fragment is empty, so the step would make no progress and a peer
        could feed empty records forever;
      - the coalesced stream `pending ++ fragment` is longer than
        [max_client_hello_len], so it could never be completed into the one
        message this buffer can ever be drained by;
      - the coalesced stream already PARSES as a whole message.  Buffering it
        would be illegal (the model's last-resort conjunct) and pointless;
        delivering a reassembled ClientHello is the next increment. *)
fn try_buffer_cleartext_handshake_record
  (s:server)
  (protected:bool)
  (content_type:U8.t)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (
             B.length 'raw_bytes == SZ.v raw_len /\
             B.length 'fragment_bytes == SZ.v fragment_len /\
             B.length 'old_network_out == SZ.v network_out_len /\
             B.length 'old_app_out == SZ.v app_out_len /\
             SZ.v fragment_len <= Bounds.max_handshake_flight_len /\
             ST.server_end_to_end_invariant 'st0 /\
             (~protected ==>
               (exists outer_ct.
                 IM.content_type_matches content_type outer_ct /\
                 W.parse_record_wire (Ghost.reveal 'raw_bytes) ==
                   Some
                     (outer_ct,
                      Ghost.reveal 'fragment_bytes,
                      B.length (Ghost.reveal 'raw_bytes)))) /\
             (forall (ct:T.content_type).
               IM.content_type_matches content_type ct ==>
               W.parse_tls_message ct (Ghost.reveal 'fragment_bytes) == None))
  returns handled:option ST.server_response
  ensures
    (match handled with
    | None ->
      connection_exactly s 'st0 **
      pts_to raw 'raw_bytes **
      pts_to fragment 'fragment_bytes **
      pts_to network_out 'old_network_out **
      pts_to app_out 'old_app_out
    | Some resp ->
      exists* st1.
        connection_exactly s st1 **
        pts_to raw 'raw_bytes **
        pts_to fragment 'fragment_bytes **
        pts_to network_out 'old_network_out **
        pts_to app_out 'old_app_out **
        pure (
          (exists step.
            st1 ==
              CM.cleartext_handshake_state
                'st0
                step
                (Ghost.reveal 'raw_bytes) /\
            ST.cleartext_handshake_step_correct
              'st0
              st1
              resp
              step
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out) /\
          (ST.server_end_to_end_invariant 'st0 ==>
           ST.server_end_to_end_invariant st1)))
{
  let is_cleartext_handshake = ((not protected) && content_type = 0x16uy);
  if (not is_cleartext_handshake) {
    None #ST.server_response
  } else if (SZ.eq fragment_len 0sz) {
    None #ST.server_response
  } else {
    unfold (connection_exactly s 'st0);
    let ok = CQ.can_buffer_cleartext_handshake s;
    if (not ok) {
      fold (connection_exactly s 'st0);
      None #ST.server_response
    } else {
      let pending = CQ.copy_pending_cleartext_handshake s;
      match pending {
        Some p -> {
          with pending_bytes. assert (
            V.pts_to p.CR.pending_cleartext_fragment pending_bytes);
          (* The reassembly cap is [max_client_hello_len], not the model's
             [max_pending_cleartext_handshake].  A cleartext buffer can only
             ever be drained by a ClientHello (server) or a ServerHello
             (client), and both are bounded by it, so anything larger could
             never complete; capping here also keeps the stream inside
             [parse_tls_message]'s record-fragment bound. *)
          let pending_fits =
            SZ.lte
              p.CR.pending_cleartext_fragment_len
              Bounds.max_client_hello_len_sz;
          if (not pending_fits) {
            V.free p.CR.pending_cleartext_fragment;
            fold (connection_exactly s 'st0);
            None #ST.server_response
          } else {
            let room =
              SZ.sub
                Bounds.max_client_hello_len_sz
                p.CR.pending_cleartext_fragment_len;
            let fits = SZ.lte fragment_len room;
            if (not fits) {
              V.free p.CR.pending_cleartext_fragment;
              fold (connection_exactly s 'st0);
              None #ST.server_response
            } else {
              let stream_len =
                SZ.add p.CR.pending_cleartext_fragment_len fragment_len;
              let stream = V.alloc 0uy stream_len;
              V.to_array_pts_to stream;
              V.to_array_pts_to p.CR.pending_cleartext_fragment;
              SC.copy_array_slice_to_array
                (V.vec_to_array p.CR.pending_cleartext_fragment)
                p.CR.pending_cleartext_fragment_len
                0sz
                p.CR.pending_cleartext_fragment_len
                (V.vec_to_array stream)
                stream_len
                0sz;
              SC.copy_array_slice_to_array
                fragment
                fragment_len
                0sz
                fragment_len
                (V.vec_to_array stream)
                stream_len
                p.CR.pending_cleartext_fragment_len;
              V.to_vec_pts_to p.CR.pending_cleartext_fragment;
              V.free p.CR.pending_cleartext_fragment;
              with stream_bytes. assert (
                pts_to (V.vec_to_array stream) stream_bytes);
              let step = Ghost.hide ({
                CS.cleartext_handshake_fragment = Ghost.reveal 'fragment_bytes;
              } <: CS.cleartext_handshake_step);
              assert (pure (Seq.equal
                (Ghost.reveal stream_bytes)
                (CS.cleartext_handshake_stream
                  'st0.CS.cs_model
                  (Ghost.reveal step))));
              (* THE coalescing decode: the combined stream, not this record's
                 fragment alone, is what has to fail to parse for buffering to
                 be a legal last resort. *)
              let coalesced =
                P.parse_tls_message
                  content_type
                  (V.vec_to_array stream)
                  stream_len;
              match coalesced {
                Some l -> {
                  (* The record COMPLETES a message.  Delivering a reassembled
                     ClientHello is the next increment; for now hand back to
                     the decode-error path rather than buffer a stream that
                     already parses, which the model forbids. *)
                  IM.free_tls_message l;
                  V.to_vec_pts_to stream;
                  V.free stream;
                  fold (connection_exactly s 'st0);
                  None #ST.server_response
                }
                None -> {
                  assert (pure (IM.content_type_matches content_type T.Handshake));
                  assert (pure (W.parse_tls_message
                    T.Handshake
                    (CS.cleartext_handshake_stream
                      'st0.CS.cs_model
                      (Ghost.reveal step)) == None));
                  assert (pure (CS.legal_cleartext_handshake_step
                    'st0.CS.cs_model
                    (Ghost.reveal step)));
                  assert (pure (CS.legal_event
                    'st0.CS.cs_model
                    (CS.ConnCleartextHandshake (Ghost.reveal step))));
                  assert (pure (Some? (CS.step_cleartext_handshake
                    'st0.CS.cs_model
                    (Ghost.reveal step))));
                  lemma_cleartext_record_raw_delta_legal
                    content_type
                    (Ghost.reveal 'fragment_bytes)
                    (Ghost.reveal 'raw_bytes);
                  assert (pure (CS.event_raw_delta_legal
                    'st0.CS.cs_model
                    (CS.ConnCleartextHandshake (Ghost.reveal step))
                    B.empty
                    (Ghost.reveal 'raw_bytes)));

                  Trace.emit Trace.server_cleartext_buffer
                    (SZ.sizet_to_uint64 fragment_len)
                    (SZ.sizet_to_uint64 raw_len)
                    (SZ.sizet_to_uint64 stream_len);
                  CN.buffer_cleartext_handshake_record
                    s raw (V.vec_to_array stream) stream_len #step;
                  V.to_vec_pts_to stream;
                  V.free stream;
                  fold (connection_exactly
                    s
                    (CM.cleartext_handshake_state
                      'st0
                      (Ghost.reveal step)
                      (Ghost.reveal 'raw_bytes)));

                  let resp = {
                    ST.network_out_len = 0sz;
                    ST.app_out_len = 0sz;
                    ST.status = ST.StepOk;
                  };
                  ST.lemma_cleartext_handshake_step_correct_intro
                    'st0
                    resp
                    (Ghost.reveal step)
                    (Ghost.reveal 'raw_bytes)
                    'old_network_out
                    'old_app_out;
                  ST.lemma_cleartext_handshake_step_correct_preserves_end_to_end_invariant_conditional
                    'st0
                    (CM.cleartext_handshake_state
                      'st0
                      (Ghost.reveal step)
                      (Ghost.reveal 'raw_bytes))
                    resp
                    (Ghost.reveal step)
                    (Ghost.reveal 'raw_bytes)
                    'old_network_out
                    'old_app_out;
                  Some resp
                }
              }
            }
          }
        }
        None -> {
          (* The buffer is empty, so the assembled stream is exactly this
             record's fragment -- which the decoder has just told us parses
             as no message at all, discharging the "last resort" conjunct. *)
          assert (pure (CS.cleartext_handshake_buffer_empty 'st0.CS.cs_model));
          let step = Ghost.hide ({
            CS.cleartext_handshake_fragment = Ghost.reveal 'fragment_bytes;
          } <: CS.cleartext_handshake_step);
          assert (pure (Seq.equal
            (CS.cleartext_handshake_stream 'st0.CS.cs_model (Ghost.reveal step))
            (Ghost.reveal 'fragment_bytes)));
          assert (pure (IM.content_type_matches content_type T.Handshake));
          assert (pure (W.parse_tls_message
            T.Handshake
            (CS.cleartext_handshake_stream 'st0.CS.cs_model (Ghost.reveal step)) == None));
          assert (pure (CS.legal_cleartext_handshake_step
            'st0.CS.cs_model
            (Ghost.reveal step)));
          assert (pure (CS.legal_event
            'st0.CS.cs_model
            (CS.ConnCleartextHandshake (Ghost.reveal step))));
          assert (pure (Some? (CS.step_cleartext_handshake
            'st0.CS.cs_model
            (Ghost.reveal step))));
          (* [network_input_wf] pins the outer record: a non-Application_data
             outer type whose fragment is the decoder's, and [content_type]
             says that outer type is Handshake. *)
          lemma_cleartext_record_raw_delta_legal
            content_type
            (Ghost.reveal 'fragment_bytes)
            (Ghost.reveal 'raw_bytes);
          assert (pure (CS.event_raw_delta_legal
            'st0.CS.cs_model
            (CS.ConnCleartextHandshake (Ghost.reveal step))
            B.empty
            (Ghost.reveal 'raw_bytes)));

          Trace.emit Trace.server_cleartext_buffer
            (SZ.sizet_to_uint64 fragment_len)
            (SZ.sizet_to_uint64 raw_len)
            0UL;
          CN.buffer_cleartext_handshake_record
            s raw fragment fragment_len #step;
          fold (connection_exactly
            s
            (CM.cleartext_handshake_state
              'st0
              (Ghost.reveal step)
              (Ghost.reveal 'raw_bytes)));

          let resp = {
            ST.network_out_len = 0sz;
            ST.app_out_len = 0sz;
            ST.status = ST.StepOk;
          };
          ST.lemma_cleartext_handshake_step_correct_intro
            'st0
            resp
            (Ghost.reveal step)
            (Ghost.reveal 'raw_bytes)
            'old_network_out
            'old_app_out;
          ST.lemma_cleartext_handshake_step_correct_preserves_end_to_end_invariant_conditional
            'st0
            (CM.cleartext_handshake_state
              'st0
              (Ghost.reveal step)
              (Ghost.reveal 'raw_bytes))
            resp
            (Ghost.reveal step)
            (Ghost.reveal 'raw_bytes)
            'old_network_out
            'old_app_out;
          Some resp
        }
      }
    }
  }
}

(* Headroom for the per-goal SMT encoding introduced by the fstar2
   simplified effect system: the goals here are unchanged, but they are
   now discharged one at a time against the whole Pulse context. *)
#push-options "--z3rlimit 60"
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
                  app_out_bytes /\
                (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                 W.record_prefix_incomplete (Ghost.reveal 'raw_bytes) /\
                 W.parse_record_wire (Ghost.reveal 'raw_bytes) == None /\
                 Seq.equal network_out_bytes (Ghost.reveal 'old_network_out) /\
                 Seq.equal app_out_bytes (Ghost.reveal 'old_app_out)) /\
                (buffer_resp.ST.response.ST.status == ST.StepOk ==>
                 0 < SZ.v buffer_resp.ST.consumed_len))
{
  Trace.emit Trace.server_network_begin
    (SZ.sizet_to_uint64 raw_len)
    0UL
    0UL;
  unfold (connection_exactly s 'st0);
  let decoded = P.decode_network_buffer s raw raw_len;
  fold (connection_exactly s 'st0);
  match decoded {
    IM.NetworkBufferNeedMoreInput -> {
      Trace.emit Trace.server_network_need_more
        (SZ.sizet_to_uint64 raw_len)
        0UL
        0UL;
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
      assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
        W.record_prefix_incomplete (Ghost.reveal 'raw_bytes) /\
        W.parse_record_wire (Ghost.reveal 'raw_bytes) == None));
      assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
        Seq.equal (Ghost.reveal 'old_network_out) (Ghost.reveal 'old_network_out)));
      assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
        Seq.equal (Ghost.reveal 'old_app_out) (Ghost.reveal 'old_app_out)));
      buffer_resp
    }
    IM.NetworkBufferDecodeError -> {
      Trace.emit Trace.server_network_decode_error
        (SZ.sizet_to_uint64 raw_len)
        0UL
        0UL;
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
      assert (pure (buffer_resp.ST.consumed_len == 0sz));
      assert (pure (resp.ST.network_out_len == 0sz));
      assert (pure (resp.ST.app_out_len == 0sz));
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
      Trace.emit Trace.server_network_record
        (FStar.Int.Cast.uint8_to_uint64
          decoded_buffer.IM.decoded_buffer_content_type)
        (SZ.sizet_to_uint64
          decoded_buffer.IM.decoded_buffer_raw_record_len)
        (SZ.sizet_to_uint64
          decoded_buffer.IM.decoded_buffer_fragment_len);
      with raw_record_bytes fragment_bytes.
        assert (V.pts_to decoded_buffer.IM.decoded_buffer_raw_record raw_record_bytes **
                V.pts_to decoded_buffer.IM.decoded_buffer_fragment fragment_bytes);
      V.to_array_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
      V.to_array_pts_to decoded_buffer.IM.decoded_buffer_fragment;
      match decoded_buffer.IM.decoded_buffer_parsed {
        None -> {
          (* G3: a record whose fragment parses as no message is not
             necessarily malformed -- it may be one piece of a handshake
             message split across records.  Try to set it aside before
             treating it as a decode error. *)
          let handled =
            try_buffer_cleartext_handshake_record
              s
              decoded_buffer.IM.decoded_buffer_protected
              decoded_buffer.IM.decoded_buffer_content_type
              (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record)
              decoded_buffer.IM.decoded_buffer_raw_record_len
              (V.vec_to_array decoded_buffer.IM.decoded_buffer_fragment)
              decoded_buffer.IM.decoded_buffer_fragment_len
              network_out
              network_out_len
              app_out
              app_out_len;
          match handled {
          Some buffered -> {
            let buffer_resp = {
              ST.response = buffered;
              ST.consumed_len = decoded_buffer.IM.decoded_buffer_consumed_len;
            };
            with st1. assert (connection_exactly s st1);
            assert (pure (Seq.equal
              (ST.server_network_consumed_prefix
                buffer_resp
                (Ghost.reveal 'raw_bytes))
              (Ghost.reveal raw_record_bytes)));
            assert (pure (exists step.
              st1 ==
                CM.cleartext_handshake_state
                  'st0
                  step
                  (Ghost.reveal raw_record_bytes) /\
              ST.cleartext_handshake_step_correct
                'st0
                st1
                buffer_resp.ST.response
                step
                (ST.server_network_consumed_prefix
                  buffer_resp
                  (Ghost.reveal 'raw_bytes))
                'old_network_out
                'old_app_out));
            assert (pure (ST.server_network_bytes_end_to_end_correct
              'st0
              st1
              buffer_resp
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out));
            assert (pure (buffer_resp.ST.response.ST.status == ST.StepOk));
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
              'old_network_out
              'old_app_out));
            assert (pure (ST.server_network_connection_failed_consumed_prefix
              'st0
              st1
              buffer_resp
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out));
            assert (pure (ST.server_network_consumed_input_projection
              'st0
              st1
              buffer_resp
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out));
            V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_fragment;
            V.free decoded_buffer.IM.decoded_buffer_fragment;
            V.to_vec_pts_to decoded_buffer.IM.decoded_buffer_raw_record;
            V.free decoded_buffer.IM.decoded_buffer_raw_record;
            buffer_resp
          }
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
            ST.consumed_len = 0sz;
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
          }
        }
        Some l -> {
          match l {
            IM.LTlsHandshake lhs -> {
              Trace.emit Trace.server_handshake_message
                (match lhs with
                 | IM.LClientHello _ -> 1UL
                 | IM.LServerHello _ -> 2UL
                 | IM.LEncryptedExtensions _ -> 8UL
                 | IM.LCertificate _ -> 11UL
                 | IM.LCertificateVerify _ -> 15UL
                 | IM.LFinished _ -> 20UL
                 | IM.LHelloRetryRequest -> 254UL)
                (FStar.Int.Cast.uint8_to_uint64
                  decoded_buffer.IM.decoded_buffer_content_type)
                (SZ.sizet_to_uint64
                  decoded_buffer.IM.decoded_buffer_fragment_len);
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
              assert (pure (CT.received_tls_raw_delta_legal_unbuffered
                'st0
                (M.TlsHandshake (M.ClientHello ch))
                raw_record_bytes));
              unfold (IM.is_valid_client_hello lch ch);
              with random session_id server_name key_share p256_key_share cipher_suites signature_schemes. _;
              CM.lemma_cipher_suites_match_length
                cipher_suites
                (SZ.v lch.IM.client_hello_cipher_suites_len)
                (Sem.clientHello_cipher_suites ch);
              assert (pure (List.length (Sem.clientHello_cipher_suites ch) ==
                SZ.v lch.IM.client_hello_cipher_suites_len));
              assert (pure (List.length (Sem.clientHello_cipher_suites ch) < 65536));
              CM.lemma_bounded_u16_sizet_of_sizet
                (List.length (Sem.clientHello_cipher_suites ch))
                lch.IM.client_hello_cipher_suites_len;
              assert (pure (CM.client_hello_cipher_suites_len_for ch ==
                lch.IM.client_hello_cipher_suites_len));
              CM.lemma_signature_schemes_match_length
                signature_schemes
                (SZ.v lch.IM.client_hello_signature_schemes_len)
                (Some?.v (Sem.clientHello_sig_algs ch));
              assert (pure (List.length (Some?.v (Sem.clientHello_sig_algs ch)) ==
                SZ.v lch.IM.client_hello_signature_schemes_len));
              assert (pure (List.length (Some?.v (Sem.clientHello_sig_algs ch)) < 65536));
              CM.lemma_bounded_u16_sizet_of_sizet
                (List.length (Some?.v (Sem.clientHello_sig_algs ch)))
                lch.IM.client_hello_signature_schemes_len;
              assert (pure (CM.client_hello_signature_schemes_len_for ch ==
                lch.IM.client_hello_signature_schemes_len));
                assert (pure (IM.optional_byte_prefix_matches
                    lch.IM.client_hello_has_server_name
                    server_name
                    lch.IM.client_hello_server_name_len
                    (Sem.clientHello_server_name ch)));
                assert (pure (B.length server_name == IM.max_server_name_len));
                assert (pure (B.length server_name < 65536));
                lemma_client_hello_sni_len_for
                    lch.IM.client_hello_has_server_name
                    server_name
                    lch.IM.client_hello_server_name_len
                    ch;
                assert (pure (SZ.fits Bounds.max_client_hello_len));
                let fragment_fits =
                  CM.sizet_lte_plain
                    decoded_buffer.IM.decoded_buffer_fragment_len
                    Bounds.max_client_hello_len_sz;
                CM.lemma_sizet_lte_plain
                  decoded_buffer.IM.decoded_buffer_fragment_len
                  Bounds.max_client_hello_len_sz;
                fold (IM.is_valid_client_hello lch ch);
                if fragment_fits {
                  assert (pure (SZ.v decoded_buffer.IM.decoded_buffer_fragment_len <=
                    Bounds.max_client_hello_len));
                  unfold (connection_exactly s 'st0);
                  let can_receive =
                    CQ.can_receive_client_hello
                      s
                      decoded_buffer.IM.decoded_buffer_fragment_len
                      #ch
                      #'st0;
                  // The model's received-ClientHello raw-delta rule is
                  // buffer-relative: this record reads as the WHOLE message
                  // only when nothing is set aside.  A non-empty buffer means
                  // the record continues a message still being assembled.
                  let buffer_empty = CQ.cleartext_handshake_buffer_empty_runtime s;
                  fold (connection_exactly s 'st0);
                  let ready = can_receive && buffer_empty;
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
              assert (pure (CT.received_tls_raw_delta_legal_unbuffered
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
              assert (pure (TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection
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
                assert (pure (TLS13.Spec.StateMachine.KeyMaterial.record_read_key_schedule_projection_for_role
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
            assert (pure (CT.received_tls_raw_delta_legal_unbuffered
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
            assert (pure (TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection
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
                assert (pure (TLS13.Spec.StateMachine.KeyMaterial.record_read_key_schedule_projection_for_role
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
              assert (pure (Ghost.reveal parsed_alert == T.Close_notify));
              assert (pure (IM.alert_description_matches alert T.Close_notify));
              assert (pure (CT.parsed_message_wire_success_for
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (IM.LTlsAlert alert)
                (M.TlsAlert T.Close_notify)));
              assert (pure (CT.wire_parse_success
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (M.TlsAlert T.Close_notify)));
              assert (pure (CT.received_tls_raw_delta_legal_unbuffered
                'st0
                (M.TlsAlert T.Close_notify)
                raw_record_bytes));
              CT.lemma_parsed_message_network_input_projection
                'st0
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (IM.LTlsAlert alert)
                (M.TlsAlert T.Close_notify)
                raw_record_bytes;
              assert (pure (CT.network_input_message_projection
                'st0
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (M.TlsAlert T.Close_notify)
                raw_record_bytes));
              assert (pure (CS.network_message_is_cleartext
                CL.Received
                (M.TlsAlert T.Close_notify) == false));
              assert (pure (CT.protected_record_decodes_to_message
                'st0
                raw_record_bytes
                (M.TlsAlert T.Close_notify)));
              CT.lemma_protected_record_decodes_to_received_single_decode
                'st0
                raw_record_bytes
                (M.TlsAlert T.Close_notify);
              assert (pure (TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection
                'st0.CS.cs_model
                (ST.received_message_event
                  (M.TlsAlert T.Close_notify))
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
                  (M.TlsAlert T.Close_notify)
                  raw_record_bytes
                  network_out_bytes
                  app_out_bytes));
                ST.lemma_server_state_correct_record_read_key_schedule_projection
                  'st0;
                assert (pure (TLS13.Spec.StateMachine.KeyMaterial.record_read_key_schedule_projection_for_role
                  CS.ServerEndpoint
                  'st0.CS.cs_model));
                assert (pure (ST.server_protected_record_decode_uses_scheduled_read_key
                  'st0
                  raw_record_bytes));
                assert (pure (ST.server_protected_record_decode_correct
                  'st0
                  raw_record_bytes
                  (M.TlsAlert T.Close_notify)));
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
              assert (pure (Ghost.reveal parsed_alert <> T.Close_notify));
              assert (pure (CT.parsed_message_wire_success_for
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (IM.LTlsAlert alert)
                (M.TlsAlert (Ghost.reveal parsed_alert))));
              assert (pure (CT.wire_parse_success
                decoded_buffer.IM.decoded_buffer_content_type
                fragment_bytes
                (M.TlsAlert (Ghost.reveal parsed_alert))));
              assert (pure (CT.received_tls_raw_delta_legal_unbuffered
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
              assert (pure (TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection
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
            assert (pure (CT.received_tls_raw_delta_legal_unbuffered
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
            with m. assert (pure True);
            unfold (IM.is_valid_tls_message (IM.LTlsKeyUpdate lreq) m);
            with req. _;
            assert (pure (m == M.TlsKeyUpdate req));
            assert (pure (CT.parsed_message_wire_success_for
              decoded_buffer.IM.decoded_buffer_content_type
              fragment_bytes
              (IM.LTlsKeyUpdate lreq)
              (M.TlsKeyUpdate req)));
            assert (pure (CT.wire_parse_success
              decoded_buffer.IM.decoded_buffer_content_type
              fragment_bytes
              (M.TlsKeyUpdate req)));
            assert (pure (CT.received_tls_raw_delta_legal_unbuffered
              'st0
              (M.TlsKeyUpdate req)
              raw_record_bytes));
            CT.lemma_parsed_message_network_input_projection
              'st0
              decoded_buffer.IM.decoded_buffer_content_type
              fragment_bytes
              (IM.LTlsKeyUpdate lreq)
              (M.TlsKeyUpdate req)
              raw_record_bytes;
            assert (pure (CS.network_message_is_cleartext
              CL.Received
              (M.TlsKeyUpdate req) == false));
            assert (pure (CT.protected_record_decodes_to_message
              'st0
              raw_record_bytes
              (M.TlsKeyUpdate req)));
            CT.lemma_protected_record_decodes_to_received_single_decode
              'st0
              raw_record_bytes
              (M.TlsKeyUpdate req);
            assert (pure (TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection
              'st0.CS.cs_model
              (ST.received_message_event
                (M.TlsKeyUpdate req))
              raw_record_bytes));
            assert (pure (IM.key_update_request_matches lreq req));
            let requested = lreq = 1uy;
            if requested {
              assert (pure (req == M.UpdateRequested));
            } else {
              assert (pure (requested == false));
              assert (pure (req == M.UpdateNotRequested));
            };
            unfold (connection_exactly s 'st0);
            let ready =
              CQ.can_receive_endpoint_application_data
                s
                #'st0;
            fold (connection_exactly s 'st0);
            if ready {
              assert (pure ('st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
              assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
              (* On a server the read direction names the *client* traffic
                 label, which is precisely the slot [process_key_update]
                 rotates. *)
              assert (pure (CS.application_traffic_available_for_role
                CS.ServerEndpoint
                'st0.CS.cs_model.CS.model_handshake
                CL.Received));
              assert (pure (Some?
                'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
              assert (pure (U64.fits ('st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
              let resp =
                process_key_update
                  s
                  (V.vec_to_array decoded_buffer.IM.decoded_buffer_raw_record)
                  decoded_buffer.IM.decoded_buffer_raw_record_len
                  requested
                  #req
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
              assert (pure (st1 ==
                CM.server_received_key_update_state
                  'st0
                  req
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
                (M.TlsKeyUpdate req)
                raw_record_bytes
                network_out_bytes
                app_out_bytes));
              ST.lemma_server_state_correct_record_read_key_schedule_projection
                'st0;
              assert (pure (ST.server_protected_record_decode_correct
                'st0
                raw_record_bytes
                (M.TlsKeyUpdate req)));
              assert (pure (ST.server_network_step_ok_received_decode_projection
                'st0
                st1
                buffer_resp
                (Ghost.reveal 'raw_bytes)
                network_out_bytes
                app_out_bytes));
              assert (pure (ST.server_network_step_ok_consumed_prefix
                'st0
                st1
                buffer_resp
                (Ghost.reveal 'raw_bytes)));
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
        }
      }
    }
  }
}
}

#pop-options
