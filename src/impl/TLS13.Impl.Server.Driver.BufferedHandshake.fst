module TLS13.Impl.Server.Driver.BufferedHandshake

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BT = Common.BufferedTCP
module CI = Common.ChannelImplementation
module CL = TLS13.ConnectionLog
module CM = TLS13.Impl.ConnectionState.Model
module CPI = Common.ProtocolImplementation
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CryptoSpec = TLS13.Crypto.Spec
module BN = TLS13.Impl.Server.Driver.BufferedNetwork
module DS = TLS13.Impl.Server.Driver.State
module Mat = TLS13.Impl.Server.Material
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module SP = TLS13.Impl.Server.CanonicalProtocol
module S = TLS13.Impl.Server
module SSetup = TLS13.Impl.Server.Setup
module Seq = FStar.Seq
module SS = TLS13.Impl.Server.Send
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8

ghost
fn tcp_history_note_write
  (hist:MR.mref CI.io_history_preorder)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (chunk:Ghost.erased B.bytes)
  requires
    MR.pts_to hist #1.0R
      (DS.server_driver_history
        (Ghost.reveal received)
        (Ghost.reveal sent))
  ensures
    MR.pts_to hist #1.0R
      (DS.server_driver_history
        (Ghost.reveal received)
        (Seq.append (Ghost.reveal sent) (Ghost.reveal chunk)))
{
  CPI.lemma_bytes_extends_refl (Ghost.reveal received);
  CPI.lemma_bytes_extends_append
    (Ghost.reveal sent)
    (Ghost.reveal chunk);
  CI.lemma_io_history_preorder_of_extends
    (DS.server_driver_history
      (Ghost.reveal received)
      (Ghost.reveal sent))
    (DS.server_driver_history
      (Ghost.reveal received)
      (Seq.append (Ghost.reveal sent) (Ghost.reveal chunk)));
  MR.update hist
    (DS.server_driver_history
      (Ghost.reveal received)
      (Seq.append (Ghost.reveal sent) (Ghost.reveal chunk)))
}

let lemma_select_server_parameters_ready_can_select
  (st:CS.connection_state)
  (payload:B.bytes)
  : Lemma
      (requires
        ST.server_local_event_input_ready
          st
          ST.LocalSelectServerParameters
          payload)
      (ensures
        CM.can_select_server_parameters
          st
          {
            CS.server_selected_client_hello =
              Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_hello;
            CS.server_selected_cipher_suite =
              T.TLS_CHACHA20_POLY1305_SHA256;
            CS.server_selected_group = T.X25519;
            CS.server_selected_signature_scheme =
              T.Rsa_pss_rsae_sha256;
            CS.server_random = CL.raw_slice payload 0 32;
            CS.server_key_share_private =
              Some (CL.raw_slice payload 32 64);
            CS.server_key_share_public =
              CryptoSpec.x25519_public_from_private
                (CL.raw_slice payload 32 64);
            CS.server_selected_credential =
              (Some?.v st.CS.cs_model.CS.model_config.CS.config_server).
                CS.server_credential_identity;
          })
=
  ()

let lemma_select_server_parameters_call_ready
  (st:CS.connection_state)
  (payload network_out app_out:B.bytes)
  : Lemma
      (requires
        ST.server_local_event_input_ready
          st
          ST.LocalSelectServerParameters
          payload /\
        ST.server_end_to_end_invariant st /\
        B.length network_out == SZ.v DS.driver_network_out_capacity /\
        B.length app_out == SZ.v DS.driver_app_out_capacity)
      (ensures
        B.length (CL.raw_slice payload 0 32) == 32 /\
        B.length (CL.raw_slice payload 32 64) == 32 /\
        CR.server_selection_absent st.CS.cs_model.CS.model_handshake /\
        Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
        Some? st.CS.cs_model.CS.model_config.CS.config_server /\
        CM.can_select_server_parameters
          st
          {
            CS.server_selected_client_hello =
              Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_hello;
            CS.server_selected_cipher_suite =
              T.TLS_CHACHA20_POLY1305_SHA256;
            CS.server_selected_group = T.X25519;
            CS.server_selected_signature_scheme =
              T.Rsa_pss_rsae_sha256;
            CS.server_random = CL.raw_slice payload 0 32;
            CS.server_key_share_private =
              Some (CL.raw_slice payload 32 64);
            CS.server_key_share_public =
              CryptoSpec.x25519_public_from_private
                (CL.raw_slice payload 32 64);
            CS.server_selected_credential =
              (Some?.v st.CS.cs_model.CS.model_config.CS.config_server).
                CS.server_credential_identity;
          })
=
  lemma_select_server_parameters_ready_can_select st payload;
  Seq.lemma_len_slice payload 0 32;
  Seq.lemma_len_slice payload 32 64

let lemma_started_server_not_failed
  (st:CS.connection_state)
  : Lemma
      (requires CM.can_start_server st)
      (ensures
        ST.server_connection_control_not_failed
          (CM.started_server_state st))
=
  match st.CS.cs_model.CS.model_control with
  | CS.ControlNew -> ()
  | _ -> assert False

let lemma_supported_profile_selection_started
  (st:CS.connection_state)
  (credential_identity:CS.server_credential_identity)
  : Lemma
      (requires
        CM.can_start_server st /\
        DS.server_driver_supported_profile_selection st credential_identity)
      (ensures
        DS.server_driver_supported_profile_selection
          (CM.started_server_state st)
          credential_identity)
=
  match st.CS.cs_model.CS.model_control with
  | CS.ControlNew ->
    match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
    | Some selection -> ()
    | None -> ()
  | _ -> assert False

fn start_server_once
  (d:DS.buffered_driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len **
    pts_to empty_payload 'empty_payload_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'empty_payload_bytes == 0 /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len /\
      CM.can_start_server 'st0)
  returns resp:ST.server_response
  ensures
    exists* network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        (CM.started_server_state 'st0)
        'certificate_chain
        'credential_identity
        'buffered
        'buffered_len **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len)
{
  unfold (DS.buffered_driver_exactly
    d 'st0 'certificate_chain 'credential_identity 'buffered 'buffered_len);
  with model received committed sent.
    assert (DS.buffered_driver_indexed
      d 'st0 'certificate_chain 'credential_identity
      'buffered 'buffered_len model received committed sent);
  unfold (DS.buffered_driver_indexed
    d 'st0 'certificate_chain 'credential_identity
    'buffered 'buffered_len model received committed sent);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  rewrite
    (S.connection_exactly d.buffered_driver_server 'st0)
    as
    (SSetup.connection_exactly d.buffered_driver_server 'st0);
  let resp =
    SSetup.process_start_server_local_event
      d.buffered_driver_server
      ST.LocalStartServer
      empty_payload
      0sz
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (
      SSetup.connection_exactly d.buffered_driver_server st1 **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes);
  rewrite
    (SSetup.connection_exactly d.buffered_driver_server st1)
    as
    (S.connection_exactly d.buffered_driver_server st1);
  assert (pure (st1 == CM.started_server_state 'st0));
  rewrite
    (S.connection_exactly d.buffered_driver_server st1)
    as
    (S.connection_exactly
      d.buffered_driver_server
      (CM.started_server_state 'st0));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.started_server_state 'st0)
    resp
    ST.LocalStartServer
    (Ghost.reveal 'empty_payload_bytes)
    network_out_bytes
    app_out_bytes));
  unfold (DS.buffered_driver_canonical_progress d 'st0);
  SP.lemma_server_local_event_progress
    'st0
    (CM.started_server_state 'st0)
    resp
    ST.LocalStartServer
    (Ghost.reveal 'empty_payload_bytes)
    network_out_bytes
    app_out_bytes;
  MR.update
    d.buffered_driver_progress
    (CM.started_server_state 'st0);
  fold (DS.buffered_driver_canonical_progress
    d
    (CM.started_server_state 'st0));
  lemma_started_server_not_failed 'st0;
  lemma_supported_profile_selection_started
    'st0
    (Ghost.reveal 'credential_identity);
  assert (pure ((CM.started_server_state 'st0).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure (DS.server_driver_config_matches_credentials
    (CM.started_server_state 'st0)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  assert (pure (Seq.equal
    (CM.started_server_state 'st0).CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received));
  assert (pure (Seq.equal
    (CM.started_server_state 'st0).CS.cs_wire_log.CL.raw_sent
    'st0.CS.cs_wire_log.CL.raw_sent));
  assert (pure (DS.server_driver_wire_logs_match_witness
    (CM.started_server_state 'st0)
    received
    sent
    committed
    (BT.pending model)
    'buffered_len));
  fold (DS.buffered_driver_indexed
    d
    (CM.started_server_state 'st0)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (BT.pending model)
    'buffered_len
    model
    received
    committed
    sent);
  rewrite
    (DS.buffered_driver_indexed
      d
      (CM.started_server_state 'st0)
      (Ghost.reveal 'certificate_chain)
      (Ghost.reveal 'credential_identity)
      (BT.pending model)
      'buffered_len
      model
      received
      committed
      sent)
    as
    (DS.buffered_driver_indexed
      d
      (CM.started_server_state 'st0)
      (Ghost.reveal 'certificate_chain)
      (Ghost.reveal 'credential_identity)
      (Ghost.reveal 'buffered)
      'buffered_len
      model
      received
      committed
      sent);
  fold (DS.buffered_driver_exactly
    d
    (CM.started_server_state 'st0)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal 'buffered)
    'buffered_len);
  resp
}

fn select_default_server_parameters_from_payload_once
  (d:DS.buffered_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len **
    pts_to payload 'payload_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'payload_bytes == SZ.v payload_len /\
      SZ.v payload_len == 64 /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len /\
      network_out_len == DS.driver_network_out_capacity /\
      app_out_len == DS.driver_app_out_capacity /\
      ST.server_local_event_input_ready
        'st0
        ST.LocalSelectServerParameters
        (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures
    exists* st1 network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        'buffered
        'buffered_len **
      pts_to payload 'payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len /\
        selection_from_payload_correct
          'st0
          st1
          (Ghost.reveal 'payload_bytes))
{
  unfold (DS.buffered_driver_exactly
    d 'st0 'certificate_chain 'credential_identity 'buffered 'buffered_len);
  with model received committed sent.
    assert (DS.buffered_driver_indexed
      d 'st0 'certificate_chain 'credential_identity
      'buffered 'buffered_len model received committed sent);
  unfold (DS.buffered_driver_indexed
    d 'st0 'certificate_chain 'credential_identity
    'buffered 'buffered_len model received committed sent);
  lemma_select_server_parameters_call_ready
    'st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'old_network_out)
    (Ghost.reveal 'old_app_out);
  let mut server_random = [| 0uy; 32sz |];
  let mut server_private_key = [| 0uy; 32sz |];
  Mat.copy_server_random_and_private_from_payload
    payload
    server_random
    server_private_key;
  with server_random_bytes.
    assert (pts_to server_random server_random_bytes);
  with server_private_key_bytes.
    assert (pts_to server_private_key server_private_key_bytes);
  assert (pure (Seq.equal
    server_random_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32)));
  assert (pure (Seq.equal
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64)));
  Seq.lemma_eq_elim
    server_random_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32);
  Seq.lemma_eq_elim
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64);
  let resp =
    S.process_select_default_server_parameters_with_derived_public_from_private_array
      d.buffered_driver_server
      server_random
      server_private_key
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (
      S.connection_exactly d.buffered_driver_server st1 **
      pts_to server_random server_random_bytes **
      pts_to server_private_key server_private_key_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes);
  assert (pure (selection_from_payload_correct
    'st0 st1 (Ghost.reveal 'payload_bytes)));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    st1
    resp
    ST.LocalSelectServerParameters
    B.empty
    network_out_bytes
    app_out_bytes));
  unfold (DS.buffered_driver_canonical_progress d 'st0);
  SP.lemma_server_local_event_progress
    'st0
    st1
    resp
    ST.LocalSelectServerParameters
    B.empty
    network_out_bytes
    app_out_bytes;
  MR.update d.buffered_driver_progress st1;
  fold (DS.buffered_driver_canonical_progress d st1);
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure (DS.server_driver_config_matches_credentials
    st1
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  assert (pure (Some?
    st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
  assert (pure (
    (Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection).
      CS.server_selected_signature_scheme ==
      T.Rsa_pss_rsae_sha256));
  assert (pure (
    (Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection).
      CS.server_selected_credential ==
      (Ghost.reveal 'credential_identity)));
  assert (pure (DS.server_driver_supported_profile_selection
    st1
    (Ghost.reveal 'credential_identity)));
  assert (pure (ST.server_end_to_end_invariant st1));
  assert (pure (ST.server_connection_control_not_failed st1));
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received));
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    'st0.CS.cs_wire_log.CL.raw_sent));
  assert (pure (DS.server_driver_wire_logs_match_witness
    st1
    received
    sent
    committed
    (BT.pending model)
    'buffered_len));
  fold (DS.buffered_driver_indexed
    d
    st1
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (BT.pending model)
    'buffered_len
    model
    received
    committed
    sent);
  rewrite
    (DS.buffered_driver_indexed
      d st1
      (Ghost.reveal 'certificate_chain)
      (Ghost.reveal 'credential_identity)
      (BT.pending model)
      'buffered_len
      model received committed sent)
    as
    (DS.buffered_driver_indexed
      d st1
      (Ghost.reveal 'certificate_chain)
      (Ghost.reveal 'credential_identity)
      (Ghost.reveal 'buffered)
      'buffered_len
      model received committed sent);
  fold (DS.buffered_driver_exactly
    d st1
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal 'buffered)
    'buffered_len);
  resp
}

fn send_server_hello_from_payload_once
  (d:DS.buffered_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len **
    pts_to payload 'payload_bytes **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'payload_bytes == SZ.v payload_len /\
      SZ.v payload_len == 64 /\
      B.length 'old_app_out == SZ.v app_out_len /\
      ST.server_local_event_input_ready
        'st0
        ST.LocalSendServerHello
        (Ghost.reveal 'payload_bytes) /\
      (Seq.length (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32) == 32 ==>
       (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32 <: Seq.lseq U8.t 32) <>
         TLS13.Wire.Generated.ServerHello_body.serverHello_body_cst) /\
      (let sh =
         SS.mk_server_hello_witness
           (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32)
           (CryptoSpec.x25519_public_from_private
             (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64))
           T.TLS_CHACHA20_POLY1305_SHA256 in
       CM.can_send_server_hello
         'st0
         sh
         (CS.serialized_cleartext_tls_message
           (M.TlsHandshake (M.ServerHello sh)))))
  returns resp:ST.server_response
  ensures
    exists* st1 app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        'buffered
        'buffered_len **
      pts_to payload 'payload_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length app_out_bytes == SZ.v app_out_len /\
        server_hello_from_payload_correct
          'st0
          st1
          (Ghost.reveal 'payload_bytes) /\
        ST.server_local_event_end_to_end_correct
          'st0
          st1
          resp
          ST.LocalSendServerHello
          (Ghost.reveal 'payload_bytes)
          (CS.serialized_cleartext_tls_message
            (M.TlsHandshake
              (M.ServerHello
                (SS.mk_server_hello_witness
                  (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32)
                  (CryptoSpec.x25519_public_from_private
                    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64))
                  T.TLS_CHACHA20_POLY1305_SHA256))))
          app_out_bytes)
{
  unfold (DS.buffered_driver_exactly
    d 'st0 'certificate_chain 'credential_identity 'buffered 'buffered_len);
  with model received committed sent.
    assert (DS.buffered_driver_indexed
      d 'st0 'certificate_chain 'credential_identity
      'buffered 'buffered_len model received committed sent);
  unfold (DS.buffered_driver_indexed
    d 'st0 'certificate_chain 'credential_identity
    'buffered 'buffered_len model received committed sent);
  let mut server_random = [| 0uy; 32sz |];
  let mut server_private_key = [| 0uy; 32sz |];
  Mat.copy_server_random_and_private_from_payload
    payload
    server_random
    server_private_key;
  with server_random_bytes.
    assert (pts_to server_random server_random_bytes);
  with server_private_key_bytes.
    assert (pts_to server_private_key server_private_key_bytes);
  let mut server_hello_out = [| 0uy; 95sz |];
  with old_server_hello_out.
    assert (pts_to server_hello_out old_server_hello_out);
  assert (pure (Seq.equal
    server_random_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32)));
  assert (pure (Seq.equal
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64)));
  Seq.lemma_eq_elim
    server_random_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32);
  Seq.lemma_eq_elim
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64);
  let resp =
    S.process_send_server_hello_with_derived_public_from_private_array
      d.buffered_driver_server
      server_random
      server_private_key
      server_hello_out
      95sz
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (
      S.connection_exactly d.buffered_driver_server st1 **
      pts_to server_random server_random_bytes **
      pts_to server_private_key server_private_key_bytes **
      pts_to server_hello_out network_out_bytes **
      pts_to app_out app_out_bytes);
  let sh =
    Ghost.hide
      (SS.mk_server_hello_witness
        server_random_bytes
        (CryptoSpec.x25519_public_from_private server_private_key_bytes)
        T.TLS_CHACHA20_POLY1305_SHA256);
  let serialized =
    Ghost.hide
      (CS.serialized_cleartext_tls_message
        (M.TlsHandshake (M.ServerHello (Ghost.reveal sh))));
  assert (pure (Seq.equal network_out_bytes (Ghost.reveal serialized)));
  Seq.lemma_eq_elim network_out_bytes (Ghost.reveal serialized);
  assert (pure (st1 ==
    CM.sent_server_hello_state
      'st0
      (Ghost.reveal sh)
      (Ghost.reveal serialized)));
  assert (pure (server_hello_from_payload_correct
    'st0 st1 (Ghost.reveal 'payload_bytes)));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0 st1 resp ST.LocalSendServerHello B.empty
    network_out_bytes app_out_bytes));
  ST.lemma_local_send_server_hello_payload_irrelevant
    'st0
    st1
    resp
    B.empty
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0 st1 resp ST.LocalSendServerHello
    (Ghost.reveal 'payload_bytes)
    network_out_bytes app_out_bytes));
  DS.lemma_local_event_wire_lengths
    'st0
    st1
    resp
    ST.LocalSendServerHello
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  let written =
    BT.write
      d.buffered_driver_channel
      server_hello_out
      resp.ST.network_out_len;
  assert (pure (written == resp.ST.network_out_len));
  let sent_delta =
    Ghost.hide (ST.response_network_out resp network_out_bytes);
  assert (pure (Seq.equal
    (if SZ.v written <= B.length network_out_bytes
     then Seq.slice network_out_bytes 0 (SZ.v written)
     else B.empty)
    (Ghost.reveal sent_delta)));
  Seq.lemma_eq_elim
    (if SZ.v written <= B.length network_out_bytes
     then Seq.slice network_out_bytes 0 (SZ.v written)
     else B.empty)
    (Ghost.reveal sent_delta);
  rewrite
    (BT.is_buffered
      d.buffered_driver_channel
      model
      received
      committed
      (B.append sent
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty)))
    as
    (BT.is_buffered
      d.buffered_driver_channel
      model
      received
      committed
      (B.append sent (Ghost.reveal sent_delta)));
  tcp_history_note_write
    d.buffered_driver_tcp_history
    (Ghost.hide received)
    (Ghost.hide sent)
    sent_delta;
  let sent' = Ghost.hide (B.append sent (Ghost.reveal sent_delta));
  rewrite
    (BT.is_buffered
      d.buffered_driver_channel
      model
      received
      committed
      (B.append sent (Ghost.reveal sent_delta)))
    as
    (BT.is_buffered
      d.buffered_driver_channel
      model
      received
      committed
      (Ghost.reveal sent'));
  rewrite
    (MR.pts_to
      d.buffered_driver_tcp_history
      #1.0R
      (DS.server_driver_history
        received
        (B.append sent (Ghost.reveal sent_delta))))
    as
    (MR.pts_to
      d.buffered_driver_tcp_history
      #1.0R
      (DS.server_driver_history received (Ghost.reveal sent')));
  assert (pure (Seq.equal sent 'st0.CS.cs_wire_log.CL.raw_sent));
  Seq.lemma_eq_elim sent 'st0.CS.cs_wire_log.CL.raw_sent;
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (B.append 'st0.CS.cs_wire_log.CL.raw_sent
      (Ghost.reveal sent_delta))));
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received));
  Seq.lemma_eq_elim
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received;
  DS.lemma_server_local_event_received_exact_when_nonfailed
    'st0
    st1
    resp
    ST.LocalSendServerHello
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes
    received
    sent
    committed
    (BT.pending model)
    'buffered_len;
  assert (pure (DS.server_driver_wire_logs_match_witness
    st1 received (Ghost.reveal sent') committed
    (BT.pending model) 'buffered_len));
  unfold (DS.buffered_driver_canonical_progress d 'st0);
  SP.lemma_server_local_event_progress
    'st0
    st1
    resp
    ST.LocalSendServerHello
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  MR.update d.buffered_driver_progress st1;
  fold (DS.buffered_driver_canonical_progress d st1);
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure (DS.server_driver_config_matches_credentials
    st1
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  assert (pure (
    st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
    'st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
  assert (pure (DS.server_driver_supported_profile_selection
    st1
    (Ghost.reveal 'credential_identity)));
  fold (DS.buffered_driver_indexed
    d st1
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (BT.pending model)
    'buffered_len
    model
    received
    committed
    (Ghost.reveal sent'));
  rewrite
    (DS.buffered_driver_indexed
      d st1
      (Ghost.reveal 'certificate_chain)
      (Ghost.reveal 'credential_identity)
      (BT.pending model)
      'buffered_len
      model received committed (Ghost.reveal sent'))
    as
    (DS.buffered_driver_indexed
      d st1
      (Ghost.reveal 'certificate_chain)
      (Ghost.reveal 'credential_identity)
      (Ghost.reveal 'buffered)
      'buffered_len
      model received committed (Ghost.reveal sent'));
  fold (DS.buffered_driver_exactly
    d st1
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal 'buffered)
    'buffered_len);
  resp
}

let lemma_derive_shared_secret_ready_with_credentials
  (st:CS.connection_state)
  (payload certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : Lemma
      (requires
        ST.server_local_event_input_ready
          st
          ST.LocalDeriveSharedSecret
          payload)
      (ensures
        ST.server_local_event_input_ready_with_credentials
          st
          ST.LocalDeriveSharedSecret
          payload
          certificate_chain
          credential_identity)
=
  ()

fn derive_shared_secret_from_payload_once
  (d:DS.buffered_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len **
    pts_to payload 'payload_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'payload_bytes == SZ.v payload_len /\
      SZ.v payload_len == 64 /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len /\
      ST.server_local_event_input_ready
        'st0
        ST.LocalDeriveSharedSecret
        (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64))
  returns resp:ST.server_response
  ensures
    exists* st1 network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        'buffered
        'buffered_len **
      pts_to payload 'payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len /\
        ST.server_local_event_end_to_end_correct
          'st0
          st1
          resp
          ST.LocalDeriveSharedSecret
          (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64)
          network_out_bytes
          app_out_bytes /\
        derive_shared_secret_from_payload_correct
          'st0
          st1
          resp
          (Ghost.reveal 'payload_bytes))
{
  let mut server_random = [| 0uy; 32sz |];
  let mut server_private_key = [| 0uy; 32sz |];
  Mat.copy_server_random_and_private_from_payload
    payload
    server_random
    server_private_key;
  with server_private_key_bytes.
    assert (pts_to server_private_key server_private_key_bytes);
  assert (pure (Seq.equal
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64)));
  Seq.lemma_eq_elim
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64);
  lemma_derive_shared_secret_ready_with_credentials
    'st0
    server_private_key_bytes
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity);
  assert (pure (BN.local_event_ready
    'st0
    ST.LocalDeriveSharedSecret
    server_private_key_bytes
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  let result =
    BN.process_local_event
      d
      ST.LocalDeriveSharedSecret
      server_private_key
      32sz
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (
      DS.buffered_driver_exactly
        d st1 'certificate_chain 'credential_identity 'buffered 'buffered_len **
      pts_to server_private_key server_private_key_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes);
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    st1
    result.BN.local_write_resp
    ST.LocalDeriveSharedSecret
    server_private_key_bytes
    network_out_bytes
    app_out_bytes));
  assert (pure (BN.local_event_success_correct
    'st0
    st1
    result.BN.local_write_resp
    ST.LocalDeriveSharedSecret
    server_private_key_bytes));
  assert (pure (derive_shared_secret_from_payload_correct
    'st0
    st1
    result.BN.local_write_resp
    (Ghost.reveal 'payload_bytes)));
  result.BN.local_write_resp
}
