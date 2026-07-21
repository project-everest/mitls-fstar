module TLS13.Impl.Server.Driver.Handshake

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module CM = TLS13.Impl.ConnectionState.Model
module CPI = Common.ProtocolImplementation
module CQ = TLS13.Impl.ConnectionState.Queries
module CR = TLS13.Impl.ConnectionState.Repr
module ID = FStar.IndefiniteDescription
module DN = TLS13.Impl.Server.Driver.Network
module IO = Common.TCP
module Mat = TLS13.Impl.Server.Material
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Seq = FStar.Seq
module S = TLS13.Impl.Server
module SP = TLS13.Impl.Server.CanonicalProtocol
module ST = TLS13.Impl.Server.Types
module Box = Pulse.Lib.Box
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec
module Sem = TLS13.Wire.Semantics
module SS = TLS13.Impl.Server.Send
module GSHbody = TLS13.Wire.Generated.ServerHello_body

open TLS13.Impl.Server.Driver.State

let lemma_some_default_server_parameters_state
    (st0 st1:CS.connection_state)
    (server_random server_private_key:B.bytes_of_len 32)
    : Lemma
        (requires
          Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
          Some? st0.CS.cs_model.CS.model_config.CS.config_server /\
          (match
             st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
             st0.CS.cs_model.CS.model_config.CS.config_server
           with
           | Some ch, Some cfg ->
             st1 == CM.selected_server_parameters_state st0 {
               CS.server_selected_client_hello = ch;
               CS.server_selected_cipher_suite =
                 T.TLS_CHACHA20_POLY1305_SHA256;
               CS.server_selected_group = T.X25519;
               CS.server_selected_signature_scheme =
                 T.Rsa_pss_rsae_sha256;
               CS.server_random = server_random;
               CS.server_key_share_private = Some server_private_key;
               CS.server_key_share_public =
                 CryptoSpec.x25519_public_from_private server_private_key;
               CS.server_selected_credential =
                 cfg.CS.server_credential_identity;
             }
           | _ -> True))
        (ensures
          st1 == CM.selected_server_parameters_state st0 {
            CS.server_selected_client_hello =
              Some?.v
                st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello;
            CS.server_selected_cipher_suite =
              T.TLS_CHACHA20_POLY1305_SHA256;
            CS.server_selected_group = T.X25519;
            CS.server_selected_signature_scheme =
              T.Rsa_pss_rsae_sha256;
            CS.server_random = server_random;
            CS.server_key_share_private = Some server_private_key;
            CS.server_key_share_public =
              CryptoSpec.x25519_public_from_private server_private_key;
            CS.server_selected_credential =
              (Some?.v
                st0.CS.cs_model.CS.model_config.CS.config_server).
                  CS.server_credential_identity;
          })
=
  match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
        st0.CS.cs_model.CS.model_config.CS.config_server with
  | Some _, Some _ -> ()
  | _ -> assert False

let lemma_client_hello_received_selection_present
  (st:CS.connection_state)
  : Lemma
      (requires
        st.CS.cs_model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived)
      (ensures server_driver_selection_present_when_required st)
=
  match st.CS.cs_model.CS.model_control with
  | CS.ControlHandshaking stage ->
    match stage with
    | CS.HsClientHelloReceived -> ()
    | _ -> assert False

let lemma_client_hello_received_not_failed
    (st:CS.connection_state)
    : Lemma
        (requires
          st.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived)
        (ensures ST.server_connection_control_not_failed st)
=
    match st.CS.cs_model.CS.model_control with
    | CS.ControlHandshaking stage ->
      match stage with
      | CS.HsClientHelloReceived -> ()
      | _ -> assert False
    | _ -> assert False
  | _ -> assert False

let lemma_selected_server_parameters_state_wire_log
    (st:CS.connection_state)
    (selection:CS.server_handshake_selection)
    : Lemma
        (ensures
          Seq.equal
            (CM.selected_server_parameters_state
              st
              selection).CS.cs_wire_log.CL.raw_sent
            st.CS.cs_wire_log.CL.raw_sent /\
          Seq.equal
            (CM.selected_server_parameters_state
              st
              selection).CS.cs_wire_log.CL.raw_received
            st.CS.cs_wire_log.CL.raw_received)
=
  CL.lemma_append_empty_right st.CS.cs_wire_log.CL.raw_sent;
  CL.lemma_append_empty_right st.CS.cs_wire_log.CL.raw_received

let lemma_server_driver_wire_logs_match_witness_sent
    (st0 st1:CS.connection_state)
    (received sent0 sent1 consumed buffered:B.bytes)
    (buffered_len:SZ.t)
    : Lemma
        (requires
          server_driver_wire_logs_match_witness
            st0 received sent0 consumed buffered buffered_len /\
          Seq.equal sent1 st1.CS.cs_wire_log.CL.raw_sent /\
          Seq.equal
            st1.CS.cs_wire_log.CL.raw_received
            st0.CS.cs_wire_log.CL.raw_received /\
          ST.server_connection_control_not_failed st0)
        (ensures
          server_driver_wire_logs_match_witness
            st1 received sent1 consumed buffered buffered_len)
=
  Seq.lemma_eq_elim sent1 st1.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim
    st1.CS.cs_wire_log.CL.raw_received
    st0.CS.cs_wire_log.CL.raw_received

open TLS13.Impl.Server.Driver.Transport
open TLS13.Impl.Server.Driver.Network
open TLS13.Impl.Server.Driver.Local

let lemma_select_server_parameters_ready_payload_irrelevant
  (st:CS.connection_state)
  (payload0:B.bytes)
  (payload1:B.bytes)
  : Lemma
      (requires
        B.length payload0 == 64 /\
        B.length payload1 == 64 /\
        ST.server_local_event_input_ready
          st
          ST.LocalSelectServerParameters
          payload0)
      (ensures
        ST.server_local_event_input_ready
          st
          ST.LocalSelectServerParameters
          payload1 /\
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
          None)
=
  assert (st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
  assert (st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived);
  assert (CR.server_selection_absent st.CS.cs_model.CS.model_handshake);
  assert (Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  assert (Some? st.CS.cs_model.CS.model_config.CS.config_server);
  let ch = Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_hello in
  let cfg = Some?.v st.CS.cs_model.CS.model_config.CS.config_server in
  let selection0 = {
    CS.server_selected_client_hello = ch;
    CS.server_selected_cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    CS.server_selected_group = T.X25519;
    CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
    CS.server_random = CL.raw_slice payload0 0 32;
    CS.server_key_share_private = Some (CL.raw_slice payload0 32 64);
    CS.server_key_share_public =
      CryptoSpec.x25519_public_from_private (CL.raw_slice payload0 32 64);
    CS.server_selected_credential = cfg.CS.server_credential_identity;
  } in
  let selection1 = {
    CS.server_selected_client_hello = ch;
    CS.server_selected_cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    CS.server_selected_group = T.X25519;
    CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
    CS.server_random = CL.raw_slice payload1 0 32;
    CS.server_key_share_private = Some (CL.raw_slice payload1 32 64);
    CS.server_key_share_public =
      CryptoSpec.x25519_public_from_private (CL.raw_slice payload1 32 64);
    CS.server_selected_credential = cfg.CS.server_credential_identity;
  } in
  assert (CM.can_select_server_parameters st selection0);
  assert (CS.legal_event
    st.CS.cs_model
    (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0)));
  assert (st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
    None);
  assert (CS.server_selection_acceptable cfg selection0);
  assert (CS.cipher_suite_offered
    cfg.CS.server_supported_cipher_suites
    T.TLS_CHACHA20_POLY1305_SHA256);
  assert (CS.cipher_suite_offered
    (Sem.clientHello_cipher_suites ch)
    T.TLS_CHACHA20_POLY1305_SHA256);
  assert (CS.named_group_offered
    cfg.CS.server_supported_groups
    T.X25519);
  assert (CS.signature_scheme_offered
    cfg.CS.server_allowed_signature_schemes
    T.Rsa_pss_rsae_sha256);
  assert (match Sem.clientHello_sig_algs ch with
    | Some sas -> CS.signature_scheme_offered sas T.Rsa_pss_rsae_sha256
    | None -> False);
  assert (CS.sni_policy_accepts cfg.CS.server_sni_policy (Sem.clientHello_server_name ch));
  assert (CS.server_selection_key_share_consistent selection1);
  assert (CS.server_selection_acceptable cfg selection1);
  assert (CS.legal_event
    st.CS.cs_model
    (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection1)));
  assert (CM.can_select_server_parameters st selection1)

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

let lemma_select_server_parameters_input_ready_intro
    (st:CS.connection_state)
    (payload:B.bytes)
    (server_random server_private_key:B.bytes_of_len 32)
    : Lemma
        (requires
          B.length payload == 64 /\
          st.CS.cs_model.CS.model_config.CS.config_role ==
            CS.ServerEndpoint /\
          st.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived /\
          CR.server_selection_absent st.CS.cs_model.CS.model_handshake /\
          Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
          Some? st.CS.cs_model.CS.model_config.CS.config_server /\
          server_random == CL.raw_slice payload 0 32 /\
          server_private_key == CL.raw_slice payload 32 64 /\
          (match st.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                 st.CS.cs_model.CS.model_config.CS.config_server with
           | Some ch, Some cfg ->
             CM.can_select_server_parameters st {
               CS.server_selected_client_hello = ch;
               CS.server_selected_cipher_suite =
                 T.TLS_CHACHA20_POLY1305_SHA256;
               CS.server_selected_group = T.X25519;
               CS.server_selected_signature_scheme =
                 T.Rsa_pss_rsae_sha256;
               CS.server_random = server_random;
               CS.server_key_share_private = Some server_private_key;
               CS.server_key_share_public =
                 CryptoSpec.x25519_public_from_private server_private_key;
               CS.server_selected_credential =
                 cfg.CS.server_credential_identity;
             }
           | _ -> False))
        (ensures
          ST.server_local_event_input_ready
            st
            ST.LocalSelectServerParameters
            payload)
=
  match st.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
        st.CS.cs_model.CS.model_config.CS.config_server with
  | Some _, Some _ -> ()
  | _ -> assert False

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
        B.length network_out == SZ.v driver_network_out_capacity /\
        B.length app_out == SZ.v driver_app_out_capacity)
      (ensures
        B.length (CL.raw_slice payload 0 32) == 32 /\
        B.length (CL.raw_slice payload 32 64) == 32 /\
        B.length network_out == SZ.v driver_network_out_capacity /\
        B.length app_out == SZ.v driver_app_out_capacity /\
        ST.server_end_to_end_invariant st /\
        CR.server_selection_absent st.CS.cs_model.CS.model_handshake /\
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
          None /\
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

let lemma_server_local_event_input_ready_derive_shared_secret_intro
  (st:CS.connection_state)
  (payload:B.bytes)
  : Lemma
      (requires
        B.length payload == 32 /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        st.CS.cs_model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
          None /\
        Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
        (match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
         | Some selection ->
           CS.server_selection_key_share_consistent selection /\
           st.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
             Some selection.CS.server_selected_client_hello /\
           Some? selection.CS.server_key_share_private /\
           Some?.v selection.CS.server_key_share_private == payload
         | None -> False))
      (ensures
        ST.server_local_event_input_ready
          st
          ST.LocalDeriveSharedSecret
          payload)
=
  ()

let lemma_derive_shared_secret_call_ready
    (st:CS.connection_state)
    (payload network_out app_out:B.bytes)
    : Lemma
        (requires
          ST.server_local_event_input_ready
            st
            ST.LocalDeriveSharedSecret
            payload /\
          ST.server_end_to_end_invariant st /\
          B.length network_out == SZ.v driver_network_out_capacity /\
          B.length app_out == SZ.v driver_app_out_capacity)
        (ensures
          B.length payload == 32 /\
          B.length network_out == SZ.v driver_network_out_capacity /\
          B.length app_out == SZ.v driver_app_out_capacity /\
          ST.server_end_to_end_invariant st /\
          st.CS.cs_model.CS.model_config.CS.config_role ==
            CS.ServerEndpoint /\
          st.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived /\
          st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
            None /\
          Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
          (match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
           | Some selection ->
             CS.server_selection_key_share_consistent selection /\
             st.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
               Some selection.CS.server_selected_client_hello /\
             Some? selection.CS.server_key_share_private /\
             Some?.v selection.CS.server_key_share_private == payload
           | None -> False))
=
  ()

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

fn process_derive_shared_secret_from_payload_ready
    (s:S.server)
    (payload:array U8.t)
    (network_out:array U8.t)
    (app_out:array U8.t)
    requires
      S.connection_exactly s 'st0 **
      pts_to payload 'payload_bytes **
      pts_to network_out 'old_network_out **
      pts_to app_out 'old_app_out **
      pure (
        ST.server_local_event_input_ready
          'st0
          ST.LocalDeriveSharedSecret
          (Ghost.reveal 'payload_bytes) /\
        ST.server_end_to_end_invariant 'st0 /\
        B.length 'old_network_out == SZ.v driver_network_out_capacity /\
        B.length 'old_app_out == SZ.v driver_app_out_capacity)
    returns resp:ST.server_response
    ensures exists* st1 network_out_bytes app_out_bytes.
      S.connection_exactly s st1 **
      pts_to payload 'payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        ST.server_local_event_input_ready
          'st0
          ST.LocalDeriveSharedSecret
          (Ghost.reveal 'payload_bytes) /\
        ST.server_connection_control_not_failed 'st0 /\
        B.length network_out_bytes == SZ.v driver_network_out_capacity /\
        B.length app_out_bytes == SZ.v driver_app_out_capacity /\
        ST.server_local_event_end_to_end_correct
          'st0
          st1
          resp
          ST.LocalDeriveSharedSecret
          (Ghost.reveal 'payload_bytes)
          network_out_bytes
          app_out_bytes /\
        server_driver_derive_shared_secret_success_correct
          'st0
          st1
          resp
          (Ghost.reveal 'payload_bytes))
{
  lemma_derive_shared_secret_call_ready
    'st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'old_network_out)
    (Ghost.reveal 'old_app_out);
  lemma_client_hello_received_not_failed 'st0;
  let resp =
    S.process_derive_shared_secret_from_private_array
      s
      payload
      network_out
      driver_network_out_capacity
      app_out
      driver_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (
      S.connection_exactly s st1 **
      pts_to payload 'payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes);
  assert (pure (server_driver_derive_shared_secret_success_correct
    'st0
    st1
    resp
    (Ghost.reveal 'payload_bytes)));
  resp
}

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let lemma_select_derive_success_server_hello_ready
  (st0 st2:CS.connection_state)
  (resp:ST.server_response)
  (payload:B.bytes)
  : Lemma
      (requires
       B.length payload == 64 /\
       resp.ST.status == ST.StepOk /\
       server_driver_select_derive_from_payload_success_correct
         st0 st2 resp payload /\
       st2.CS.cs_model.CS.model_control ==
         CS.ControlHandshaking CS.HsClientHelloReceived /\
       st2.CS.cs_model.CS.model_config.CS.config_role ==
         CS.ServerEndpoint /\
       Some? st2.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
       st2.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
       Some? st2.CS.cs_model.CS.model_handshake.CS.hs_server_selection /\
       B.length st2.CS.cs_model.CS.model_handshake.CS.hs_transcript + 90 <=
         Bounds.max_transcript_len /\
       (Seq.length (CL.raw_slice payload 0 32) == 32 ==>
        (CL.raw_slice payload 0 32 <: Seq.lseq U8.t 32) <>
          GSHbody.serverHello_body_cst))
      (ensures
       ST.server_local_event_input_ready
         st2
         ST.LocalSendServerHello
         payload)
=
  assert (CL.raw_slice payload 0 32 == Seq.slice payload 0 32);
  assert (CL.raw_slice payload 32 64 == Seq.slice payload 32 64);
  Seq.lemma_len_slice payload 0 32;
  Seq.lemma_len_slice payload 32 64;
  assert (B.length (CL.raw_slice payload 0 32) == 32);
  assert (B.length (CL.raw_slice payload 32 64) == 32);
  let server_random = CL.raw_slice payload 0 32 in
  let server_private_key = CL.raw_slice payload 32 64 in
  let sh = SS.mk_server_hello_witness
             server_random
             (CryptoSpec.x25519_public_from_private server_private_key)
             T.TLS_CHACHA20_POLY1305_SHA256 in
  assert (exists st1 shared.
    server_driver_selection_from_payload_correct st0 st1 payload /\
    st2 == CM.derived_shared_secret_state st1 shared /\
    (match st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
     | Some ch ->
      (match CS.client_hello_key_share ch with
       | Some k -> CryptoSpec.x25519_shared server_private_key k == Some shared
       | None -> False)
     | None -> False));
  let st1 =
    ID.indefinite_description_ghost
      CS.connection_state
      (fun st1 -> exists shared.
       server_driver_selection_from_payload_correct st0 st1 payload /\
       st2 == CM.derived_shared_secret_state st1 shared /\
       (match st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
        | Some ch ->
          (match CS.client_hello_key_share ch with
           | Some k -> CryptoSpec.x25519_shared server_private_key k == Some shared
           | None -> False)
        | None -> False)) in
  let shared =
    ID.indefinite_description_ghost
      CryptoSpec.x25519_shared_secret
      (fun shared ->
       server_driver_selection_from_payload_correct st0 st1 payload /\
       st2 == CM.derived_shared_secret_state st1 shared /\
       (match st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
        | Some ch ->
          (match CS.client_hello_key_share ch with
           | Some k -> CryptoSpec.x25519_shared server_private_key k == Some shared
           | None -> False)
        | None -> False)) in
  assert (server_driver_selection_from_payload_correct st0 st1 payload);
  assert (st2 == CM.derived_shared_secret_state st1 shared);
  assert (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
               st0.CS.cs_model.CS.model_config.CS.config_server with
    | Some ch, Some cfg ->
      let selection = {
       CS.server_selected_client_hello = ch;
       CS.server_selected_cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
       CS.server_selected_group = T.X25519;
       CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
       CS.server_random = server_random;
       CS.server_key_share_private = Some server_private_key;
       CS.server_key_share_public =
         CryptoSpec.x25519_public_from_private server_private_key;
       CS.server_selected_credential = cfg.CS.server_credential_identity;
      } in
      st1 == CM.selected_server_parameters_state st0 selection
    | _ -> False);
  assert (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  assert (Some? st0.CS.cs_model.CS.model_config.CS.config_server);
  let selected_ch = Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello in
  let server_cfg = Some?.v st0.CS.cs_model.CS.model_config.CS.config_server in
  let selection = {
    CS.server_selected_client_hello = selected_ch;
    CS.server_selected_cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    CS.server_selected_group = T.X25519;
    CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
    CS.server_random = server_random;
    CS.server_key_share_private = Some server_private_key;
    CS.server_key_share_public =
      CryptoSpec.x25519_public_from_private server_private_key;
    CS.server_selected_credential = server_cfg.CS.server_credential_identity;
  } in
  assert (st1 == CM.selected_server_parameters_state st0 selection);
  assert (st2.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
    Some selection);
  assert (Some?.v st2.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
    selection);
  assert (Seq.equal selection.CS.server_random server_random);
  assert (Some? selection.CS.server_key_share_private);
  assert (Seq.equal (Some?.v selection.CS.server_key_share_private) server_private_key);
  assert (CS.server_selection_key_share_consistent selection);
  // Build-direction send obligation now carried by input_ready LocalSendServerHello:
  // the canonical ServerHello built from the selection (CM.server_hello_of_selection,
  // the server mirror of client_hello_of_start) can be sent.  valid_selection holds:
  //   - cipher suite is CHACHA (fixed in the selection construction), and
  //   - the server random differs from the HRR sentinel serverHello_body_cst
  //     (cst-guard precondition; selection.server_random == server_random ==
  //      raw_slice payload 0 32).
  assert (selection.CS.server_random == server_random);
  assert ((selection.CS.server_random <: Seq.lseq U8.t 32) <>
    GSHbody.serverHello_body_cst);
  assert (selection.CS.server_selected_cipher_suite ==
    T.TLS_CHACHA20_POLY1305_SHA256);
  assert (CM.valid_selection selection);
  let sh_sel = CM.server_hello_of_selection selection in
  CM.lemma_server_hello_of_selection_matches selection;
  CM.lemma_server_hello_of_selection_bytesize selection;
  assert (CS.server_hello_matches_selection selection sh_sel);
  assert (B.length (W.serialize_handshake (M.ServerHello sh_sel)) == 90);
  assert (CS.legal_event
    st2.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh_sel);
    }));
  assert (CS.event_raw_delta_legal
    st2.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh_sel);
    })
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello sh_sel)))
    B.empty);
  assert (CM.can_send_server_hello st2 sh_sel
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello sh_sel))));
  assert (ST.server_local_event_input_ready
    st2
    ST.LocalSendServerHello
    payload);
  assert (selection.CS.server_selected_cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256);
  assert ((Some?.v st2.CS.cs_model.CS.model_handshake.CS.hs_server_selection).CS.server_selected_cipher_suite ==
    T.TLS_CHACHA20_POLY1305_SHA256)
#pop-options

// Helper lemma: assembles can_send_server_hello from individual runtime facts,
// cst-guard, and serialize-length. Used by select_derive_send_server_hello_from_payload_once
// to satisfy send_server_hello_from_payload_once's TODO-A1 precondition.
let lemma_assemble_can_send_server_hello
  (st:CS.connection_state)
  (payload:B.bytes)
  : Lemma
      (requires
       B.length payload == 64 /\
       st.CS.cs_model.CS.model_control ==
         CS.ControlHandshaking CS.HsClientHelloReceived /\
       st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
       Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
       st.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
       Some? st.CS.cs_model.CS.model_handshake.CS.hs_server_selection /\
       (Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_server_selection).CS.server_selected_cipher_suite ==
         T.TLS_CHACHA20_POLY1305_SHA256 /\
       B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 90 <=
         Bounds.max_transcript_len /\
       ST.server_local_event_input_ready st ST.LocalSendServerHello payload /\
       (Seq.length (CL.raw_slice payload 0 32) == 32 ==>
        (CL.raw_slice payload 0 32 <: Seq.lseq U8.t 32) <>
          GSHbody.serverHello_body_cst) /\
       (let sh = SS.mk_server_hello_witness
                  (CL.raw_slice payload 0 32)
                  (CryptoSpec.x25519_public_from_private (CL.raw_slice payload 32 64))
                  T.TLS_CHACHA20_POLY1305_SHA256 in
        B.length (W.serialize_handshake (M.ServerHello sh)) == 90))
      (ensures
       (let sh = SS.mk_server_hello_witness
                  (CL.raw_slice payload 0 32)
                  (CryptoSpec.x25519_public_from_private (CL.raw_slice payload 32 64))
                  T.TLS_CHACHA20_POLY1305_SHA256 in
        CM.can_send_server_hello st sh
          (CS.serialized_cleartext_tls_message
            (M.TlsHandshake (M.ServerHello sh)))))
=
  let server_random = CL.raw_slice payload 0 32 in
  let server_private_key = CL.raw_slice payload 32 64 in
  Seq.lemma_len_slice payload 0 32;
  Seq.lemma_len_slice payload 32 64;
  let key_share = CryptoSpec.x25519_public_from_private server_private_key in
  let sh = SS.mk_server_hello_witness server_random key_share
             T.TLS_CHACHA20_POLY1305_SHA256 in
  let selection = Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_server_selection in
  assert (Seq.equal selection.CS.server_random server_random);
  assert (Some? selection.CS.server_key_share_private);
  assert (Seq.equal (Some?.v selection.CS.server_key_share_private) server_private_key);
  assert (CS.server_selection_key_share_consistent selection);
  assert (Seq.equal selection.CS.server_key_share_public key_share);
  assert (CS.server_hello_matches_selection selection sh);
  assert (CS.legal_event
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    }));
  assert (CS.event_raw_delta_legal
    st.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    })
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello sh)))
    B.empty);
  assert (CM.can_send_server_hello st sh
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello sh))))

fn generate_server_material_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns ok:bool
  ensures server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));

  unfold (server_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out material cv_input signature app_out.
    assert (
      Box.pts_to d.server_driver_buffered_len buffered_len **
      V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.server_driver_raw #1.0R raw **
      V.pts_to d.server_driver_network_out #1.0R network_out **
      V.pts_to d.server_driver_material_payload #1.0R material **
      V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
      V.pts_to d.server_driver_signature #1.0R signature **
      V.pts_to d.server_driver_app_out #1.0R app_out);
  V.to_array_pts_to d.server_driver_material_payload;
  let ok =
    Crypto.random_bytes
      (V.vec_to_array d.server_driver_material_payload)
      driver_material_capacity;
  with material_bytes.
    assert (pts_to (V.vec_to_array d.server_driver_material_payload) material_bytes);
  assert (pure (B.length material_bytes == SZ.v driver_material_capacity));
  V.to_vec_pts_to d.server_driver_material_payload;
  fold (server_driver_buffers d buffered buffered_len);
  fold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  ok
}

fn select_default_server_parameters_once
  (d:server_driver)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (ST.server_local_event_input_ready
             'st0
             ST.LocalSelectServerParameters
             (Seq.create 64 0uy))
  returns resp:ST.server_response
  ensures exists* st1.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            'sent
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));

  unfold (server_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out material cv_input signature app_out.
    assert (
      Box.pts_to d.server_driver_buffered_len buffered_len **
      V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.server_driver_raw #1.0R raw **
      V.pts_to d.server_driver_network_out #1.0R network_out **
      V.pts_to d.server_driver_material_payload #1.0R material **
      V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
      V.pts_to d.server_driver_signature #1.0R signature **
      V.pts_to d.server_driver_app_out #1.0R app_out);
  V.to_array_pts_to d.server_driver_material_payload;
  V.to_array_pts_to d.server_driver_network_out;
  V.to_array_pts_to d.server_driver_app_out;
  with material_bytes.
    assert (pts_to (V.vec_to_array d.server_driver_material_payload) material_bytes);
  assert (pure (B.length material_bytes == SZ.v driver_material_capacity));
  assert (pure (B.length material_bytes == 64));
  lemma_select_server_parameters_ready_payload_irrelevant
    'st0
    (Seq.create 64 0uy)
    material_bytes;
  assert (pure (ST.server_local_event_input_ready
    'st0
    ST.LocalSelectServerParameters
    material_bytes));

  let mut server_random = [| 0uy; 32sz |];
  let mut server_private_key = [| 0uy; 32sz |];
  Mat.copy_server_random_and_private_from_payload
    (V.vec_to_array d.server_driver_material_payload)
    server_random
    server_private_key;
  with server_random_bytes. assert (pts_to server_random server_random_bytes);
  with server_private_key_bytes.
    assert (pts_to server_private_key server_private_key_bytes);
  assert (pure (B.length server_random_bytes == 32));
  assert (pure (B.length server_private_key_bytes == 32));
  assert (pure (Seq.equal
    server_random_bytes
    (CL.raw_slice material_bytes 0 32)));
  assert (pure (Seq.equal
    server_private_key_bytes
    (CL.raw_slice material_bytes 32 64)));
  Seq.lemma_eq_elim
    server_random_bytes
    (CL.raw_slice material_bytes 0 32);
  Seq.lemma_eq_elim
    server_private_key_bytes
    (CL.raw_slice material_bytes 32 64);
  Seq.lemma_len_slice material_bytes 0 32;
  Seq.lemma_len_slice material_bytes 32 64;
  assert (pure (B.length (CL.raw_slice material_bytes 0 32) == 32));
  assert (pure (B.length (CL.raw_slice material_bytes 32 64) == 32));
  lemma_select_server_parameters_call_ready
    'st0
    material_bytes
    network_out
    app_out;

  let resp =
    S.process_select_default_server_parameters_with_derived_public_from_private_array
      d.server_driver_server
      server_random
      server_private_key
      (V.vec_to_array d.server_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.server_driver_app_out)
      driver_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (
      S.connection_exactly d.server_driver_server st1 **
      pts_to server_random server_random_bytes **
      pts_to server_private_key server_private_key_bytes **
      pts_to (V.vec_to_array d.server_driver_network_out) network_out_bytes **
      pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
  lemma_some_default_server_parameters_state
    'st0
    st1
    server_random_bytes
    server_private_key_bytes;
  SP.lemma_server_local_event_progress
    'st0
    st1
    resp
    ST.LocalSelectServerParameters
    B.empty
    network_out_bytes
    app_out_bytes;
  advance_server_driver_canonical_progress
    d 'st0 st1;
  assert (pure (st1.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived));
  assert (pure (st1.CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (
    st1.CS.cs_model.CS.model_handshake.CS.hs_keys ==
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys));
  assert (pure (
    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
      None));
  assert (pure (
    st1.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret));
  assert (pure (
    st1.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
      None));
  assert (pure (Some?
    st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure (Seq.equal
    server_private_key_bytes
    (CL.raw_slice material_bytes 32 64)));
  assert (pure (ST.server_end_to_end_invariant st1));

  CL.lemma_append_empty_right 'st0.CS.cs_wire_log.CL.raw_sent;
  CL.lemma_append_empty_right 'st0.CS.cs_wire_log.CL.raw_received;
  lemma_selected_server_parameters_state_wire_log
    'st0
    (Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
  assert (pure ('st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived));
  lemma_client_hello_received_not_failed 'st0;
  lemma_client_hello_received_not_failed st1;
  lemma_local_event_wire_lengths
    'st0
    st1
    resp
    ST.LocalSelectServerParameters
    B.empty
    network_out_bytes
    app_out_bytes;
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received));
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    'st0.CS.cs_wire_log.CL.raw_sent));
  lemma_server_driver_wire_logs_match_nonfailed_stutter
    'st0
    st1
    'received
    'sent
    buffered
    buffered_len;
  assert (pure (server_driver_wire_logs_match
    st1
    'received
    'sent
    buffered
    buffered_len));
  assert (pure (server_driver_config_matches_credentials
    st1
    'certificate_chain
    'credential_identity));
  assert (pure (CS.signature_scheme_offered
    st1.CS.cs_model.CS.model_config.CS.config_signature_schemes
    T.Rsa_pss_rsae_sha256));
  lemma_client_hello_received_selection_present st1;
  assert (pure (Some?
    st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
  assert (pure (
    (Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection).
      CS.server_selected_signature_scheme ==
      T.Rsa_pss_rsae_sha256));
  assert (pure (
    (Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection).
      CS.server_selected_credential ==
      'credential_identity));
  assert (pure (server_driver_supported_profile_selection
    st1
    'credential_identity));

  V.to_vec_pts_to d.server_driver_material_payload;
  V.to_vec_pts_to d.server_driver_network_out;
  V.to_vec_pts_to d.server_driver_app_out;
  fold (server_driver_buffers d buffered buffered_len);
  fold (server_driver_connected
    d
    st1
    'certificate_chain
    'credential_identity
    'received
    'sent);
  resp
}

let lemma_server_selection_from_payload_correct_intro
    (st0:CS.connection_state)
    (st1:CS.connection_state)
    (payload:B.bytes)
    : Lemma
        (requires
          B.length payload == 64 /\
          Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
          Some? st0.CS.cs_model.CS.model_config.CS.config_server /\
          st1 == CM.selected_server_parameters_state st0 {
            CS.server_selected_client_hello =
              Some?.v
                st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello;
            CS.server_selected_cipher_suite =
              T.TLS_CHACHA20_POLY1305_SHA256;
            CS.server_selected_group = T.X25519;
            CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
            CS.server_random = CL.raw_slice payload 0 32;
            CS.server_key_share_private =
              Some (CL.raw_slice payload 32 64);
            CS.server_key_share_public =
              CryptoSpec.x25519_public_from_private
                (CL.raw_slice payload 32 64);
            CS.server_selected_credential =
              (Some?.v
                st0.CS.cs_model.CS.model_config.CS.config_server).
                  CS.server_credential_identity;
          })
        (ensures
          server_driver_selection_from_payload_correct st0 st1 payload)
=
  match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
        st0.CS.cs_model.CS.model_config.CS.config_server with
  | Some _, Some _ -> ()
  | _ -> assert False

fn select_default_server_parameters_from_payload_once
  (d:server_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 SZ.v payload_len == 64 /\
                 ST.server_local_event_input_ready
                   'st0
                   ST.LocalSelectServerParameters
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            'sent **
          pts_to payload 'payload_bytes **
          pure (server_driver_selection_from_payload_correct
            'st0
            st1
            (Ghost.reveal 'payload_bytes) /\
            st1.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config)
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));

  unfold (server_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out material cv_input signature app_out.
    assert (
      Box.pts_to d.server_driver_buffered_len buffered_len **
      V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.server_driver_raw #1.0R raw **
      V.pts_to d.server_driver_network_out #1.0R network_out **
      V.pts_to d.server_driver_material_payload #1.0R material **
      V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
      V.pts_to d.server_driver_signature #1.0R signature **
      V.pts_to d.server_driver_app_out #1.0R app_out);
  V.to_array_pts_to d.server_driver_network_out;
  V.to_array_pts_to d.server_driver_app_out;

  let mut server_random = [| 0uy; 32sz |];
  let mut server_private_key = [| 0uy; 32sz |];
  Mat.copy_server_random_and_private_from_payload
    payload
    server_random
    server_private_key;
  with server_random_bytes. assert (pts_to server_random server_random_bytes);
  with server_private_key_bytes.
    assert (pts_to server_private_key server_private_key_bytes);
  assert (pure (B.length server_random_bytes == 32));
  assert (pure (B.length server_private_key_bytes == 32));
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
  lemma_select_server_parameters_call_ready
    'st0
    (Ghost.reveal 'payload_bytes)
    network_out
    app_out;

  let resp =
    S.process_select_default_server_parameters_with_derived_public_from_private_array
      d.server_driver_server
      server_random
      server_private_key
      (V.vec_to_array d.server_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.server_driver_app_out)
      driver_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (
      S.connection_exactly d.server_driver_server st1 **
      pts_to server_random server_random_bytes **
      pts_to server_private_key server_private_key_bytes **
      pts_to (V.vec_to_array d.server_driver_network_out) network_out_bytes **
      pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
  lemma_some_default_server_parameters_state
    'st0
    st1
    server_random_bytes
    server_private_key_bytes;
  SP.lemma_server_local_event_progress
    'st0
    st1
    resp
    ST.LocalSelectServerParameters
    B.empty
    network_out_bytes
    app_out_bytes;
  advance_server_driver_canonical_progress
    d 'st0 st1;
  assert (pure (st1.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived));
  assert (pure (st1.CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure (
    st1.CS.cs_model.CS.model_handshake.CS.hs_keys ==
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys));
  assert (pure (
    st1.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
      None));
  assert (pure (Some?
    st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
  assert (pure (CS.server_selection_key_share_consistent
    (Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection)));
  assert (pure (Some?
    (Some?.v
      st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection).
        CS.server_key_share_private));
  assert (pure (B.length (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64) == 32));
  assert (pure (
    Some?.v
      (Some?.v
        st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection).
          CS.server_key_share_private ==
      server_private_key_bytes));
  assert (pure (match st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
    | Some selection1 ->
      CS.server_selection_key_share_consistent selection1 /\
      st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
        Some selection1.CS.server_selected_client_hello /\
      Some? selection1.CS.server_key_share_private /\
      Some?.v selection1.CS.server_key_share_private == server_private_key_bytes
    | None -> False));
  lemma_server_local_event_input_ready_derive_shared_secret_intro
    st1
    server_private_key_bytes;
  assert (pure (ST.server_local_event_input_ready
    st1
    ST.LocalDeriveSharedSecret
    server_private_key_bytes));
  assert (pure (ST.server_end_to_end_invariant st1));
  lemma_server_selection_from_payload_correct_intro
    'st0
    st1
    (Ghost.reveal 'payload_bytes);
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure (server_driver_config_matches_credentials
    st1
    'certificate_chain
    'credential_identity));
  lemma_client_hello_received_selection_present st1;
  assert (pure (
    (Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection).
      CS.server_selected_signature_scheme ==
      T.Rsa_pss_rsae_sha256));
  assert (pure (
    (Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection).
      CS.server_selected_credential ==
      'credential_identity));
  assert (pure (server_driver_supported_profile_selection
    st1
    'credential_identity));

  CL.lemma_append_empty_right 'st0.CS.cs_wire_log.CL.raw_sent;
  CL.lemma_append_empty_right 'st0.CS.cs_wire_log.CL.raw_received;
  lemma_selected_server_parameters_state_wire_log
    'st0
    (Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
  assert (pure ('st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived));
  lemma_client_hello_received_not_failed 'st0;
  lemma_client_hello_received_not_failed st1;
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received));
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    'st0.CS.cs_wire_log.CL.raw_sent));
  lemma_server_driver_wire_logs_match_nonfailed_stutter
    'st0
    st1
    'received
    'sent
    buffered
    buffered_len;
  assert (pure (server_driver_wire_logs_match
    st1
    'received
    'sent
    buffered
    buffered_len));

  V.to_vec_pts_to d.server_driver_network_out;
  V.to_vec_pts_to d.server_driver_app_out;
  fold (server_driver_buffers d buffered buffered_len);
  fold (server_driver_connected
    d
    st1
    'certificate_chain
    'credential_identity
    'received
    'sent);
  resp
}

fn derive_shared_secret_from_payload_once
  (d:server_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 SZ.v payload_len == 32 /\
                 ST.server_local_event_input_ready
                   'st0
                   ST.LocalDeriveSharedSecret
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pts_to payload 'payload_bytes **
          pure (server_driver_local_write_correct
            'st0
            st1
            resp
            ST.LocalDeriveSharedSecret
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'sent)
            sent' /\
           server_driver_derive_shared_secret_success_correct
            'st0
            st1
            resp
            (Ghost.reveal 'payload_bytes) /\
           st1.CS.cs_model.CS.model_config ==
             'st0.CS.cs_model.CS.model_config)
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));

  unfold (server_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out material cv_input signature app_out.
    assert (
      Box.pts_to d.server_driver_buffered_len buffered_len **
      V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.server_driver_raw #1.0R raw **
      V.pts_to d.server_driver_network_out #1.0R network_out **
      V.pts_to d.server_driver_material_payload #1.0R material **
      V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
      V.pts_to d.server_driver_signature #1.0R signature **
      V.pts_to d.server_driver_app_out #1.0R app_out);
  V.to_array_pts_to d.server_driver_network_out;
  V.to_array_pts_to d.server_driver_app_out;
  assert (pure (B.length (Ghost.reveal 'payload_bytes) == 32));
  assert (pure (B.length network_out == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out == SZ.v driver_app_out_capacity));
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (ST.server_local_event_input_ready
    'st0
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)));
  let resp =
    process_derive_shared_secret_from_payload_ready
      d.server_driver_server
      payload
      (V.vec_to_array d.server_driver_network_out)
      (V.vec_to_array d.server_driver_app_out);
  with st1 network_out_bytes app_out_bytes.
    assert (
      S.connection_exactly d.server_driver_server st1 **
      pts_to payload 'payload_bytes **
      pts_to (V.vec_to_array d.server_driver_network_out) network_out_bytes **
      pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    st1
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes));
  assert (pure (ST.server_end_to_end_invariant st1));
  SP.lemma_server_local_event_progress
    'st0
    st1
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  advance_server_driver_canonical_progress
    d 'st0 st1;
  lemma_local_event_wire_lengths
    'st0
    st1
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  assert (pure (SZ.v resp.ST.network_out_len <= B.length network_out_bytes));

  let current_channel = Box.(!d.server_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite (IO.is_channel ch 'received 'sent) as
    (IO.is_channel concrete_ch 'received 'sent);
  let written =
    IO.write
      concrete_ch
      (V.vec_to_array d.server_driver_network_out)
      resp.ST.network_out_len;
  assert (pure (written == resp.ST.network_out_len));
  assert (pure (SZ.v written <= B.length network_out_bytes));
  rewrite
    (IO.is_channel
      concrete_ch
      'received
      (B.append
        (Ghost.reveal 'sent)
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty)))
    as
    (IO.is_channel
      ch
      'received
      (B.append
        (Ghost.reveal 'sent)
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty)));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written);
  assert (pure (Seq.equal
    (if SZ.v written <= B.length network_out_bytes
     then Seq.slice network_out_bytes 0 (SZ.v written)
     else B.empty)
    (ST.response_network_out resp network_out_bytes)));
  let old_consumed =
    choose_server_driver_wire_logs_consumed
      'st0
      (Ghost.reveal 'received)
      (Ghost.reveal 'sent)
      buffered
      buffered_len;
  assert (pure (server_driver_wire_logs_match_witness
    'st0
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent)
    (Ghost.reveal old_consumed)
    buffered
    buffered_len));
  assert (pure (Seq.equal
    (Ghost.reveal 'sent)
    'st0.CS.cs_wire_log.CL.raw_sent));
  Seq.lemma_eq_elim
    (Ghost.reveal 'sent)
    'st0.CS.cs_wire_log.CL.raw_sent;
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (B.append
      'st0.CS.cs_wire_log.CL.raw_sent
      (ST.response_network_out resp network_out_bytes))));
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received));
  Seq.lemma_eq_elim
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received;
  assert (pure (Seq.equal
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    st1.CS.cs_wire_log.CL.raw_sent));
  Seq.lemma_eq_elim
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    st1.CS.cs_wire_log.CL.raw_sent;
  lemma_server_driver_wire_logs_match_witness_sent
    'st0
    st1
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (Ghost.reveal old_consumed)
    buffered
    buffered_len;
  assert (pure (server_driver_wire_logs_match
    st1
    (Ghost.reveal 'received)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    buffered
    buffered_len));
  lemma_server_driver_local_write_correct_intro
    'st0
    st1
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    network_out_bytes
    app_out_bytes;
  assert (pure (ST.server_local_event_input_ready
    'st0
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)));
  lemma_derive_shared_secret_ready_with_credentials
    'st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity);
  assert (pure (ST.server_local_event_input_ready_with_credentials
    'st0
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  lemma_server_driver_local_write_correct_preserves_config
    'st0
    st1
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty));
  assert (pure (server_driver_config_matches_credentials
    st1
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  lemma_server_driver_local_write_correct_preserves_supported_profile_selection
    'st0
    st1
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty));
  assert (pure (server_driver_supported_profile_selection
    st1
    (Ghost.reveal 'credential_identity)));

  V.to_vec_pts_to d.server_driver_network_out;
  V.to_vec_pts_to d.server_driver_app_out;
  fold (server_driver_buffers d buffered buffered_len);
  CPI.lemma_bytes_extends_refl (Ghost.reveal 'received);
  CPI.lemma_bytes_extends_append
    (Ghost.reveal 'sent)
    (if SZ.v written <= B.length network_out_bytes
     then Seq.slice network_out_bytes 0 (SZ.v written)
     else B.empty);
  advance_server_driver_io_history
    d
    'received
    'sent
    'received
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty));
  fold (server_driver_connected
    d
    st1
    'certificate_chain
    'credential_identity
    'received
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty)));
  assert (pure (Seq.equal
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (B.append
      (Ghost.reveal 'sent)
      (ST.response_network_out resp network_out_bytes))));
  lemma_server_driver_local_write_correct_intro
    'st0
    st1
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    network_out_bytes
    app_out_bytes;
  assert (pure (server_driver_local_write_correct
    'st0
    st1
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))));
  assert (pure (server_driver_derive_shared_secret_success_correct
    'st0
    st1
    resp
    (Ghost.reveal 'payload_bytes)));
  resp
}

fn select_supported_server_parameters_from_payload_if_ready_once
  (d:server_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 SZ.v payload_len == 64 /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                        'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some ch, Some cfg ->
                    CS.cipher_suite_offered
                      cfg.CS.server_supported_cipher_suites
                      T.TLS_CHACHA20_POLY1305_SHA256 /\
                    CS.named_group_offered
                      cfg.CS.server_supported_groups
                      T.X25519 /\
                    CS.signature_scheme_offered
                      cfg.CS.server_allowed_signature_schemes
                      T.Rsa_pss_rsae_sha256 /\
                    CS.sni_policy_accepts cfg.CS.server_sni_policy (Sem.clientHello_server_name ch)
                  | _, _ -> True))
  returns status:server_driver_local_status
  ensures (match status with
           | ServerDriverLocalProcessed ->
             exists* st1.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 'received
                 'sent **
               pts_to payload 'payload_bytes **
               pure (server_driver_selection_from_payload_correct
                 'st0
                 st1
                 (Ghost.reveal 'payload_bytes) /\
               st1.CS.cs_model.CS.model_config ==
                 'st0.CS.cs_model.CS.model_config)
           | ServerDriverLocalNotReady ->
               server_driver_connected
                 d
                 'st0
                 'certificate_chain
                 'credential_identity
                 'received
                 'sent **
               pts_to payload 'payload_bytes
           | ServerDriverLocalStepFailed ->
               pure False
           | ServerDriverLocalUnsupported ->
               pure False)
{
  assert (pure (B.length (Ghost.reveal 'payload_bytes) == 64));
  assert (pure (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32 ==
    Seq.slice (Ghost.reveal 'payload_bytes) 0 32));
  Seq.lemma_len_slice (Ghost.reveal 'payload_bytes) 0 32;
  assert (pure (B.length (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32) == 32));
  assert (pure (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64 ==
    Seq.slice (Ghost.reveal 'payload_bytes) 32 64));
  Seq.lemma_len_slice (Ghost.reveal 'payload_bytes) 32 64;
  assert (pure (B.length (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64) == 32));
  let server_random : erased (b:B.bytes{B.length b == 32}) =
    Ghost.hide (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32);
  let server_private_key : erased (b:B.bytes{B.length b == 32}) =
    Ghost.hide (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64);
  assert (pure (Ghost.reveal server_random ==
    CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32));
  assert (pure (Ghost.reveal server_private_key ==
    CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64));

  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));

  rewrite (S.connection_exactly d.server_driver_server 'st0)
    as (CR.connection_exactly d.server_driver_server 'st0);
  let ready =
    CQ.can_select_supported_server_parameters_runtime
      d.server_driver_server
      #server_random
      #server_private_key;
  rewrite (CR.connection_exactly d.server_driver_server 'st0)
    as (S.connection_exactly d.server_driver_server 'st0);
  if ready {
    assert (pure (ready));
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloReceived));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role ==
      CS.ServerEndpoint));
    assert (pure (CR.server_selection_absent
      'st0.CS.cs_model.CS.model_handshake));
    assert (pure (
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
        None));
    assert (pure (
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
        None));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                        'st0.CS.cs_model.CS.model_config.CS.config_server with
      | Some selected_ch, Some cfg ->
        let selection = {
          CS.server_selected_client_hello = selected_ch;
          CS.server_selected_cipher_suite =
            T.TLS_CHACHA20_POLY1305_SHA256;
          CS.server_selected_group = T.X25519;
          CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
          CS.server_random = Ghost.reveal server_random;
          CS.server_key_share_private = Some (Ghost.reveal server_private_key);
          CS.server_key_share_public =
            CryptoSpec.x25519_public_from_private
              (Ghost.reveal server_private_key);
          CS.server_selected_credential = cfg.CS.server_credential_identity;
        } in
        CM.can_select_server_parameters 'st0 selection
      | _, _ -> False));
    Seq.lemma_eq_elim
      (Ghost.reveal server_random)
      (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32);
    Seq.lemma_eq_elim
      (Ghost.reveal server_private_key)
      (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64);
    lemma_select_server_parameters_input_ready_intro
      'st0
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal server_random)
      (Ghost.reveal server_private_key);
    fold (server_driver_connected
      d
      'st0
      'certificate_chain
      'credential_identity
      'received
      'sent);
    let resp =
      select_default_server_parameters_from_payload_once
        d
        payload
        payload_len;
    with st1.
      assert (server_driver_connected
        d
        st1
        'certificate_chain
        'credential_identity
        'received
        'sent);
    assert (pure (server_driver_selection_from_payload_correct
      'st0
      st1
      (Ghost.reveal 'payload_bytes)));
    assert (pure (st1.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    ServerDriverLocalProcessed
  } else {
    fold (server_driver_connected
      d
      'st0
      'certificate_chain
      'credential_identity
      'received
      'sent);
    ServerDriverLocalNotReady
  }
}

fn select_and_derive_shared_secret_from_payload_once
  (d:server_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 SZ.v payload_len == 64 /\
                 ST.server_local_event_input_ready
                   'st0
                   ST.LocalSelectServerParameters
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st2 sent'.
          server_driver_connected
            d
            st2
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pts_to payload 'payload_bytes **
          pure (server_driver_select_derive_from_payload_success_correct
            'st0
            st2
            resp
            (Ghost.reveal 'payload_bytes) /\
          st2.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config)
{
  let _ =
    select_default_server_parameters_from_payload_once
      d
      payload
      payload_len;
  with st1.
    assert (
      server_driver_connected
        d
        st1
        'certificate_chain
        'credential_identity
        'received
        'sent **
      pts_to payload 'payload_bytes **
      pure (server_driver_selection_from_payload_correct
        'st0
        st1
        (Ghost.reveal 'payload_bytes)));

  let mut server_random = [| 0uy; 32sz |];
  let mut server_private_key = [| 0uy; 32sz |];
  Mat.copy_server_random_and_private_from_payload
    payload
    server_random
    server_private_key;
  with server_random_bytes. assert (pts_to server_random server_random_bytes);
  with server_private_key_bytes.
    assert (pts_to server_private_key server_private_key_bytes);
  assert (pure (B.length server_private_key_bytes == 32));
  assert (pure (Seq.equal
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64)));
  Seq.lemma_eq_elim
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64);
  assert (pure (ST.server_local_event_input_ready
    st1
    ST.LocalDeriveSharedSecret
    server_private_key_bytes));
  let resp =
    derive_shared_secret_from_payload_once
      d
      server_private_key
      32sz;
  with st2 sent'.
    assert (
      server_driver_connected
        d
        st2
        'certificate_chain
        'credential_identity
        'received
        sent' **
      pts_to server_private_key server_private_key_bytes **
      pure (server_driver_local_write_correct
        st1
        st2
        resp
        ST.LocalDeriveSharedSecret
        server_private_key_bytes
        (Ghost.reveal 'sent)
        sent' /\
      server_driver_derive_shared_secret_success_correct
        st1
        st2
        resp
        server_private_key_bytes /\
      st2.CS.cs_model.CS.model_config ==
        st1.CS.cs_model.CS.model_config));
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure (st2.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure (Seq.equal
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64)));
  Seq.lemma_eq_elim
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64);
  assert (pure (server_driver_select_derive_from_payload_success_correct
    'st0
    st2
    resp
    (Ghost.reveal 'payload_bytes)));
  resp
}

fn send_server_hello_from_payload_once
  (d:server_driver)
 (payload:array U8.t)
 (payload_len:SZ.t)
 requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 SZ.v payload_len == 64 /\
                 ST.server_local_event_input_ready
                   'st0
                   ST.LocalSendServerHello
                   (Ghost.reveal 'payload_bytes) /\
                 // TODO-A1: ServerHello random must differ from the HelloRetryRequest
                 // sentinel (serverHello_body_cst); unprovable for a symbolic payload slice.
                 // Plus can_send_server_hello needs the build-direction SH witness (deleted
                 // Reveal layer). Both become explicit caller obligations.
                 (Seq.length (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32) == 32 ==>
                  (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32 <: Seq.lseq U8.t 32)
                    <> GSHbody.serverHello_body_cst) /\
                 (let sh = SS.mk_server_hello_witness
                            (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32)
                            (CryptoSpec.x25519_public_from_private
                              (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64))
                            T.TLS_CHACHA20_POLY1305_SHA256 in
                  CM.can_send_server_hello 'st0 sh
                    (CS.serialized_cleartext_tls_message
                      (M.TlsHandshake (M.ServerHello sh)))))
 returns resp:ST.server_response
 ensures exists* st1 sent'.
         server_driver_connected
           d
           st1
           'certificate_chain
           'credential_identity
           'received
           sent' **
         pts_to payload 'payload_bytes **
         pure (server_driver_local_write_correct
           'st0
           st1
           resp
           ST.LocalSendServerHello
           (Ghost.reveal 'payload_bytes)
           (Ghost.reveal 'sent)
           sent' /\
         server_driver_send_server_hello_from_payload_success_correct
           'st0
           st1
           resp
           (Ghost.reveal 'payload_bytes) /\
         st1.CS.cs_model.CS.model_config ==
           'st0.CS.cs_model.CS.model_config)
{
 unfold (server_driver_connected
   d
   'st0
   'certificate_chain
   'credential_identity
   'received
   'sent);
 with ch buffered buffered_len.
   assert (Box.pts_to d.server_driver_channel (Some ch) **
           IO.is_channel ch 'received 'sent **
           server_driver_buffers d buffered buffered_len);
 assert (pure (ST.server_end_to_end_invariant 'st0));
 assert (pure (server_driver_wire_logs_match
   'st0
   'received
   'sent
   buffered
   buffered_len));

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
 with server_hello_out_bytes.
   assert (pts_to server_hello_out server_hello_out_bytes);
 unfold (server_driver_buffers d buffered buffered_len);
 with empty_payload raw network_out material cv_input signature app_out.
   assert (
     Box.pts_to d.server_driver_buffered_len buffered_len **
     V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
     V.pts_to d.server_driver_raw #1.0R raw **
     V.pts_to d.server_driver_network_out #1.0R network_out **
     V.pts_to d.server_driver_material_payload #1.0R material **
     V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
     V.pts_to d.server_driver_signature #1.0R signature **
     V.pts_to d.server_driver_app_out #1.0R app_out);
 V.to_array_pts_to d.server_driver_app_out;
 assert (pure (B.length server_random_bytes == 32));
 assert (pure (B.length server_private_key_bytes == 32));
 assert (pure (B.length server_hello_out_bytes == 95));
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
 assert (pure (let sh = SS.mk_server_hello_witness
     server_random_bytes
     (CryptoSpec.x25519_public_from_private server_private_key_bytes)
     T.TLS_CHACHA20_POLY1305_SHA256 in
   CM.can_send_server_hello
     'st0
     sh
     (CS.serialized_cleartext_tls_message
       (M.TlsHandshake (M.ServerHello sh)))));

 let resp =
   S.process_send_server_hello_with_derived_public_from_private_array
     d.server_driver_server
     server_random
     server_private_key
     server_hello_out
     95sz
     (V.vec_to_array d.server_driver_app_out)
     driver_app_out_capacity;
 with st1 network_out_bytes app_out_bytes.
   assert (
     S.connection_exactly d.server_driver_server st1 **
     pts_to server_random server_random_bytes **
     pts_to server_private_key server_private_key_bytes **
     pts_to server_hello_out network_out_bytes **
     pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
 assert (pure (B.length network_out_bytes == 95));
 assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
 assert (pure (Seq.equal
   network_out_bytes
   (CS.serialized_cleartext_tls_message
     (M.TlsHandshake
       (M.ServerHello
         (SS.mk_server_hello_witness
           server_random_bytes
           (CryptoSpec.x25519_public_from_private server_private_key_bytes)
           T.TLS_CHACHA20_POLY1305_SHA256))))));
 Seq.lemma_eq_elim
   network_out_bytes
   (CS.serialized_cleartext_tls_message
     (M.TlsHandshake
       (M.ServerHello
         (SS.mk_server_hello_witness
           server_random_bytes
           (CryptoSpec.x25519_public_from_private server_private_key_bytes)
           T.TLS_CHACHA20_POLY1305_SHA256))));
 assert (pure (server_driver_send_server_hello_from_payload_success_correct
   'st0
   st1
   resp
   (Ghost.reveal 'payload_bytes)));
 assert (pure (ST.server_local_event_end_to_end_correct
   'st0
   st1
   resp
   ST.LocalSendServerHello
   B.empty
   network_out_bytes
   app_out_bytes));
 SP.lemma_server_local_event_progress
   'st0
   st1
   resp
   ST.LocalSendServerHello
   B.empty
   network_out_bytes
   app_out_bytes;
 advance_server_driver_canonical_progress
   d 'st0 st1;
 ST.lemma_local_send_server_hello_payload_irrelevant
   'st0
   st1
   resp
   B.empty
   (Ghost.reveal 'payload_bytes)
   network_out_bytes
   app_out_bytes;
 assert (pure (ST.server_local_event_end_to_end_correct
   'st0
   st1
   resp
   ST.LocalSendServerHello
   (Ghost.reveal 'payload_bytes)
   network_out_bytes
   app_out_bytes));
 assert (pure (ST.server_end_to_end_invariant st1));
 lemma_local_event_wire_lengths
   'st0
   st1
   resp
   ST.LocalSendServerHello
   (Ghost.reveal 'payload_bytes)
   network_out_bytes
   app_out_bytes;
 assert (pure (SZ.v resp.ST.network_out_len <= B.length network_out_bytes));

 let current_channel = Box.(!d.server_driver_channel);
 assert (pure (current_channel == Some ch));
 assert (pure (Some? current_channel));
 let concrete_ch = Some?.v current_channel;
 assert (pure (current_channel == Some concrete_ch));
 assert (pure (Some concrete_ch == Some ch));
 rewrite (IO.is_channel ch 'received 'sent) as
   (IO.is_channel concrete_ch 'received 'sent);
 let written =
   IO.write
     concrete_ch
     server_hello_out
     resp.ST.network_out_len;
 assert (pure (written == resp.ST.network_out_len));
 assert (pure (SZ.v written <= B.length network_out_bytes));
 rewrite
   (IO.is_channel
     concrete_ch
     'received
     (B.append
       (Ghost.reveal 'sent)
       (if SZ.v written <= B.length network_out_bytes
        then Seq.slice network_out_bytes 0 (SZ.v written)
        else B.empty)))
   as
   (IO.is_channel
     ch
     'received
     (B.append
       (Ghost.reveal 'sent)
       (if SZ.v written <= B.length network_out_bytes
        then Seq.slice network_out_bytes 0 (SZ.v written)
        else B.empty)));
 Seq.lemma_len_slice network_out_bytes 0 (SZ.v written);
 assert (pure (Seq.equal
   (if SZ.v written <= B.length network_out_bytes
    then Seq.slice network_out_bytes 0 (SZ.v written)
    else B.empty)
   (ST.response_network_out resp network_out_bytes)));
 let old_consumed =
   choose_server_driver_wire_logs_consumed
     'st0
     (Ghost.reveal 'received)
     (Ghost.reveal 'sent)
     buffered
     buffered_len;
 assert (pure (server_driver_wire_logs_match_witness
   'st0
   (Ghost.reveal 'received)
   (Ghost.reveal 'sent)
   (Ghost.reveal old_consumed)
   buffered
   buffered_len));
 assert (pure (Seq.equal
   (Ghost.reveal 'sent)
   'st0.CS.cs_wire_log.CL.raw_sent));
 Seq.lemma_eq_elim
   (Ghost.reveal 'sent)
   'st0.CS.cs_wire_log.CL.raw_sent;
 assert (pure (Seq.equal
   st1.CS.cs_wire_log.CL.raw_sent
   (B.append
     'st0.CS.cs_wire_log.CL.raw_sent
     (ST.response_network_out resp network_out_bytes))));
 assert (pure (Seq.equal
   st1.CS.cs_wire_log.CL.raw_received
   'st0.CS.cs_wire_log.CL.raw_received));
 Seq.lemma_eq_elim
   st1.CS.cs_wire_log.CL.raw_received
   'st0.CS.cs_wire_log.CL.raw_received;
 assert (pure (Seq.equal
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty))
   st1.CS.cs_wire_log.CL.raw_sent));
 Seq.lemma_eq_elim
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty))
   st1.CS.cs_wire_log.CL.raw_sent;
 lemma_client_hello_received_not_failed 'st0;
 lemma_server_driver_wire_logs_match_witness_sent
   'st0
   st1
   (Ghost.reveal 'received)
   (Ghost.reveal 'sent)
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty))
   (Ghost.reveal old_consumed)
   buffered
   buffered_len;
 assert (pure (server_driver_wire_logs_match
   st1
   (Ghost.reveal 'received)
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty))
   buffered
   buffered_len));
 assert (pure (st1.CS.cs_model.CS.model_config ==
   'st0.CS.cs_model.CS.model_config));
 assert (pure (server_driver_config_matches_credentials
   st1
   'certificate_chain
   'credential_identity));
 assert (pure (
   st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
     'st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
 assert (pure (st1.CS.cs_model.CS.model_control ==
   CS.ControlHandshaking CS.HsServerHelloSent));
 assert (pure (server_driver_selection_present_when_required st1));
 assert (pure (server_driver_supported_profile_selection
   st1
   'credential_identity));

 V.to_vec_pts_to d.server_driver_app_out;
 fold (server_driver_buffers d buffered buffered_len);
 CPI.lemma_bytes_extends_refl (Ghost.reveal 'received);
 CPI.lemma_bytes_extends_append
   (Ghost.reveal 'sent)
   (if SZ.v written <= B.length network_out_bytes
    then Seq.slice network_out_bytes 0 (SZ.v written)
    else B.empty);
 advance_server_driver_io_history
   d
   'received
   'sent
   'received
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty));
 fold (server_driver_connected
   d
   st1
   'certificate_chain
   'credential_identity
   'received
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty)));
 assert (pure (Seq.equal
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty))
   (B.append
     (Ghost.reveal 'sent)
     (ST.response_network_out resp network_out_bytes))));
 lemma_server_driver_local_write_correct_intro
   'st0
   st1
   resp
   ST.LocalSendServerHello
   (Ghost.reveal 'payload_bytes)
   (Ghost.reveal 'sent)
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty))
   network_out_bytes
   app_out_bytes;
 assert (pure (server_driver_local_write_correct
   'st0
   st1
   resp
   ST.LocalSendServerHello
   (Ghost.reveal 'payload_bytes)
   (Ghost.reveal 'sent)
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty))));
 lemma_server_driver_local_write_correct_preserves_config
   'st0
   st1
   resp
   ST.LocalSendServerHello
   (Ghost.reveal 'payload_bytes)
   (Ghost.reveal 'sent)
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty));
 resp
}

#push-options "--z3rlimit 15"
fn select_derive_send_server_hello_from_payload_once
 (d:server_driver)
 (payload:array U8.t)
 (payload_len:SZ.t)
 requires server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent **
          pts_to payload 'payload_bytes **
          pure (B.length 'payload_bytes == SZ.v payload_len /\
                SZ.v payload_len == 64 /\
                ST.server_local_event_input_ready
                  'st0
                  ST.LocalSelectServerParameters
                  (Ghost.reveal 'payload_bytes) /\
                // TODO-A1: ServerHello random must differ from the HelloRetryRequest
                // sentinel (serverHello_body_cst); unprovable for a symbolic payload slice.
                // Plus the serialized ServerHello length equation (deleted
                // lemma_serialize_server_hello_len). Both become explicit caller obligations.
                (Seq.length (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32) == 32 ==>
                 (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32 <: Seq.lseq U8.t 32)
                   <> GSHbody.serverHello_body_cst) /\
                (let sh = SS.mk_server_hello_witness
                           (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32)
                           (CryptoSpec.x25519_public_from_private
                             (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64))
                           T.TLS_CHACHA20_POLY1305_SHA256 in
                 B.length (W.serialize_handshake (M.ServerHello sh)) == 90))
 returns result:server_driver_select_derive_server_hello_result
 ensures (match result with
          | ServerDriverSelectDeriveServerHelloOk ->
            exists* st3 sent_after_send.
              server_driver_connected
                d
                st3
                'certificate_chain
                'credential_identity
                'received
                sent_after_send **
              pts_to payload 'payload_bytes **
              pure (st3.CS.cs_model.CS.model_config ==
                'st0.CS.cs_model.CS.model_config)
          | ServerDriverSelectDeriveServerHelloDeriveFailed ->
            exists* st2 sent_after_derive.
              server_driver_connected
                d
                st2
                'certificate_chain
                'credential_identity
                'received
                sent_after_derive **
              pts_to payload 'payload_bytes **
              pure (st2.CS.cs_model.CS.model_config ==
                'st0.CS.cs_model.CS.model_config)
          | ServerDriverSelectDeriveServerHelloSendNotReady ->
            exists* st2 sent_after_derive.
              server_driver_connected
                d
                st2
                'certificate_chain
                'credential_identity
                'received
                sent_after_derive **
              pts_to payload 'payload_bytes **
              pure (st2.CS.cs_model.CS.model_config ==
                'st0.CS.cs_model.CS.model_config))
{
 let derive_resp =
   select_and_derive_shared_secret_from_payload_once
     d
     payload
     payload_len;
 with st2 sent_after_derive.
   assert (
     server_driver_connected
       d
       st2
       'certificate_chain
       'credential_identity
       'received
       sent_after_derive **
     pts_to payload 'payload_bytes **
     pure (server_driver_select_derive_from_payload_success_correct
       'st0
       st2
       derive_resp
       (Ghost.reveal 'payload_bytes) /\
     st2.CS.cs_model.CS.model_config ==
       'st0.CS.cs_model.CS.model_config));

 if (derive_resp.ST.status = ST.StepOk) {
   assert (pure (derive_resp.ST.status == ST.StepOk));
   unfold (server_driver_connected
     d
     st2
     'certificate_chain
     'credential_identity
     'received
     sent_after_derive);
   with ch2 buffered2 buffered_len2.
     assert (
       Box.pts_to d.server_driver_channel (Some ch2) **
       IO.is_channel ch2 'received sent_after_derive **
       server_driver_buffers d buffered2 buffered_len2);
   rewrite (S.connection_exactly d.server_driver_server st2)
     as (CR.connection_exactly d.server_driver_server st2);
   let ready =
     CQ.can_send_server_hello_runtime
       d.server_driver_server;
   rewrite (CR.connection_exactly d.server_driver_server st2)
     as (S.connection_exactly d.server_driver_server st2);
   fold (server_driver_connected
     d
     st2
     'certificate_chain
     'credential_identity
     'received
     sent_after_derive);
   if ready {
     assert (pure (ready));
     assert (pure (st2.CS.cs_model.CS.model_control ==
       CS.ControlHandshaking CS.HsClientHelloReceived));
     assert (pure (st2.CS.cs_model.CS.model_config.CS.config_role ==
       CS.ServerEndpoint));
     assert (pure (Some?
       st2.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret));
     assert (pure (
       st2.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None));
     assert (pure (Some?
       st2.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
     assert (pure (
       B.length st2.CS.cs_model.CS.model_handshake.CS.hs_transcript + 90 <=
         Bounds.max_transcript_len));
     lemma_select_derive_success_server_hello_ready
       'st0
       st2
       derive_resp
       (Ghost.reveal 'payload_bytes);
     assert (pure (ST.server_local_event_input_ready
       st2
       ST.LocalSendServerHello
       (Ghost.reveal 'payload_bytes)));
     assert (pure ((Some?.v st2.CS.cs_model.CS.model_handshake.CS.hs_server_selection).CS.server_selected_cipher_suite ==
       T.TLS_CHACHA20_POLY1305_SHA256));
     assert (pure (Seq.length (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32) == 32 ==>
       (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32 <: Seq.lseq U8.t 32)
         <> GSHbody.serverHello_body_cst));
     assert (pure (let sh = SS.mk_server_hello_witness
                     (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32)
                     (CryptoSpec.x25519_public_from_private
                       (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64))
                     T.TLS_CHACHA20_POLY1305_SHA256 in
       B.length (W.serialize_handshake (M.ServerHello sh)) == 90));
     lemma_assemble_can_send_server_hello st2 (Ghost.reveal 'payload_bytes);
     assert (pure (let sh = SS.mk_server_hello_witness
                     (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32)
                     (CryptoSpec.x25519_public_from_private
                       (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64))
                     T.TLS_CHACHA20_POLY1305_SHA256 in
       CM.can_send_server_hello st2 sh
         (CS.serialized_cleartext_tls_message
           (M.TlsHandshake (M.ServerHello sh)))));
     let send_resp =
       send_server_hello_from_payload_once
         d
         payload
         payload_len;
     with st3 sent_after_send.
       assert (
         server_driver_connected
           d
           st3
           'certificate_chain
           'credential_identity
           'received
           sent_after_send **
         pts_to payload 'payload_bytes **
         pure (server_driver_local_write_correct
           st2
           st3
           send_resp
           ST.LocalSendServerHello
           (Ghost.reveal 'payload_bytes)
           sent_after_derive
           sent_after_send /\
         server_driver_send_server_hello_from_payload_success_correct
           st2
           st3
           send_resp
           (Ghost.reveal 'payload_bytes) /\
         st3.CS.cs_model.CS.model_config ==
           st2.CS.cs_model.CS.model_config));
      assert (pure (st2.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      assert (pure (st3.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
     assert (pure (derive_resp.ST.status == ST.StepOk));
     assert (pure (server_driver_select_derive_from_payload_success_correct
       'st0
       st2
       derive_resp
       (Ghost.reveal 'payload_bytes)));
     assert (pure (server_driver_local_write_correct
       st2
       st3
       send_resp
       ST.LocalSendServerHello
       (Ghost.reveal 'payload_bytes)
       sent_after_derive
       sent_after_send));
     assert (pure (server_driver_send_server_hello_from_payload_success_correct
       st2
       st3
       send_resp
       (Ghost.reveal 'payload_bytes)));
     assert (
       server_driver_connected
         d
         st3
         'certificate_chain
         'credential_identity
         'received
         sent_after_send **
       pts_to payload 'payload_bytes **
       pure (st3.CS.cs_model.CS.model_config ==
         'st0.CS.cs_model.CS.model_config));
     ServerDriverSelectDeriveServerHelloOk
   } else {
     assert (pure (derive_resp.ST.status == ST.StepOk));
     assert (pure (server_driver_select_derive_from_payload_success_correct
       'st0
       st2
       derive_resp
       (Ghost.reveal 'payload_bytes)));
     assert (
       server_driver_connected
         d
         st2
         'certificate_chain
         'credential_identity
         'received
         sent_after_derive **
       pts_to payload 'payload_bytes **
       pure (st2.CS.cs_model.CS.model_config ==
         'st0.CS.cs_model.CS.model_config));
     ServerDriverSelectDeriveServerHelloSendNotReady
   }
 } else {
   assert (pure (derive_resp.ST.status <> ST.StepOk));
   assert (pure (server_driver_select_derive_from_payload_success_correct
     'st0
     st2
     derive_resp
     (Ghost.reveal 'payload_bytes)));
   assert (
     server_driver_connected
       d
       st2
       'certificate_chain
       'credential_identity
       'received
       sent_after_derive **
     pts_to payload 'payload_bytes **
     pure (st2.CS.cs_model.CS.model_config ==
       'st0.CS.cs_model.CS.model_config));
   ServerDriverSelectDeriveServerHelloDeriveFailed
 }
}
#pop-options

fn select_and_derive_shared_secret_once
 (d:server_driver)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (ST.server_local_event_input_ready
             'st0
             ST.LocalSelectServerParameters
             (Seq.create 64 0uy))
  returns resp:ST.server_response
  ensures exists* st2 sent'.
          server_driver_connected
            d
            st2
            'certificate_chain
            'credential_identity
            'received
            sent' **
           pure (st2.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config)
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));

  unfold (server_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out material cv_input signature app_out.
    assert (
      Box.pts_to d.server_driver_buffered_len buffered_len **
      V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.server_driver_raw #1.0R raw **
      V.pts_to d.server_driver_network_out #1.0R network_out **
      V.pts_to d.server_driver_material_payload #1.0R material **
      V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
      V.pts_to d.server_driver_signature #1.0R signature **
      V.pts_to d.server_driver_app_out #1.0R app_out);
  V.to_array_pts_to d.server_driver_material_payload;
  V.to_array_pts_to d.server_driver_network_out;
  V.to_array_pts_to d.server_driver_app_out;
  with material_bytes.
    assert (pts_to (V.vec_to_array d.server_driver_material_payload) material_bytes);
  assert (pure (B.length material_bytes == SZ.v driver_material_capacity));
  assert (pure (B.length material_bytes == 64));
  lemma_select_server_parameters_ready_payload_irrelevant
    'st0
    (Seq.create 64 0uy)
    material_bytes;
  assert (pure (ST.server_local_event_input_ready
    'st0
    ST.LocalSelectServerParameters
    material_bytes));

  let mut server_random = [| 0uy; 32sz |];
  let mut server_private_key = [| 0uy; 32sz |];
  Mat.copy_server_random_and_private_from_payload
    (V.vec_to_array d.server_driver_material_payload)
    server_random
    server_private_key;
  with server_random_bytes. assert (pts_to server_random server_random_bytes);
  with server_private_key_bytes.
    assert (pts_to server_private_key server_private_key_bytes);
  assert (pure (B.length server_random_bytes == 32));
  assert (pure (B.length server_private_key_bytes == 32));
  assert (pure (Seq.equal
    server_random_bytes
    (CL.raw_slice material_bytes 0 32)));
  assert (pure (Seq.equal
    server_private_key_bytes
    (CL.raw_slice material_bytes 32 64)));
  Seq.lemma_eq_elim
    server_random_bytes
    (CL.raw_slice material_bytes 0 32);
  Seq.lemma_eq_elim
    server_private_key_bytes
    (CL.raw_slice material_bytes 32 64);
  lemma_select_server_parameters_call_ready
    'st0
    material_bytes
    network_out
    app_out;

  let select_resp =
    S.process_select_default_server_parameters_with_derived_public_from_private_array
      d.server_driver_server
      server_random
      server_private_key
      (V.vec_to_array d.server_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.server_driver_app_out)
      driver_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (
      S.connection_exactly d.server_driver_server st1 **
      pts_to server_random server_random_bytes **
      pts_to server_private_key server_private_key_bytes **
      pts_to (V.vec_to_array d.server_driver_network_out) network_out_bytes **
      pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
  lemma_some_default_server_parameters_state
    'st0
    st1
    server_random_bytes
    server_private_key_bytes;
  SP.lemma_server_local_event_progress
    'st0
    st1
    select_resp
    ST.LocalSelectServerParameters
    B.empty
    network_out_bytes
    app_out_bytes;
  advance_server_driver_canonical_progress
    d 'st0 st1;
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure (st1.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived));
  assert (pure (st1.CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (
    st1.CS.cs_model.CS.model_handshake.CS.hs_keys ==
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys));
  assert (pure (
    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
      None));
  assert (pure (
    st1.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret));
  assert (pure (
    st1.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
      None));
  assert (pure (Some?
    st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure (Some?
    st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
  assert (pure (CS.server_selection_key_share_consistent
    (Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection)));
  assert (pure (Some?
    (Some?.v
      st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection).
        CS.server_key_share_private));
  assert (pure (
    Some?.v
      (Some?.v
        st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection).
          CS.server_key_share_private ==
      server_private_key_bytes));
  assert (pure (B.length (CL.raw_slice material_bytes 32 64) == 32));
  assert (pure (match st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
    | Some selection1 ->
      CS.server_selection_key_share_consistent selection1 /\
      st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
        Some selection1.CS.server_selected_client_hello /\
      Some? selection1.CS.server_key_share_private /\
      Some?.v selection1.CS.server_key_share_private == server_private_key_bytes
    | None -> False));
  lemma_server_local_event_input_ready_derive_shared_secret_intro
    st1
    server_private_key_bytes;
  assert (pure (ST.server_local_event_input_ready
    st1
    ST.LocalDeriveSharedSecret
    server_private_key_bytes));
  assert (pure (ST.server_end_to_end_invariant st1));
  CL.lemma_append_empty_right 'st0.CS.cs_wire_log.CL.raw_sent;
  CL.lemma_append_empty_right 'st0.CS.cs_wire_log.CL.raw_received;
  lemma_selected_server_parameters_state_wire_log
    'st0
    (Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
  assert (pure ('st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived));
  lemma_client_hello_received_not_failed 'st0;
  lemma_client_hello_received_not_failed st1;
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received));
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    'st0.CS.cs_wire_log.CL.raw_sent));
  lemma_server_driver_wire_logs_match_nonfailed_stutter
    'st0
    st1
    'received
    'sent
    buffered
    buffered_len;
  assert (pure (server_driver_wire_logs_match
    st1
    'received
    'sent
    buffered
    buffered_len));
  assert (pure (server_driver_config_matches_credentials
    st1
    'certificate_chain
    'credential_identity));
  lemma_client_hello_received_selection_present st1;
  assert (pure (
    (Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection).
      CS.server_selected_signature_scheme ==
      T.Rsa_pss_rsae_sha256));
  assert (pure (
    (Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection).
      CS.server_selected_credential ==
      'credential_identity));
  assert (pure (server_driver_supported_profile_selection
    st1
    'credential_identity));

  V.to_vec_pts_to d.server_driver_material_payload;
  V.to_vec_pts_to d.server_driver_network_out;
  V.to_vec_pts_to d.server_driver_app_out;
  fold (server_driver_buffers d buffered buffered_len);
  fold (server_driver_connected
    d
    st1
    'certificate_chain
    'credential_identity
    'received
    'sent);
  assert (pure (ST.server_local_event_input_ready
    st1
    ST.LocalDeriveSharedSecret
    server_private_key_bytes));
  let resp =
    derive_shared_secret_from_payload_once
      d
      server_private_key
      32sz;
  with st2 sent'.
    assert (
      server_driver_connected
        d
        st2
        'certificate_chain
        'credential_identity
        'received
        sent' **
      pts_to server_private_key server_private_key_bytes **
      pure (st2.CS.cs_model.CS.model_config ==
        st1.CS.cs_model.CS.model_config));
  assert (pure (st2.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  resp
}

fn select_and_derive_shared_secret_if_ready_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent **
           pure (Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                        'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some ch, Some cfg ->
                    CS.cipher_suite_offered
                      cfg.CS.server_supported_cipher_suites
                      T.TLS_CHACHA20_POLY1305_SHA256 /\
                    CS.named_group_offered
                      cfg.CS.server_supported_groups
                      T.X25519 /\
                    CS.signature_scheme_offered
                      cfg.CS.server_allowed_signature_schemes
                      T.Rsa_pss_rsae_sha256 /\
                    CS.sni_policy_accepts cfg.CS.server_sni_policy (Sem.clientHello_server_name ch)
                  | _, _ -> True))
  returns status:server_driver_local_status
  ensures (match status with
           | ServerDriverLocalProcessed ->
             exists* st2 sent'.
               server_driver_connected
                 d
                 st2
                 'certificate_chain
                 'credential_identity
                 'received
                 sent' **
                pure (st2.CS.cs_model.CS.model_config ==
                 'st0.CS.cs_model.CS.model_config)
           | ServerDriverLocalNotReady ->
             server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               'received
               'sent
           | ServerDriverLocalStepFailed ->
             pure False
           | ServerDriverLocalUnsupported ->
             pure False)
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));

  unfold (server_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out material cv_input signature app_out.
    assert (
      Box.pts_to d.server_driver_buffered_len buffered_len **
      V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.server_driver_raw #1.0R raw **
      V.pts_to d.server_driver_network_out #1.0R network_out **
      V.pts_to d.server_driver_material_payload #1.0R material **
      V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
      V.pts_to d.server_driver_signature #1.0R signature **
      V.pts_to d.server_driver_app_out #1.0R app_out);
  assert (pure (B.length material == 64));
  assert (pure (CL.raw_slice material 0 32 ==
    Seq.slice material 0 32));
  Seq.lemma_len_slice material 0 32;
  assert (pure (B.length (CL.raw_slice material 0 32) == 32));
  assert (pure (CL.raw_slice material 32 64 ==
    Seq.slice material 32 64));
  Seq.lemma_len_slice material 32 64;
  assert (pure (B.length (CL.raw_slice material 32 64) == 32));
  let server_random : erased (b:B.bytes{B.length b == 32}) =
    Ghost.hide (CL.raw_slice material 0 32);
  let server_private_key : erased (b:B.bytes{B.length b == 32}) =
    Ghost.hide (CL.raw_slice material 32 64);
  assert (pure (Ghost.reveal server_random ==
    CL.raw_slice material 0 32));
  assert (pure (Ghost.reveal server_private_key ==
    CL.raw_slice material 32 64));

  rewrite (S.connection_exactly d.server_driver_server 'st0)
    as (CR.connection_exactly d.server_driver_server 'st0);
  let ready =
    CQ.can_select_supported_server_parameters_runtime
      d.server_driver_server
      #server_random
      #server_private_key;
  rewrite (CR.connection_exactly d.server_driver_server 'st0)
    as (S.connection_exactly d.server_driver_server 'st0);
  if ready {
    assert (pure (ready));
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloReceived));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role ==
      CS.ServerEndpoint));
    assert (pure (CR.server_selection_absent
      'st0.CS.cs_model.CS.model_handshake));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                        'st0.CS.cs_model.CS.model_config.CS.config_server with
      | Some selected_ch, Some cfg ->
        let selection = {
          CS.server_selected_client_hello = selected_ch;
          CS.server_selected_cipher_suite =
            T.TLS_CHACHA20_POLY1305_SHA256;
          CS.server_selected_group = T.X25519;
          CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
          CS.server_random = Ghost.reveal server_random;
          CS.server_key_share_private = Some (Ghost.reveal server_private_key);
          CS.server_key_share_public =
            CryptoSpec.x25519_public_from_private
              (Ghost.reveal server_private_key);
          CS.server_selected_credential = cfg.CS.server_credential_identity;
        } in
        CM.can_select_server_parameters 'st0 selection
      | _, _ -> False));
    Seq.lemma_eq_elim
      (Ghost.reveal server_random)
      (CL.raw_slice material 0 32);
    Seq.lemma_eq_elim
      (Ghost.reveal server_private_key)
      (CL.raw_slice material 32 64);
    lemma_select_server_parameters_input_ready_intro
      'st0
      material
      (Ghost.reveal server_random)
      (Ghost.reveal server_private_key);
    Seq.lemma_create_len 64 0uy;
    lemma_select_server_parameters_ready_payload_irrelevant
      'st0
      material
      (Seq.create 64 0uy);
    assert (pure (ST.server_local_event_input_ready
      'st0
      ST.LocalSelectServerParameters
      (Seq.create 64 0uy)));
    assert (pure (
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
        None));
    fold (server_driver_buffers d buffered buffered_len);
    fold (server_driver_connected
      d
      'st0
      'certificate_chain
      'credential_identity
      'received
      'sent);
    let resp = select_and_derive_shared_secret_once d;
    with st2 sent'.
      assert (
        server_driver_connected
          d
          st2
          'certificate_chain
          'credential_identity
          'received
          sent' **
        pure (st2.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
    ServerDriverLocalProcessed
  } else {
    fold (server_driver_buffers d buffered buffered_len);
    fold (server_driver_connected
      d
      'st0
      'certificate_chain
      'credential_identity
      'received
      'sent);
    ServerDriverLocalNotReady
  }
}

fn accept_transport_and_start_once
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                 CM.can_start_server 'st0)
  returns status:server_driver_transport_status
  ensures pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerDriverTransportOk ->
             server_driver_connected
               d
               (CM.started_server_state 'st0)
               'certificate_chain
               'credential_identity
               B.empty
               B.empty
           | _ ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity)
{
  let status = accept_transport_once d bind_host bind_host_len port;
  match status {
    ServerDriverTransportOk -> {
      let _ = start_server_once d;
      ServerDriverTransportOk
    }
    ServerDriverListenFailed -> {
      ServerDriverListenFailed
    }
    ServerDriverAcceptFailed -> {
      ServerDriverAcceptFailed
    }
  }
}

fn accept_transport_start_and_read_client_hello
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (network_fuel:SZ.t)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                 CM.can_start_server 'st0)
  returns result:server_driver_accept_client_hello_result
  ensures pts_to bind_host 'bind_host_bytes **
          (match result with
           | ServerDriverAcceptClientHelloTransportOk wait ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (st1.CS.cs_model.CS.model_config ==
                   (CM.started_server_state 'st0).CS.cs_model.CS.model_config /\
                 (wait.server_driver_client_hello_wait_ready == true ==>
                   st1.CS.cs_model.CS.model_control ==
                     CS.ControlHandshaking CS.HsClientHelloReceived /\
                   st1.CS.cs_model.CS.model_config ==
                     (CM.started_server_state 'st0).CS.cs_model.CS.model_config))
           | _ ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity)
{
  let transport =
    accept_transport_and_start_once
      d
      bind_host
      bind_host_len
      port;
  match transport {
    ServerDriverTransportOk -> {
      let wait =
        read_until_client_hello_received
          d
          network_fuel;
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent **
        pure (st1.CS.cs_model.CS.model_config ==
            (CM.started_server_state 'st0).CS.cs_model.CS.model_config /\
          (wait.server_driver_client_hello_wait_ready == true ==>
            st1.CS.cs_model.CS.model_control ==
               CS.ControlHandshaking CS.HsClientHelloReceived /\
             st1.CS.cs_model.CS.model_config ==
               (CM.started_server_state 'st0).CS.cs_model.CS.model_config)));
      ServerDriverAcceptClientHelloTransportOk wait
    }
    ServerDriverListenFailed -> {
      ServerDriverAcceptClientHelloListenFailed
    }
    ServerDriverAcceptFailed -> {
      ServerDriverAcceptClientHelloAcceptFailed
    }
  }
}

fn accept_start_read_client_hello_select_derive_once
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (network_fuel:SZ.t)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                 CM.can_start_server 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some cfg ->
                    CS.cipher_suite_offered
                      cfg.CS.server_supported_cipher_suites
                      T.TLS_CHACHA20_POLY1305_SHA256 /\
                    CS.named_group_offered
                      cfg.CS.server_supported_groups
                      T.X25519 /\
                    CS.signature_scheme_offered
                      cfg.CS.server_allowed_signature_schemes
                      T.Rsa_pss_rsae_sha256 /\
                    cfg.CS.server_sni_policy == None
                  | None -> False))
  returns result:server_driver_accept_select_derive_result
  ensures pts_to bind_host 'bind_host_bytes **
          (match result with
           | ServerDriverAcceptSelectDeriveListenFailed ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity
           | ServerDriverAcceptSelectDeriveAcceptFailed ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity
           | ServerDriverAcceptSelectDeriveClientHelloWait wait ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (wait.server_driver_client_hello_wait_ready == false /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config)
           | ServerDriverAcceptSelectDeriveMaterialFailed ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (st1.CS.cs_model.CS.model_control ==
                 CS.ControlHandshaking CS.HsClientHelloReceived /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config)
           | ServerDriverAcceptSelectDeriveSelectionNotReady ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (st1.CS.cs_model.CS.model_control ==
                 CS.ControlHandshaking CS.HsClientHelloReceived /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config)
           | ServerDriverAcceptSelectDeriveInternalUnsupported ->
             pure False
           | ServerDriverAcceptSelectDeriveOk ->
             exists* st2 received sent.
               server_driver_connected
                 d
                 st2
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
                pure (st2.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config))
{
  let accepted =
    accept_transport_start_and_read_client_hello
      d
      bind_host
      bind_host_len
      port
      network_fuel;
  match accepted {
    ServerDriverAcceptClientHelloListenFailed -> {
      ServerDriverAcceptSelectDeriveListenFailed
    }
    ServerDriverAcceptClientHelloAcceptFailed -> {
      ServerDriverAcceptSelectDeriveAcceptFailed
    }
    ServerDriverAcceptClientHelloTransportOk wait -> {
      with st_ch received sent.
        assert (server_driver_connected
          d
          st_ch
          'certificate_chain
          'credential_identity
          received
          sent **
        pure (st_ch.CS.cs_model.CS.model_config ==
            (CM.started_server_state 'st0).CS.cs_model.CS.model_config /\
          (wait.server_driver_client_hello_wait_ready == true ==>
          st_ch.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived /\
          st_ch.CS.cs_model.CS.model_config ==
            (CM.started_server_state 'st0).CS.cs_model.CS.model_config)));
      assert (pure (
        (CM.started_server_state 'st0).CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
      assert (pure (st_ch.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      if wait.server_driver_client_hello_wait_ready {
        assert (pure (wait.server_driver_client_hello_wait_ready == true));
        assert (pure (st_ch.CS.cs_model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived));
        assert (pure (
          (CM.started_server_state 'st0).CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
        assert (pure (
          st_ch.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
        assert (pure (Some?
          st_ch.CS.cs_model.CS.model_config.CS.config_server));
        assert (pure (
          match st_ch.CS.cs_model.CS.model_config.CS.config_server with
          | Some cfg ->
            CS.cipher_suite_offered
              cfg.CS.server_supported_cipher_suites
              T.TLS_CHACHA20_POLY1305_SHA256 /\
            CS.named_group_offered
              cfg.CS.server_supported_groups
              T.X25519 /\
            CS.signature_scheme_offered
              cfg.CS.server_allowed_signature_schemes
              T.Rsa_pss_rsae_sha256 /\
            cfg.CS.server_sni_policy == None
          | None -> False));
        assert (pure (
          match st_ch.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                st_ch.CS.cs_model.CS.model_config.CS.config_server with
          | Some ch, Some cfg ->
            CS.cipher_suite_offered
              cfg.CS.server_supported_cipher_suites
              T.TLS_CHACHA20_POLY1305_SHA256 /\
            CS.named_group_offered
              cfg.CS.server_supported_groups
              T.X25519 /\
            CS.signature_scheme_offered
              cfg.CS.server_allowed_signature_schemes
              T.Rsa_pss_rsae_sha256 /\
            CS.sni_policy_accepts cfg.CS.server_sni_policy (Sem.clientHello_server_name ch)
          | _, _ -> True));
        let material_ok = generate_server_material_once d;
        assert (server_driver_connected
          d
          st_ch
          'certificate_chain
          'credential_identity
          received
          sent);
        if material_ok {
          assert (pure (
            Some? st_ch.CS.cs_model.CS.model_config.CS.config_server /\
            (match st_ch.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                   st_ch.CS.cs_model.CS.model_config.CS.config_server with
             | Some ch, Some cfg ->
               CS.cipher_suite_offered
                 cfg.CS.server_supported_cipher_suites
                 T.TLS_CHACHA20_POLY1305_SHA256 /\
               CS.named_group_offered
                 cfg.CS.server_supported_groups
                 T.X25519 /\
               CS.signature_scheme_offered
                 cfg.CS.server_allowed_signature_schemes
                 T.Rsa_pss_rsae_sha256 /\
               CS.sni_policy_accepts cfg.CS.server_sni_policy (Sem.clientHello_server_name ch)
             | _, _ -> True)));
          let status = select_and_derive_shared_secret_if_ready_once d;
          match status {
            ServerDriverLocalProcessed -> {
              ServerDriverAcceptSelectDeriveOk
            }
            ServerDriverLocalNotReady -> {
              assert (server_driver_connected
                d
                st_ch
                'certificate_chain
                'credential_identity
                received
                sent);
              assert (pure (st_ch.CS.cs_model.CS.model_control ==
                CS.ControlHandshaking CS.HsClientHelloReceived));
              assert (pure (st_ch.CS.cs_model.CS.model_config ==
                'st0.CS.cs_model.CS.model_config));
              ServerDriverAcceptSelectDeriveSelectionNotReady
            }
            ServerDriverLocalUnsupported -> {
              assert (pure False);
              ServerDriverAcceptSelectDeriveInternalUnsupported
            }
            ServerDriverLocalStepFailed -> {
              assert (pure False);
              ServerDriverAcceptSelectDeriveInternalUnsupported
            }
          }
        } else {
          assert (pure (st_ch.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived));
          assert (pure (st_ch.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
          ServerDriverAcceptSelectDeriveMaterialFailed
        }
      } else {
        assert (pure (wait.server_driver_client_hello_wait_ready == false));
        assert (pure (st_ch.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
        ServerDriverAcceptSelectDeriveClientHelloWait wait
      }
    }
  }
}

#push-options "--z3rlimit 15"
fn accept_start_read_client_hello_select_derive_send_server_hello_once
            (d:server_driver)
            (bind_host:array U8.t)
            (bind_host_len:SZ.t)
            (port:U16.t)
            (network_fuel:SZ.t)
            requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
                     pts_to bind_host 'bind_host_bytes **
                     pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                           CM.can_start_server 'st0 /\
                           Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                           (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                            | Some cfg ->
                              CS.cipher_suite_offered
                                cfg.CS.server_supported_cipher_suites
                                T.TLS_CHACHA20_POLY1305_SHA256 /\
                              CS.named_group_offered
                                cfg.CS.server_supported_groups
                                T.X25519 /\
                              CS.signature_scheme_offered
                                cfg.CS.server_allowed_signature_schemes
                                T.Rsa_pss_rsae_sha256 /\
                              cfg.CS.server_sni_policy == None
                            | None -> False))
            returns result:server_driver_accept_server_hello_result
            ensures pts_to bind_host 'bind_host_bytes **
                    (match result with
                     | ServerDriverAcceptServerHelloListenFailed ->
                       server_driver_live d 'st0 'certificate_chain 'credential_identity
                     | ServerDriverAcceptServerHelloAcceptFailed ->
                       server_driver_live d 'st0 'certificate_chain 'credential_identity
                     | ServerDriverAcceptServerHelloClientHelloWait wait ->
                       exists* st1 received sent.
                         server_driver_connected
                           d
                           st1
                           'certificate_chain
                           'credential_identity
                           received
                           sent **
                         pure (wait.server_driver_client_hello_wait_ready == false /\
                           st1.CS.cs_model.CS.model_config ==
                             'st0.CS.cs_model.CS.model_config)
                     | ServerDriverAcceptServerHelloMaterialFailed
                     | ServerDriverAcceptServerHelloSelectionNotReady ->
                       exists* st1 received sent.
                         server_driver_connected
                           d
                           st1
                           'certificate_chain
                           'credential_identity
                           received
                           sent **
                         pure (st1.CS.cs_model.CS.model_control ==
                           CS.ControlHandshaking CS.HsClientHelloReceived /\
                           st1.CS.cs_model.CS.model_config ==
                             'st0.CS.cs_model.CS.model_config)
                     | ServerDriverAcceptServerHelloDeriveFailed
                     | ServerDriverAcceptServerHelloSendNotReady
                     | ServerDriverAcceptServerHelloOk ->
                       exists* st2 received sent.
                         server_driver_connected
                           d
                           st2
                           'certificate_chain
                           'credential_identity
                           received
                           sent **
                          pure (st2.CS.cs_model.CS.model_config ==
                           'st0.CS.cs_model.CS.model_config))
          {
            let accepted =
              accept_transport_start_and_read_client_hello
                d
                bind_host
                bind_host_len
                port
                network_fuel;
            match accepted {
              ServerDriverAcceptClientHelloListenFailed -> {
                ServerDriverAcceptServerHelloListenFailed
              }

                ServerDriverAcceptClientHelloAcceptFailed -> {
                  ServerDriverAcceptServerHelloAcceptFailed
                }
              ServerDriverAcceptClientHelloTransportOk wait -> {
                with st_ch received sent.
                  assert (server_driver_connected
                    d
                    st_ch
                    'certificate_chain
                    'credential_identity
                    received
                    sent **
                  pure (st_ch.CS.cs_model.CS.model_config ==
                      (CM.started_server_state 'st0).CS.cs_model.CS.model_config /\
                    (wait.server_driver_client_hello_wait_ready == true ==>
                    st_ch.CS.cs_model.CS.model_control ==
                      CS.ControlHandshaking CS.HsClientHelloReceived /\
                    st_ch.CS.cs_model.CS.model_config ==
                      (CM.started_server_state 'st0).CS.cs_model.CS.model_config)));
                 assert (pure (
                  (CM.started_server_state 'st0).CS.cs_model.CS.model_config ==
                    'st0.CS.cs_model.CS.model_config));
                 assert (pure (st_ch.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config));
                if wait.server_driver_client_hello_wait_ready {
                  assert (pure (wait.server_driver_client_hello_wait_ready == true));
                  assert (pure (st_ch.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsClientHelloReceived));
                  assert (pure (
                    (CM.started_server_state 'st0).CS.cs_model.CS.model_config ==
                      'st0.CS.cs_model.CS.model_config));
                  assert (pure (
                    st_ch.CS.cs_model.CS.model_config ==
                      'st0.CS.cs_model.CS.model_config));
                  assert (pure (Some?
                    st_ch.CS.cs_model.CS.model_config.CS.config_server));
                  assert (pure (
                    match st_ch.CS.cs_model.CS.model_config.CS.config_server with
                    | Some cfg ->
                      CS.cipher_suite_offered
                        cfg.CS.server_supported_cipher_suites
                        T.TLS_CHACHA20_POLY1305_SHA256 /\
                      CS.named_group_offered
                        cfg.CS.server_supported_groups
                        T.X25519 /\
                      CS.signature_scheme_offered
                        cfg.CS.server_allowed_signature_schemes
                        T.Rsa_pss_rsae_sha256 /\
                      cfg.CS.server_sni_policy == None
                    | None -> False));
                  assert (pure (
                    match st_ch.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                          st_ch.CS.cs_model.CS.model_config.CS.config_server with
                    | Some ch, Some cfg ->
                      CS.cipher_suite_offered
                        cfg.CS.server_supported_cipher_suites
                        T.TLS_CHACHA20_POLY1305_SHA256 /\
                      CS.named_group_offered
                        cfg.CS.server_supported_groups
                        T.X25519 /\
                      CS.signature_scheme_offered
                        cfg.CS.server_allowed_signature_schemes
                        T.Rsa_pss_rsae_sha256 /\
                      CS.sni_policy_accepts cfg.CS.server_sni_policy (Sem.clientHello_server_name ch)
                    | _, _ -> True));

                  let mut material_payload = [| 0uy; 64sz |];
                  let material_ok = Crypto.random_bytes material_payload 64sz;
                  with material_bytes.
                    assert (pts_to material_payload material_bytes);
                  assert (pure (B.length material_bytes == 64));
                  if material_ok {
                    assert (pure (CL.raw_slice material_bytes 0 32 ==
                      Seq.slice material_bytes 0 32));
                    Seq.lemma_len_slice material_bytes 0 32;
                    assert (pure (B.length (CL.raw_slice material_bytes 0 32) == 32));
                    assert (pure (CL.raw_slice material_bytes 32 64 ==
                      Seq.slice material_bytes 32 64));
                    Seq.lemma_len_slice material_bytes 32 64;
                    assert (pure (B.length (CL.raw_slice material_bytes 32 64) == 32));
                    let server_random : erased (b:B.bytes{B.length b == 32}) =
                      Ghost.hide (CL.raw_slice material_bytes 0 32);
                    let server_private_key : erased (b:B.bytes{B.length b == 32}) =
                      Ghost.hide (CL.raw_slice material_bytes 32 64);
                    assert (pure (Ghost.reveal server_random ==
                      CL.raw_slice material_bytes 0 32));
                    assert (pure (Ghost.reveal server_private_key ==
                      CL.raw_slice material_bytes 32 64));

                    unfold (server_driver_connected
                      d
                      st_ch
                      'certificate_chain
                      'credential_identity
                      received
                      sent);
                    with ch2 buffered2 buffered_len2.
                      assert (
                        Box.pts_to d.server_driver_channel (Some ch2) **
                        IO.is_channel ch2 received sent **
                        server_driver_buffers d buffered2 buffered_len2);
                    rewrite (S.connection_exactly d.server_driver_server st_ch)
                      as (CR.connection_exactly d.server_driver_server st_ch);
                    let ready =
                      CQ.can_select_supported_server_parameters_runtime
                        d.server_driver_server
                        #server_random
                        #server_private_key;
                    rewrite (CR.connection_exactly d.server_driver_server st_ch)
                      as (S.connection_exactly d.server_driver_server st_ch);
                    fold (server_driver_connected
                      d
                      st_ch
                      'certificate_chain
                      'credential_identity
                      received
                      sent);
                    if ready {
                      assert (pure (ready));
                      assert (pure (st_ch.CS.cs_model.CS.model_control ==
                        CS.ControlHandshaking CS.HsClientHelloReceived));
                      assert (pure (st_ch.CS.cs_model.CS.model_config.CS.config_role ==
                        CS.ServerEndpoint));
                      assert (pure (CR.server_selection_absent
                        st_ch.CS.cs_model.CS.model_handshake));
                      assert (pure (Some?
                        st_ch.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
                      assert (pure (Some?
                        st_ch.CS.cs_model.CS.model_config.CS.config_server));
                      assert (pure (match st_ch.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                                          st_ch.CS.cs_model.CS.model_config.CS.config_server with
                        | Some selected_ch, Some cfg ->
                          let selection = {
                            CS.server_selected_client_hello = selected_ch;
                            CS.server_selected_cipher_suite =
                              T.TLS_CHACHA20_POLY1305_SHA256;
                            CS.server_selected_group = T.X25519;
                            CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
                            CS.server_random = Ghost.reveal server_random;
                            CS.server_key_share_private = Some (Ghost.reveal server_private_key);
                            CS.server_key_share_public =
                              CryptoSpec.x25519_public_from_private
                                (Ghost.reveal server_private_key);
                            CS.server_selected_credential = cfg.CS.server_credential_identity;
                          } in
                          CM.can_select_server_parameters st_ch selection
                        | _, _ -> False));
                      Seq.lemma_eq_elim
                        (Ghost.reveal server_random)
                        (CL.raw_slice material_bytes 0 32);
                      Seq.lemma_eq_elim
                        (Ghost.reveal server_private_key)
                        (CL.raw_slice material_bytes 32 64);
                      lemma_select_server_parameters_input_ready_intro
                        st_ch
                        material_bytes
                        (Ghost.reveal server_random)
                        (Ghost.reveal server_private_key);
                      // TODO-A1 cst-guard: discharge via a RUNTIME comparison of the
                      // freshly-generated random against the HRR sentinel, instead of
                      // the (unsatisfiable) universal caller precondition.
                      assert (pure (B.length material_bytes == 64));
                      let differs =
                        SS.server_random_differs_from_cst material_payload;
                      if not differs {
                        // Runtime sentinel collision (cryptographically impossible):
                        // bail out, re-establishing the connected predicate.
                        assert (server_driver_connected
                          d
                          st_ch
                          'certificate_chain
                          'credential_identity
                          received
                          sent);
                        assert (pure (st_ch.CS.cs_model.CS.model_control ==
                          CS.ControlHandshaking CS.HsClientHelloReceived));
                        assert (pure (st_ch.CS.cs_model.CS.model_config ==
                          'st0.CS.cs_model.CS.model_config));
                        ServerDriverAcceptServerHelloMaterialFailed
                      } else {
                        // [differs] establishes the cst-guard for material_bytes; the
                        // ==90 serialized-length follows from the existing lemma.
                        SS.lemma_mk_server_hello_witness_bytesize
                          (CL.raw_slice material_bytes 0 32)
                          (CryptoSpec.x25519_public_from_private
                            (CL.raw_slice material_bytes 32 64))
                          T.TLS_CHACHA20_POLY1305_SHA256;
                        assert (pure (
                          (Seq.length (CL.raw_slice material_bytes 0 32) == 32 ==>
                           (CL.raw_slice material_bytes 0 32 <: Seq.lseq U8.t 32) <>
                             GSHbody.serverHello_body_cst) /\
                          (let sh = SS.mk_server_hello_witness
                                     (CL.raw_slice material_bytes 0 32)
                                     (CryptoSpec.x25519_public_from_private
                                       (CL.raw_slice material_bytes 32 64))
                                     T.TLS_CHACHA20_POLY1305_SHA256 in
                           B.length (W.serialize_handshake (M.ServerHello sh)) == 90)));
                        let server_hello_result =
                          select_derive_send_server_hello_from_payload_once
                            d
                            material_payload
                            64sz;
                        match server_hello_result {
                          ServerDriverSelectDeriveServerHelloOk -> {
                            ServerDriverAcceptServerHelloOk
                          }
                          ServerDriverSelectDeriveServerHelloDeriveFailed -> {
                            ServerDriverAcceptServerHelloDeriveFailed
                          }
                          ServerDriverSelectDeriveServerHelloSendNotReady -> {
                            ServerDriverAcceptServerHelloSendNotReady
                          }
                        }
                      }
                    } else {
                      assert (server_driver_connected
                        d
                        st_ch
                        'certificate_chain
                        'credential_identity
                        received
                        sent);
                      assert (pure (st_ch.CS.cs_model.CS.model_control ==
                        CS.ControlHandshaking CS.HsClientHelloReceived));
                      assert (pure (st_ch.CS.cs_model.CS.model_config ==
                        'st0.CS.cs_model.CS.model_config));
                      ServerDriverAcceptServerHelloSelectionNotReady
                    }
                  } else {
                    assert (server_driver_connected
                      d
                      st_ch
                      'certificate_chain
                      'credential_identity
                      received
                      sent);
                    assert (pure (st_ch.CS.cs_model.CS.model_control ==
                      CS.ControlHandshaking CS.HsClientHelloReceived));
                    assert (pure (st_ch.CS.cs_model.CS.model_config ==
                      'st0.CS.cs_model.CS.model_config));
                    ServerDriverAcceptServerHelloMaterialFailed
                  }
                } else {
                  assert (pure (wait.server_driver_client_hello_wait_ready == false));
                  assert (pure (st_ch.CS.cs_model.CS.model_config ==
                    'st0.CS.cs_model.CS.model_config));
                  ServerDriverAcceptServerHelloClientHelloWait wait
                }
              }
            }
          }
#pop-options

fn accept_start_read_client_hello_select_derive_send_server_hello_drain_empty_once
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (network_fuel:SZ.t)
  (local_fuel:SZ.t)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                 CM.can_start_server 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some cfg ->
                    CS.cipher_suite_offered
                      cfg.CS.server_supported_cipher_suites
                      T.TLS_CHACHA20_POLY1305_SHA256 /\
                    CS.named_group_offered
                      cfg.CS.server_supported_groups
                      T.X25519 /\
                    CS.signature_scheme_offered
                      cfg.CS.server_allowed_signature_schemes
                      T.Rsa_pss_rsae_sha256 /\
                    cfg.CS.server_sni_policy == None
                  | None -> False))
  returns result:server_driver_accept_server_hello_drain_result
  ensures pts_to bind_host 'bind_host_bytes **
          (match result with
           | ServerDriverAcceptServerHelloDrainListenFailed ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity
           | ServerDriverAcceptServerHelloDrainAcceptFailed ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity
           | ServerDriverAcceptServerHelloDrainOk _ ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
                pure (st1.CS.cs_model.CS.model_config ==
                 'st0.CS.cs_model.CS.model_config)
            | ServerDriverAcceptServerHelloDrainClientHelloWait _
            | ServerDriverAcceptServerHelloDrainMaterialFailed
            | ServerDriverAcceptServerHelloDrainSelectionNotReady
            | ServerDriverAcceptServerHelloDrainDeriveFailed
            | ServerDriverAcceptServerHelloDrainSendNotReady ->
              exists* st1 received sent.
                server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
                pure (st1.CS.cs_model.CS.model_config ==
                 'st0.CS.cs_model.CS.model_config))
{
  let accepted =
    accept_start_read_client_hello_select_derive_send_server_hello_once
      d
      bind_host
      bind_host_len
      port
      network_fuel;
  match accepted {
    ServerDriverAcceptServerHelloListenFailed -> {
      ServerDriverAcceptServerHelloDrainListenFailed
    }
    ServerDriverAcceptServerHelloAcceptFailed -> {
      ServerDriverAcceptServerHelloDrainAcceptFailed
    }
    ServerDriverAcceptServerHelloClientHelloWait wait -> {
      with st_wait received_wait sent_wait.
        assert (
          server_driver_connected
            d
            st_wait
            'certificate_chain
            'credential_identity
            received_wait
            sent_wait **
          pure (st_wait.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
      ServerDriverAcceptServerHelloDrainClientHelloWait wait
    }
    ServerDriverAcceptServerHelloMaterialFailed -> {
      with st_material received_material sent_material.
        assert (
          server_driver_connected
            d
            st_material
            'certificate_chain
            'credential_identity
            received_material
            sent_material **
          pure (st_material.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
      ServerDriverAcceptServerHelloDrainMaterialFailed
    }
    ServerDriverAcceptServerHelloSelectionNotReady -> {
      with st_selection received_selection sent_selection.
        assert (
          server_driver_connected
            d
            st_selection
            'certificate_chain
            'credential_identity
            received_selection
            sent_selection **
          pure (st_selection.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
      ServerDriverAcceptServerHelloDrainSelectionNotReady
    }
    ServerDriverAcceptServerHelloDeriveFailed -> {
      with st_derive received_derive sent_derive.
        assert (
          server_driver_connected
            d
            st_derive
            'certificate_chain
            'credential_identity
            received_derive
            sent_derive **
          pure (st_derive.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
      ServerDriverAcceptServerHelloDrainDeriveFailed
    }
    ServerDriverAcceptServerHelloSendNotReady -> {
      with st_send received_send sent_send.
        assert (
          server_driver_connected
            d
            st_send
            'certificate_chain
            'credential_identity
            received_send
            sent_send **
          pure (st_send.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
      ServerDriverAcceptServerHelloDrainSendNotReady
    }
    ServerDriverAcceptServerHelloOk -> {
      with st_sh received_sh sent_sh.
        assert (
          server_driver_connected
            d
            st_sh
            'certificate_chain
            'credential_identity
            received_sh
            sent_sh **
          pure (st_sh.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
      let drain = drain_ready_empty_local_actions d local_fuel;
      with st_drain received_drain sent_drain.
        assert (
          server_driver_connected
            d
            st_drain
            'certificate_chain
            'credential_identity
            received_drain
            sent_drain **
          pure (st_drain.CS.cs_model.CS.model_config ==
            st_sh.CS.cs_model.CS.model_config));
      assert (pure (st_drain.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      ServerDriverAcceptServerHelloDrainOk drain
    }
  }
}
