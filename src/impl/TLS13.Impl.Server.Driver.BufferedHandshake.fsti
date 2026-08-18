module TLS13.Impl.Server.Driver.BufferedHandshake

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CryptoSpec = TLS13.Crypto.Spec
module BN = TLS13.Impl.Server.Driver.BufferedNetwork
module DS = TLS13.Impl.Server.Driver.State
module M = TLS13.Messages
module Seq = FStar.Seq
module SS = TLS13.Impl.Server.Send
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module GSHbody = TLS13.Wire.Generated.ServerHello_body
module GNG = TLS13.Wire.Generated.NamedGroup

type server_flight_result =
  | ServerFlightOk
  | ServerFlightDeriveFailed
  | ServerFlightSendNotReady

val lemma_select_server_parameters_input_ready_intro
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
               (CM.server_selected_suite st);
             CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (ch));
             CS.server_selected_signature_scheme =
               CryptoSpec.credential_signature_scheme
                 (cfg.CS.server_credential_identity);
             CS.server_random = server_random;
             CS.server_key_share_private = Some server_private_key;
             CS.server_key_share_public =
               CryptoSpec.x25519_public_from_private server_private_key;
             CS.server_p256_private = Some server_private_key;
             CS.server_p256_public =
               CryptoSpec.p256_public_from_private server_private_key;
             CS.server_selected_credential =
               cfg.CS.server_credential_identity;
           }
         | _ -> False))
      (ensures
        ST.server_local_event_input_ready
          st
          ST.LocalSelectServerParameters
          payload)

noextract
let selection_from_payload_correct
  (st0 st1:CS.connection_state)
  (payload:B.bytes)
  : prop =
  B.length payload == 64 /\
  (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
         st0.CS.cs_model.CS.model_config.CS.config_server with
   | Some ch, Some cfg ->
     let selection = {
       CS.server_selected_client_hello = ch;
       CS.server_selected_cipher_suite = (CM.server_selected_suite st0);
       CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (ch));
       CS.server_selected_signature_scheme =
         CryptoSpec.credential_signature_scheme
           (cfg.CS.server_credential_identity);
       CS.server_random = CL.raw_slice payload 0 32;
       CS.server_key_share_private = Some (CL.raw_slice payload 32 64);
       CS.server_key_share_public =
         CryptoSpec.x25519_public_from_private (CL.raw_slice payload 32 64);
       CS.server_p256_private = Some (CL.raw_slice payload 32 64);
       CS.server_p256_public =
         CryptoSpec.p256_public_from_private (CL.raw_slice payload 32 64);
       CS.server_selected_credential =
         cfg.CS.server_credential_identity;
     } in
     st1 == CM.selected_server_parameters_state st0 selection
   | _ -> False)

noextract
let server_hello_from_payload_correct
  (st0 st1:CS.connection_state)
  (payload:B.bytes)
  : prop =
  B.length payload == 64 /\
  (let sh =
     SS.mk_server_hello_witness (CM.stored_client_hello_named_group st0)
       (CL.raw_slice payload 0 32)
       (CryptoSpec.kex_public_from_private (CM.stored_client_hello_kex_group st0)
         (CL.raw_slice payload 32 64))
       (CM.stored_client_hello_session_id st0)
       (CM.server_selected_suite st0) in
   st1 ==
     CM.sent_server_hello_state
       st0
       sh
       (CS.serialized_cleartext_tls_message
         (M.TlsHandshake (M.ServerHello sh))))

noextract
let derive_shared_secret_from_payload_correct
  (st0 st1:CS.connection_state)
  (resp:ST.server_response)
  (payload:B.bytes)
  : prop =
  B.length payload == 64 /\
  (resp.ST.status == ST.StepOk ==>
   exists shared.
     st1 == CM.derived_shared_secret_state st0 shared /\
     (* G2 stage S6.8d: group-agile; see BN.local_event_success_correct. *)
     (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
      | Some ch ->
       (let g = CM.client_hello_kex_group_for ch in
        match CS.client_hello_kex ch g with
        | Some client_public ->
          CryptoSpec.kex_shared
            g
            (CL.raw_slice payload 32 64)
            client_public == Some shared
        | None -> False)
      | None -> False))

noextract
let select_derive_from_payload_success_correct
  (st0 st2:CS.connection_state)
  (resp:ST.server_response)
  (payload:B.bytes)
  : prop =
  resp.ST.status == ST.StepOk ==>
  exists st1.
    selection_from_payload_correct st0 st1 payload /\
    derive_shared_secret_from_payload_correct st1 st2 resp payload

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
         GSHbody.serverHello_body_cst) /\
      (let sh =
         SS.mk_server_hello_witness (CM.stored_client_hello_named_group 'st0)
           (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32)
           (CryptoSpec.kex_public_from_private (CM.stored_client_hello_kex_group 'st0)
             (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64))
           (CM.stored_client_hello_session_id 'st0)
           (CM.server_selected_suite 'st0) in
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
                (SS.mk_server_hello_witness (CM.stored_client_hello_named_group 'st0)
                  (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32)
                  (CryptoSpec.kex_public_from_private (CM.stored_client_hello_kex_group 'st0)
                    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64))
                  (CM.stored_client_hello_session_id 'st0)
                  (CM.server_selected_suite 'st0)))))
          app_out_bytes)

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

fn select_derive_send_server_hello_from_payload_once
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
        (Ghost.reveal 'payload_bytes) /\
      (Seq.length
         (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32) == 32 ==>
       (CL.raw_slice
          (Ghost.reveal 'payload_bytes)
          0
          32 <: Seq.lseq U8.t 32) <>
         GSHbody.serverHello_body_cst) /\
      (let sh =
         SS.mk_server_hello_witness (CM.stored_client_hello_named_group 'st0)
           (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32)
           (CryptoSpec.kex_public_from_private (CM.stored_client_hello_kex_group 'st0)
             (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64))
           (CM.stored_client_hello_session_id 'st0)
           (CM.server_selected_suite 'st0) in
       B.length (TLS13.Wire.Spec.serialize_handshake (M.ServerHello sh)) ==
         58 + CryptoSpec.kex_public_len (CM.stored_client_hello_kex_group 'st0) + Seq.length (CM.stored_client_hello_session_id 'st0)))
  returns result:server_flight_result
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
        (result == ServerFlightOk ==>
         st1.CS.cs_model.CS.model_control ==
           CS.ControlHandshaking CS.HsServerHelloSent))
