module TLS13.Impl.Server.Driver.Handshake

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module ID = FStar.IndefiniteDescription
module DN = TLS13.Impl.Server.Driver.Network
module M = TLS13.Messages
module Seq = FStar.Seq
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module W = TLS13.Wire.Spec

open TLS13.Impl.Server.Driver.State
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
          payload1)
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
    CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
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
    CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
    CS.server_random = CL.raw_slice payload1 0 32;
    CS.server_key_share_private = Some (CL.raw_slice payload1 32 64);
    CS.server_key_share_public =
      CryptoSpec.x25519_public_from_private (CL.raw_slice payload1 32 64);
    CS.server_selected_credential = cfg.CS.server_credential_identity;
  } in
  assert (CM.can_select_server_parameters st selection0);
  assert (CS.server_selection_acceptable cfg selection0);
  assert (CS.cipher_suite_offered
    cfg.CS.server_supported_cipher_suites
    T.TLS_CHACHA20_POLY1305_SHA256);
  assert (CS.cipher_suite_offered
    ch.M.cipher_suites
    T.TLS_CHACHA20_POLY1305_SHA256);
  assert (CS.named_group_offered
    cfg.CS.server_supported_groups
    T.X25519);
  assert (CS.signature_scheme_offered
    cfg.CS.server_allowed_signature_schemes
    T.RsaPssRsaeSha256);
  assert (CS.signature_scheme_offered
    ch.M.signature_schemes
    T.RsaPssRsaeSha256);
  assert (CS.sni_policy_accepts cfg.CS.server_sni_policy ch.M.server_name);
  assert (CS.server_selection_key_share_consistent selection1);
  assert (CS.server_selection_acceptable cfg selection1);
  assert (CS.legal_event
    st.CS.cs_model
    (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection1)));
  assert (CM.can_select_server_parameters st selection1)

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
         Bounds.max_transcript_len)
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
  let sh = {
    M.random = server_random;
    M.key_share = CryptoSpec.x25519_public_from_private server_private_key;
    M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
  } in
  assert (exists st1 shared.
    server_driver_selection_from_payload_correct st0 st1 payload /\
    st2 == CM.derived_shared_secret_state st1 shared /\
    (match st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
     | Some ch ->
      CryptoSpec.x25519_shared
        server_private_key
        ch.M.key_share == Some shared
     | None -> False));
  let st1 =
    ID.indefinite_description_ghost
      CS.connection_state
      (fun st1 -> exists shared.
       server_driver_selection_from_payload_correct st0 st1 payload /\
       st2 == CM.derived_shared_secret_state st1 shared /\
       (match st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
        | Some ch ->
          CryptoSpec.x25519_shared
            server_private_key
            ch.M.key_share == Some shared
        | None -> False)) in
  let shared =
    ID.indefinite_description_ghost
      CryptoSpec.x25519_shared_secret
      (fun shared ->
       server_driver_selection_from_payload_correct st0 st1 payload /\
       st2 == CM.derived_shared_secret_state st1 shared /\
       (match st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
        | Some ch ->
          CryptoSpec.x25519_shared
            server_private_key
            ch.M.key_share == Some shared
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
       CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
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
    CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
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
  assert (CS.server_hello_matches_selection selection sh);
  W.lemma_serialize_server_hello_len sh;
  assert (B.length (W.serialize_handshake (M.ServerHello sh)) == 90);
  assert (
    B.length st2.CS.cs_model.CS.model_handshake.CS.hs_transcript +
      B.length (W.serialize_handshake (M.ServerHello sh)) <=
      Bounds.max_transcript_len);
  assert (CS.legal_event
    st2.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    }));
  assert (CS.event_raw_delta_legal
    st2.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    })
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello sh)))
    B.empty);
  assert (CM.can_send_server_hello
    st2
    sh
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello sh))));
  assert (ST.server_local_event_input_ready
    st2
    ST.LocalSendServerHello
    payload)

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
               pure (wait.server_driver_client_hello_wait_ready == true ==>
                   st1.CS.cs_model.CS.model_control ==
                     CS.ControlHandshaking CS.HsClientHelloReceived /\
                   st1.CS.cs_model.CS.model_config ==
                     (CM.started_server_state 'st0).CS.cs_model.CS.model_config)
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
        pure (wait.server_driver_client_hello_wait_ready == true ==>
          st1.CS.cs_model.CS.model_control ==
             CS.ControlHandshaking CS.HsClientHelloReceived /\
           st1.CS.cs_model.CS.model_config ==
             (CM.started_server_state 'st0).CS.cs_model.CS.model_config));
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
