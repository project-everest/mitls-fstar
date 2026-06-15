module TLS13.Impl.Server.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module A = Pulse.Lib.Array
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CT = TLS13.Impl.Client.Types
module Crypto = TLS13.Crypto
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module ID = FStar.IndefiniteDescription
module IM = TLS13.Impl.Messages
module IO = TLS13.IO
module Mat = TLS13.Impl.Server.Material
module M = TLS13.Messages
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module S = TLS13.Impl.Server
module DS = TLS13.Impl.Server.Driver.State
module DT = TLS13.Impl.Server.Driver.Transport
module DN = TLS13.Impl.Server.Driver.Network
module DL = TLS13.Impl.Server.Driver.Local
module DH = TLS13.Impl.Server.Driver.Handshake
module SSetup = TLS13.Impl.Server.Setup
module ST = TLS13.Impl.Server.Types
module Tags = TLS13.Impl.ConnectionState.Tags
module Box = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module RS = TLS13.Record.Spec
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec

type server_driver = DS.server_driver

noextract
let server_driver_wire_logs_match = DS.server_driver_wire_logs_match

noextract
let server_driver_live = DS.server_driver_live

noextract
let server_driver_connected = DS.server_driver_connected

noextract
let server_driver_closed = DS.server_driver_closed

open TLS13.Impl.Server.Driver.State
open TLS13.Impl.Server.Driver.Transport
open TLS13.Impl.Server.Driver.Network
open TLS13.Impl.Server.Driver.Local
open TLS13.Impl.Server.Driver.Handshake

fn new_server
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len /\
                 B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len)
  returns result: option server_driver
  ensures pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (match result with
           | Some d ->
             exists* credential_identity.
               server_driver_live
                 d
                 (CR.server_initial_state
                   (Ghost.reveal 'certificate_chain_bytes)
                   credential_identity)
                 (Ghost.reveal 'certificate_chain_bytes)
                 credential_identity **
               pure (ST.server_state_correct
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     CM.can_start_server
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     ST.server_end_to_end_invariant
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity))
           | None ->
             emp)
{
  let creds_opt =
    O.server_credentials_new
      certificate_chain
      certificate_chain_len
      private_key
      private_key_len;
  match creds_opt {
    None -> {
      None
    }
    Some creds -> {
      with credential_identity. assert (
        O.is_server_credentials
          creds
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      let erased_identity : erased CS.server_credential_identity =
        Ghost.hide credential_identity;
      let s =
        S.new_server_erased_credential_identity
          certificate_chain
          certificate_chain_len
          #erased_identity;
      assert (pure (Ghost.reveal erased_identity == credential_identity));
      rewrite
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            (Ghost.reveal erased_identity)))
        as
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity));
      let channel = Box.alloc no_channel;
      let buffered_len = Box.alloc 0sz;
      let empty_payload = V.alloc 0uy 0sz;
      let raw = V.alloc 0uy driver_rx_capacity;
      let network_out = V.alloc 0uy driver_network_out_capacity;
      let material_payload = V.alloc 0uy driver_material_capacity;
      let cv_input = V.alloc 0uy driver_certificate_verify_input_capacity;
      let signature = V.alloc 0uy driver_signature_capacity;
      let app_out = V.alloc 0uy driver_app_out_capacity;
      assert (pure (Bounds.max_certificate_verify_input_len <=
        SZ.v driver_certificate_verify_input_capacity));
      assert (pure (IM.max_signature_len <= SZ.v driver_signature_capacity));
      assert (pure (IM.max_record_fragment_len <= SZ.v driver_app_out_capacity));
      let d = {
        server_driver_server = s;
        server_driver_credentials = creds;
        server_driver_channel = channel;
        server_driver_buffered_len = buffered_len;
        server_driver_empty_payload = empty_payload;
        server_driver_raw = raw;
        server_driver_network_out = network_out;
        server_driver_material_payload = material_payload;
        server_driver_certificate_verify_input = cv_input;
        server_driver_signature = signature;
        server_driver_app_out = app_out;
      };
      rewrite (Box.pts_to channel no_channel) as
        (Box.pts_to d.server_driver_channel no_channel);
      rewrite (Box.pts_to buffered_len 0sz) as
        (Box.pts_to d.server_driver_buffered_len 0sz);
      rewrite (V.pts_to empty_payload #1.0R (Seq.create 0 0uy)) as
        (V.pts_to d.server_driver_empty_payload #1.0R (Seq.create 0 0uy));
      rewrite
        (V.pts_to raw #1.0R (Seq.create (SZ.v driver_rx_capacity) 0uy))
        as
        (V.pts_to d.server_driver_raw #1.0R (Seq.create (SZ.v driver_rx_capacity) 0uy));
      rewrite
        (V.pts_to network_out #1.0R (Seq.create (SZ.v driver_network_out_capacity) 0uy))
        as
        (V.pts_to d.server_driver_network_out #1.0R (Seq.create (SZ.v driver_network_out_capacity) 0uy));
      rewrite
        (V.pts_to material_payload #1.0R (Seq.create (SZ.v driver_material_capacity) 0uy))
        as
        (V.pts_to d.server_driver_material_payload #1.0R (Seq.create (SZ.v driver_material_capacity) 0uy));
      rewrite
        (V.pts_to cv_input #1.0R (Seq.create (SZ.v driver_certificate_verify_input_capacity) 0uy))
        as
        (V.pts_to d.server_driver_certificate_verify_input #1.0R
          (Seq.create (SZ.v driver_certificate_verify_input_capacity) 0uy));
      rewrite
        (V.pts_to signature #1.0R (Seq.create (SZ.v driver_signature_capacity) 0uy))
        as
        (V.pts_to d.server_driver_signature #1.0R
          (Seq.create (SZ.v driver_signature_capacity) 0uy));
      rewrite
        (V.pts_to app_out #1.0R (Seq.create (SZ.v driver_app_out_capacity) 0uy))
        as
        (V.pts_to d.server_driver_app_out #1.0R
          (Seq.create (SZ.v driver_app_out_capacity) 0uy));
      rewrite
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity))
        as
        (S.connection_exactly
          d.server_driver_server
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity));
      rewrite
        (O.is_server_credentials
          creds
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)
        as
        (O.is_server_credentials
          d.server_driver_credentials
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      fold (server_driver_buffers d B.empty 0sz);
      fold (server_driver_live
        d
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity);
      Some d
    }
  }
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
                      T.RsaPssRsaeSha256 /\
                    CS.sni_policy_accepts cfg.CS.server_sni_policy ch.M.server_name
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
                 sent'
           | ServerDriverLocalNotReady ->
             server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               'received
               'sent
           | ServerDriverLocalExternalOrUnsupported ->
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
          CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
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
    assert (pure (ST.server_local_event_input_ready
      'st0
      ST.LocalSelectServerParameters
      material));
    Seq.lemma_create_len 64 0uy;
    lemma_select_server_parameters_ready_payload_irrelevant
      'st0
      material
      (Seq.create 64 0uy);
    assert (pure (ST.server_local_event_input_ready
      'st0
      ST.LocalSelectServerParameters
      (Seq.create 64 0uy)));
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
      assert (server_driver_connected
        d
        st2
        'certificate_chain
        'credential_identity
        'received
        sent');
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
                      T.RsaPssRsaeSha256 /\
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
               pure (wait.server_driver_client_hello_wait_ready == false)
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
                 CS.ControlHandshaking CS.HsClientHelloReceived)
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
                 CS.ControlHandshaking CS.HsClientHelloReceived)
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
                 sent)
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
        pure (wait.server_driver_client_hello_wait_ready == true ==>
          st_ch.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived /\
          st_ch.CS.cs_model.CS.model_config ==
            (CM.started_server_state 'st0).CS.cs_model.CS.model_config));
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
              T.RsaPssRsaeSha256 /\
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
              T.RsaPssRsaeSha256 /\
            CS.sni_policy_accepts cfg.CS.server_sni_policy ch.M.server_name
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
                 T.RsaPssRsaeSha256 /\
               CS.sni_policy_accepts cfg.CS.server_sni_policy ch.M.server_name
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
              ServerDriverAcceptSelectDeriveSelectionNotReady
            }
            ServerDriverLocalExternalOrUnsupported -> {
              assert (pure False);
              ServerDriverAcceptSelectDeriveInternalUnsupported
            }
          }
        } else {
          assert (pure (st_ch.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived));
          ServerDriverAcceptSelectDeriveMaterialFailed
        }
      } else {
        assert (pure (wait.server_driver_client_hello_wait_ready == false));
        ServerDriverAcceptSelectDeriveClientHelloWait wait
      }
    }
  }
}

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
                      T.RsaPssRsaeSha256 /\
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
               pure (wait.server_driver_client_hello_wait_ready == false)
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
                 CS.ControlHandshaking CS.HsClientHelloReceived)
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
                 sent)
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
        pure (wait.server_driver_client_hello_wait_ready == true ==>
          st_ch.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived /\
          st_ch.CS.cs_model.CS.model_config ==
            (CM.started_server_state 'st0).CS.cs_model.CS.model_config));
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
              T.RsaPssRsaeSha256 /\
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
              T.RsaPssRsaeSha256 /\
            CS.sni_policy_accepts cfg.CS.server_sni_policy ch.M.server_name
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
                  CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
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
            assert (pure (ST.server_local_event_input_ready
              st_ch
              ST.LocalSelectServerParameters
              material_bytes));
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
          ServerDriverAcceptServerHelloMaterialFailed
        }
      } else {
        assert (pure (wait.server_driver_client_hello_wait_ready == false));
        ServerDriverAcceptServerHelloClientHelloWait wait
      }
    }
  }
}

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
                      T.RsaPssRsaeSha256 /\
                    cfg.CS.server_sni_policy == None
                  | None -> False))
  returns result:server_driver_accept_server_hello_drain_result
  ensures pts_to bind_host 'bind_host_bytes **
          (match result with
           | ServerDriverAcceptServerHelloDrainListenFailed ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity
           | ServerDriverAcceptServerHelloDrainAcceptFailed ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity
           | _ ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent)
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
      ServerDriverAcceptServerHelloDrainClientHelloWait wait
    }
    ServerDriverAcceptServerHelloMaterialFailed -> {
      ServerDriverAcceptServerHelloDrainMaterialFailed
    }
    ServerDriverAcceptServerHelloSelectionNotReady -> {
      ServerDriverAcceptServerHelloDrainSelectionNotReady
    }
    ServerDriverAcceptServerHelloDeriveFailed -> {
      ServerDriverAcceptServerHelloDrainDeriveFailed
    }
    ServerDriverAcceptServerHelloSendNotReady -> {
      ServerDriverAcceptServerHelloDrainSendNotReady
    }
    ServerDriverAcceptServerHelloOk -> {
      let drain = drain_ready_empty_local_actions d local_fuel;
      ServerDriverAcceptServerHelloDrainOk drain
    }
  }
}

fn accept
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
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
                      T.RsaPssRsaeSha256 /\
                    cfg.CS.server_sni_policy == None
                  | None -> False))
  returns status:server_workflow_status
  ensures exists* st1.
          pts_to bind_host 'bind_host_bytes **
            server_driver_closed d st1 'certificate_chain 'credential_identity **
            pure (status <> ServerWorkflowOk)
{
  let result =
    accept_start_read_client_hello_select_derive_send_server_hello_drain_empty_once
      d
      bind_host
      bind_host_len
      port
      network_fuel
      local_fuel;
  match result {
    ServerDriverAcceptServerHelloDrainListenFailed -> {
      close_live_without_transport d;
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainAcceptFailed -> {
      close_live_without_transport d;
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainClientHelloWait wait -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent);
      close_transport_once d;
      if (wait.server_driver_client_hello_wait_exhausted) {
        ServerWorkflowExhausted
      } else {
        ServerWorkflowNeedMoreInput
      }
    }
    ServerDriverAcceptServerHelloDrainMaterialFailed -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent);
      close_transport_once d;
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainSelectionNotReady -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent);
      close_transport_once d;
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainDeriveFailed -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent);
      close_transport_once d;
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainSendNotReady -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent);
      close_transport_once d;
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainOk drain -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent);
      close_transport_once d;
      if (drain.server_driver_local_drain_exhausted) {
        ServerWorkflowExhausted
      } else {
        match drain.server_driver_local_drain_last {
          ServerDriverLocalExternalOrUnsupported -> {
            ServerWorkflowNeedExternalAction
          }
          ServerDriverLocalNotReady -> {
            ServerWorkflowNeedMoreInput
          }
          ServerDriverLocalProcessed -> {
            ServerWorkflowNeedMoreInput
          }
        }
      }
    }
  }
}

fn send
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
                 ST.server_local_event_input_ready
                   'st0
                   ST.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns status:server_workflow_status
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pts_to payload 'payload_bytes **
          pure (status == ServerWorkflowOk \/
                status == ServerWorkflowStepFailed)
{
  let resp = send_application_data_once d payload payload_len;
  if (resp.ST.status = ST.StepOk) {
    ServerWorkflowOk
  } else {
    ServerWorkflowStepFailed
  }
}

fn receive
  (d:server_driver)
  (out:array U8.t)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pts_to out 'out_bytes **
           pure (B.length 'out_bytes == SZ.v out_len)
  returns result:server_receive_result
  ensures exists* st1 received' sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            received'
            sent' **
          pts_to out 'out_bytes **
          pure (result.server_receive_len == 0sz /\
                SZ.v result.server_receive_len <= SZ.v out_len)
{
  let loop = read_process_network_until_ready d network_fuel;
  if (loop.server_driver_network_loop_exhausted) {
    {
      server_receive_status = ServerWorkflowExhausted;
      server_receive_len = 0sz;
    }
  } else {
    match loop.server_driver_network_loop_last.ST.response.ST.status {
      ST.StepOk -> {
        {
          server_receive_status = ServerWorkflowOk;
          server_receive_len = 0sz;
        }
      }
      ST.NeedMoreInput -> {
        {
          server_receive_status = ServerWorkflowNeedMoreInput;
          server_receive_len = 0sz;
        }
      }
      _ -> {
        {
          server_receive_status = ServerWorkflowStepFailed;
          server_receive_len = 0sz;
        }
      }
    }
  }
}

fn close
  (d:server_driver)
  (wait_for_peer:bool)
  (network_fuel:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent
  returns status:server_workflow_status
  ensures server_driver_closed d 'st0 'certificate_chain 'credential_identity **
          pure (status == ServerWorkflowClosed)
{
  close_transport_once d;
  ServerWorkflowClosed
}
