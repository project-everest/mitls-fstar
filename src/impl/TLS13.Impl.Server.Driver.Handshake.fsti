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
module DN = TLS13.Impl.Server.Driver.Network
module DL = TLS13.Impl.Server.Driver.Local
module DS = TLS13.Impl.Server.Driver.State
module DT = TLS13.Impl.Server.Driver.Transport
module M = TLS13.Messages
module Seq = FStar.Seq
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module W = TLS13.Wire.Spec

type server_driver_accept_client_hello_result =
  | ServerDriverAcceptClientHelloTransportOk of DN.server_driver_client_hello_wait_result
  | ServerDriverAcceptClientHelloListenFailed
  | ServerDriverAcceptClientHelloAcceptFailed

type server_driver_accept_select_derive_result =
  | ServerDriverAcceptSelectDeriveOk
  | ServerDriverAcceptSelectDeriveClientHelloWait of DN.server_driver_client_hello_wait_result
  | ServerDriverAcceptSelectDeriveMaterialFailed
  | ServerDriverAcceptSelectDeriveSelectionNotReady
  | ServerDriverAcceptSelectDeriveInternalUnsupported
  | ServerDriverAcceptSelectDeriveListenFailed
  | ServerDriverAcceptSelectDeriveAcceptFailed

type server_driver_accept_server_hello_result =
  | ServerDriverAcceptServerHelloOk
  | ServerDriverAcceptServerHelloClientHelloWait of DN.server_driver_client_hello_wait_result
  | ServerDriverAcceptServerHelloMaterialFailed
  | ServerDriverAcceptServerHelloSelectionNotReady
  | ServerDriverAcceptServerHelloDeriveFailed
  | ServerDriverAcceptServerHelloSendNotReady
  | ServerDriverAcceptServerHelloListenFailed
  | ServerDriverAcceptServerHelloAcceptFailed

type server_driver_accept_server_hello_drain_result =
  | ServerDriverAcceptServerHelloDrainOk of DL.server_driver_local_drain_result
  | ServerDriverAcceptServerHelloDrainClientHelloWait of DN.server_driver_client_hello_wait_result
  | ServerDriverAcceptServerHelloDrainMaterialFailed
  | ServerDriverAcceptServerHelloDrainSelectionNotReady
  | ServerDriverAcceptServerHelloDrainDeriveFailed
  | ServerDriverAcceptServerHelloDrainSendNotReady
  | ServerDriverAcceptServerHelloDrainListenFailed
  | ServerDriverAcceptServerHelloDrainAcceptFailed

type server_driver_select_derive_server_hello_result =
  | ServerDriverSelectDeriveServerHelloOk
  | ServerDriverSelectDeriveServerHelloDeriveFailed
  | ServerDriverSelectDeriveServerHelloSendNotReady

val lemma_select_server_parameters_ready_payload_irrelevant :
  st:CS.connection_state ->
  payload0:B.bytes ->
  payload1:B.bytes ->
  Lemma
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

noextract
let server_driver_selection_from_payload_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (payload:B.bytes)
  : GTot prop =
  B.length payload == 64 /\
  (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
         st0.CS.cs_model.CS.model_config.CS.config_server with
   | Some ch, Some cfg ->
     let selection = {
       CS.server_selected_client_hello = ch;
       CS.server_selected_cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
       CS.server_selected_group = T.X25519;
       CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
       CS.server_random = CL.raw_slice payload 0 32;
       CS.server_key_share_private = Some (CL.raw_slice payload 32 64);
       CS.server_key_share_public =
         CryptoSpec.x25519_public_from_private (CL.raw_slice payload 32 64);
       CS.server_selected_credential = cfg.CS.server_credential_identity;
     } in
     st1 == CM.selected_server_parameters_state st0 selection
   | _ -> False)

noextract
let server_driver_derive_shared_secret_success_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (payload:B.bytes)
  : GTot prop =
  resp.ST.status == ST.StepOk ==>
   (exists shared.
     st1 == CM.derived_shared_secret_state st0 shared /\
     (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
      | Some ch ->
        CryptoSpec.x25519_shared payload ch.M.key_share == Some shared
      | None -> False))

let server_driver_select_derive_from_payload_success_correct
  (st0:CS.connection_state)
  (st2:CS.connection_state)
  (resp:ST.server_response)
  (payload:B.bytes)
  : GTot prop =
  resp.ST.status == ST.StepOk ==>
   (exists st1 shared.
     server_driver_selection_from_payload_correct st0 st1 payload /\
     st2 == CM.derived_shared_secret_state st1 shared /\
     (match st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
      | Some ch ->
        CryptoSpec.x25519_shared
          (CL.raw_slice payload 32 64)
          ch.M.key_share == Some shared
      | None -> False))

noextract
let server_driver_send_server_hello_from_payload_success_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (payload:B.bytes)
  : GTot prop =
  resp.ST.status == ST.StepOk ==>
    B.length payload == 64 /\
    (let sh = {
      M.random = CL.raw_slice payload 0 32;
      M.key_share =
        CryptoSpec.x25519_public_from_private (CL.raw_slice payload 32 64);
      M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
     } in
     st1 ==
      CM.sent_server_hello_state
        st0
        sh
        (CS.serialized_cleartext_tls_message
          (M.TlsHandshake (M.ServerHello sh))))

val lemma_select_derive_success_server_hello_ready :
  st0:CS.connection_state ->
  st2:CS.connection_state ->
  resp:ST.server_response ->
  payload:B.bytes ->
  Lemma
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

fn generate_server_material_once
  (d:DS.server_driver)
  requires DS.server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               'received
               'sent
  returns ok:bool
  ensures DS.server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent

fn select_default_server_parameters_once
  (d:DS.server_driver)
  requires DS.server_driver_connected
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
          DS.server_driver_connected
              d
              st1
              'certificate_chain
              'credential_identity
              'received
              'sent

fn select_default_server_parameters_from_payload_once
  (d:DS.server_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires DS.server_driver_connected
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
          DS.server_driver_connected
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
              (Ghost.reveal 'payload_bytes))

fn derive_shared_secret_from_payload_once
  (d:DS.server_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires DS.server_driver_connected
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
          DS.server_driver_connected
              d
              st1
              'certificate_chain
              'credential_identity
              'received
              sent' **
          pts_to payload 'payload_bytes **
          pure (DL.server_driver_local_write_correct
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
              (Ghost.reveal 'payload_bytes))

fn select_supported_server_parameters_from_payload_if_ready_once
  (d:DS.server_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires DS.server_driver_connected
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
                        T.RsaPssRsaeSha256 /\
                      CS.sni_policy_accepts cfg.CS.server_sni_policy ch.M.server_name
                    | _, _ -> True))
  returns status:DL.server_driver_local_status
  ensures (match status with
           | DL.ServerDriverLocalProcessed ->
               exists* st1.
                 DS.server_driver_connected
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
                   (Ghost.reveal 'payload_bytes))
           | DL.ServerDriverLocalNotReady ->
                 DS.server_driver_connected
                   d
                   'st0
                   'certificate_chain
                   'credential_identity
                   'received
                   'sent **
                 pts_to payload 'payload_bytes
           | DL.ServerDriverLocalExternalOrUnsupported ->
                 pure False)

fn select_and_derive_shared_secret_from_payload_once
  (d:DS.server_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires DS.server_driver_connected
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
          DS.server_driver_connected
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
            (Ghost.reveal 'payload_bytes))

fn send_server_hello_from_payload_once
  (d:DS.server_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires DS.server_driver_connected
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
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          DS.server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pts_to payload 'payload_bytes **
          pure (DL.server_driver_local_write_correct
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
            (Ghost.reveal 'payload_bytes))

fn select_derive_send_server_hello_from_payload_once
 (d:DS.server_driver)
 (payload:array U8.t)
 (payload_len:SZ.t)
 requires DS.server_driver_connected
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
 returns result:server_driver_select_derive_server_hello_result
 ensures (match result with
          | ServerDriverSelectDeriveServerHelloOk ->
            exists* st3 sent_after_send.
              DS.server_driver_connected
                d
                st3
                'certificate_chain
                'credential_identity
                'received
                sent_after_send **
              pts_to payload 'payload_bytes
          | ServerDriverSelectDeriveServerHelloDeriveFailed ->
            exists* st2 sent_after_derive.
              DS.server_driver_connected
                d
                st2
                'certificate_chain
                'credential_identity
                'received
                sent_after_derive **
              pts_to payload 'payload_bytes
          | ServerDriverSelectDeriveServerHelloSendNotReady ->
            exists* st2 sent_after_derive.
              DS.server_driver_connected
                d
                st2
                'certificate_chain
                'credential_identity
                'received
                sent_after_derive **
              pts_to payload 'payload_bytes)

fn select_and_derive_shared_secret_once
 (d:DS.server_driver)
  requires DS.server_driver_connected
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
          DS.server_driver_connected
            d
            st2
            'certificate_chain
            'credential_identity
            'received
            sent'

fn select_and_derive_shared_secret_if_ready_once
  (d:DS.server_driver)
  requires DS.server_driver_connected
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
  returns status:DL.server_driver_local_status
  ensures (match status with
           | DL.ServerDriverLocalProcessed ->
             exists* st2 sent'.
               DS.server_driver_connected
                 d
                 st2
                 'certificate_chain
                 'credential_identity
                 'received
                 sent'
           | DL.ServerDriverLocalNotReady ->
             DS.server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               'received
               'sent
           | DL.ServerDriverLocalExternalOrUnsupported ->
             pure False)

fn accept_start_read_client_hello_select_derive_once
  (d:DS.server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (network_fuel:SZ.t)
  requires DS.server_driver_live d 'st0 'certificate_chain 'credential_identity **
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
             DS.server_driver_live d 'st0 'certificate_chain 'credential_identity
           | ServerDriverAcceptSelectDeriveAcceptFailed ->
             DS.server_driver_live d 'st0 'certificate_chain 'credential_identity
           | ServerDriverAcceptSelectDeriveClientHelloWait wait ->
             exists* st1 received sent.
               DS.server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (wait.DN.server_driver_client_hello_wait_ready == false)
           | ServerDriverAcceptSelectDeriveMaterialFailed ->
             exists* st1 received sent.
               DS.server_driver_connected
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
               DS.server_driver_connected
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
               DS.server_driver_connected
                 d
                 st2
                 'certificate_chain
                 'credential_identity
                 received
                 sent)

fn accept_start_read_client_hello_select_derive_send_server_hello_once
  (d:DS.server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (network_fuel:SZ.t)
  requires DS.server_driver_live d 'st0 'certificate_chain 'credential_identity **
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
               DS.server_driver_live d 'st0 'certificate_chain 'credential_identity
           | ServerDriverAcceptServerHelloAcceptFailed ->
               DS.server_driver_live d 'st0 'certificate_chain 'credential_identity
           | ServerDriverAcceptServerHelloClientHelloWait wait ->
               exists* st1 received sent.
                 DS.server_driver_connected
                   d
                   st1
                   'certificate_chain
                   'credential_identity
                   received
                   sent **
                 pure (wait.DN.server_driver_client_hello_wait_ready == false)
           | ServerDriverAcceptServerHelloMaterialFailed
           | ServerDriverAcceptServerHelloSelectionNotReady ->
               exists* st1 received sent.
                 DS.server_driver_connected
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
                 DS.server_driver_connected
                   d
                   st2
                   'certificate_chain
                   'credential_identity
                   received
                   sent)

fn accept_start_read_client_hello_select_derive_send_server_hello_drain_empty_once
  (d:DS.server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (network_fuel:SZ.t)
  (local_fuel:SZ.t)
  requires DS.server_driver_live d 'st0 'certificate_chain 'credential_identity **
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
             DS.server_driver_live d 'st0 'certificate_chain 'credential_identity
           | ServerDriverAcceptServerHelloDrainAcceptFailed ->
             DS.server_driver_live d 'st0 'certificate_chain 'credential_identity
           | _ ->
             exists* st1 received sent.
                 DS.server_driver_connected
                   d
                   st1
                   'certificate_chain
                   'credential_identity
                   received
                   sent)

fn accept_transport_and_start_once
  (d:DS.server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  requires DS.server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                 CM.can_start_server 'st0)
  returns status:DS.server_driver_transport_status
  ensures pts_to bind_host 'bind_host_bytes **
          (match status with
           | DS.ServerDriverTransportOk ->
             DS.server_driver_connected
               d
               (CM.started_server_state 'st0)
               'certificate_chain
               'credential_identity
               B.empty
               B.empty
           | _ ->
             DS.server_driver_live d 'st0 'certificate_chain 'credential_identity)

fn accept_transport_start_and_read_client_hello
  (d:DS.server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (network_fuel:SZ.t)
  requires DS.server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                 CM.can_start_server 'st0)
  returns result:server_driver_accept_client_hello_result
  ensures pts_to bind_host 'bind_host_bytes **
          (match result with
           | ServerDriverAcceptClientHelloTransportOk wait ->
             exists* st1 received sent.
               DS.server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (wait.DN.server_driver_client_hello_wait_ready == true ==>
                   st1.CS.cs_model.CS.model_control ==
                     CS.ControlHandshaking CS.HsClientHelloReceived /\
                   st1.CS.cs_model.CS.model_config ==
                     (CM.started_server_state 'st0).CS.cs_model.CS.model_config)
           | _ ->
             DS.server_driver_live d 'st0 'certificate_chain 'credential_identity)
