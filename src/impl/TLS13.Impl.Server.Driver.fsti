module TLS13.Impl.Server.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module IO = TLS13.IO
module M = TLS13.Messages
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module S = TLS13.Impl.Server
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8

val server_driver : Type0

type server_driver_transport_status =
  | ServerDriverTransportOk
  | ServerDriverListenFailed
  | ServerDriverAcceptFailed

type server_driver_local_status =
  | ServerDriverLocalProcessed
  | ServerDriverLocalNotReady
  | ServerDriverLocalExternalOrUnsupported

type server_driver_network_loop_result = {
  server_driver_network_loop_last: ST.server_buffer_response;
  server_driver_network_loop_exhausted: bool;
}

type server_driver_local_drain_result = {
  server_driver_local_drain_last: server_driver_local_status;
  server_driver_local_drain_exhausted: bool;
}

type server_driver_client_hello_wait_result = {
  server_driver_client_hello_wait_last: ST.server_buffer_response;
  server_driver_client_hello_wait_ready: bool;
  server_driver_client_hello_wait_exhausted: bool;
}

type server_driver_accept_client_hello_result =
  | ServerDriverAcceptClientHelloTransportOk of server_driver_client_hello_wait_result
  | ServerDriverAcceptClientHelloListenFailed
  | ServerDriverAcceptClientHelloAcceptFailed

type server_driver_accept_select_derive_result =
  | ServerDriverAcceptSelectDeriveOk
  | ServerDriverAcceptSelectDeriveClientHelloWait of server_driver_client_hello_wait_result
  | ServerDriverAcceptSelectDeriveMaterialFailed
  | ServerDriverAcceptSelectDeriveSelectionNotReady
  | ServerDriverAcceptSelectDeriveInternalUnsupported
  | ServerDriverAcceptSelectDeriveListenFailed
  | ServerDriverAcceptSelectDeriveAcceptFailed

noextract
val server_driver_live
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop

noextract
val server_driver_connected
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  (received:B.bytes)
  (sent:B.bytes)
  : slprop

noextract
val server_driver_closed
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop

noextract
val server_driver_local_write_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop

noextract
val server_driver_network_process_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop

noextract
val server_driver_selection_from_payload_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (payload:B.bytes)
  : prop

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

fn accept_transport_once
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len)
  returns status:server_driver_transport_status
  ensures pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerDriverTransportOk ->
             server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               B.empty
               B.empty
           | _ ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity)

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

fn close_transport_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  ensures server_driver_closed d 'st0 'certificate_chain 'credential_identity

fn read_transport_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns n:SZ.t
  ensures exists* received'.
          server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            received'
            'sent **
          pure (SZ.v n <= 65535)

fn process_buffered_network_bytes_compact_once
  (d:server_driver)
  requires server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
  returns resp:ST.server_buffer_response
  ensures exists* st1 sent'.
          server_driver_connected
           d
           st1
           'certificate_chain
           'credential_identity
           'received
           sent' **
          pure (server_driver_network_process_correct
           'st0
           st1
           resp
           (Ghost.reveal 'sent)
           sent')

fn read_and_process_network_once
  (d:server_driver)
  requires server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
  returns resp:ST.server_buffer_response
  ensures exists* st1 received' sent'.
          server_driver_connected
           d
           st1
           'certificate_chain
           'credential_identity
           received'
           sent' **
          pure (server_driver_network_process_correct
           'st0
           st1
           resp
           (Ghost.reveal 'sent)
           sent')

fn read_process_network_until_ready
  (d:server_driver)
  (fuel:SZ.t)
  requires server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
  returns result:server_driver_network_loop_result
  ensures exists* st1 received' sent'.
          server_driver_connected
           d
           st1
           'certificate_chain
           'credential_identity
           received'
           sent' **
          pure (result.server_driver_network_loop_exhausted == false ==>
            result.server_driver_network_loop_last.ST.response.ST.status <>
              ST.NeedMoreInput /\
            server_driver_network_process_correct
              'st0
              st1
              result.server_driver_network_loop_last
              (Ghost.reveal 'sent)
              sent')

fn read_until_client_hello_received
  (d:server_driver)
  (fuel:SZ.t)
  requires server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
  returns result:server_driver_client_hello_wait_result
  ensures exists* st1 received' sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            received'
            sent' **
          pure (result.server_driver_client_hello_wait_ready == true ==>
            st1.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived /\
            st1.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config)
fn start_server_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent **
           pure (CM.can_start_server 'st0)
  returns resp:ST.server_response
  ensures server_driver_connected
            d
            (CM.started_server_state 'st0)
            'certificate_chain
            'credential_identity
            'received
            'sent

fn start_server_if_ready
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns status:server_driver_local_status
  ensures (match status with
           | ServerDriverLocalProcessed ->
             server_driver_connected
               d
               (CM.started_server_state 'st0)
               'certificate_chain
               'credential_identity
               'received
               'sent
           | _ ->
             server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               'received
               'sent)

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
            (Ghost.reveal 'payload_bytes))

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
                      T.RsaPssRsaeSha256 /\
                    CS.sni_policy_accepts cfg.CS.server_sni_policy ch.M.server_name
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
                 (Ghost.reveal 'payload_bytes))
           | ServerDriverLocalNotReady ->
               server_driver_connected
                 d
                 'st0
                 'certificate_chain
                 'credential_identity
                 'received
                 'sent **
               pts_to payload 'payload_bytes
           | ServerDriverLocalExternalOrUnsupported ->
               pure False)

fn process_local_event_and_write_once
  (d:server_driver)
  (kind:ST.local_event_kind)
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
                ST.server_local_event_input_ready_with_credentials
                  'st0
                  kind
                  (Ghost.reveal 'payload_bytes)
                  (Ghost.reveal 'certificate_chain)
                  (Ghost.reveal 'credential_identity))
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
           kind
           (Ghost.reveal 'payload_bytes)
           (Ghost.reveal 'sent)
           sent')

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
           sent')

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
          pts_to payload 'payload_bytes

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
           sent'

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

fn process_ready_empty_local_action_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns status:server_driver_local_status
  ensures (match status with
           | ServerDriverLocalProcessed ->
            exists* st1 sent'.
              server_driver_connected
                d
                st1
                'certificate_chain
                'credential_identity
                'received
                sent'
           | _ ->
            server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent)

fn drain_ready_empty_local_actions
  (d:server_driver)
  (fuel:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent
  returns result:server_driver_local_drain_result
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'

fn send_application_data_once
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
            ST.LocalSendApplicationData
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'sent)
            sent')

fn send_close_notify_once
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
             ST.LocalSendCloseNotify
             B.empty)
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'

fn send_certificate_once
  (d:server_driver)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (ST.server_local_event_input_ready_with_credentials
             'st0
             ST.LocalSendCertificate
             B.empty
             (Ghost.reveal 'certificate_chain)
             (Ghost.reveal 'credential_identity))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'

fn sign_certificate_verify_once
  (d:server_driver)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (ST.server_local_event_input_ready_with_credentials
             'st0
             ST.LocalSignCertificateVerify
             B.empty
             (Ghost.reveal 'certificate_chain)
             (Ghost.reveal 'credential_identity))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'

fn verify_client_finished_once
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
             ST.LocalVerifyClientFinished
             B.empty)
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'
