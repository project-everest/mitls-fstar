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
module O = TLS13.OpenSSL
module S = TLS13.Impl.Server
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
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
          pts_to payload 'payload_bytes

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
