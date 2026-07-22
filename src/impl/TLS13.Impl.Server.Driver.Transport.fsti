module TLS13.Impl.Server.Driver.Transport

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open TLS13.Impl.Server.Driver.State

module B = TLS13.Bytes
module CS = TLS13.Spec.StateMachine
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

type server_transport_source = option Common.TCP.listener

noextract
let owns_server_transport_source
  (source:server_transport_source)
  (bind_host:B.bytes)
  (port:U16.t)
  : slprop =
  match source with
  | None -> pure True
  | Some listener -> Common.TCP.is_listener listener bind_host port

fn accept_transport_once_from
  (source:server_transport_source)
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  requires owns_server_transport_source source 'bind_host_bytes port **
           server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len)
  returns status:server_driver_transport_status
  ensures owns_server_transport_source source 'bind_host_bytes port **
          pts_to bind_host 'bind_host_bytes **
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

fn close_live_without_transport
  (d:server_driver)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity
  ensures server_driver_closed d 'st0 'certificate_chain 'credential_identity
