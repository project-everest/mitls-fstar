module TLS13.Impl.Server.Driver.BufferedAccept

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BTrans = TLS13.Impl.Server.Driver.BufferedTransport
module CM = TLS13.Impl.ConnectionState.Model
module DS = TLS13.Impl.Server.Driver.State
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

type accept_status =
  | BufferedAcceptOk
  | BufferedAcceptListenFailed
  | BufferedAcceptTransportFailed
  | BufferedAcceptExhausted
  | BufferedAcceptHandshakeFailed

fn run
  (d:DS.top_server_driver)
  (source:BTrans.server_transport_source)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires
    BTrans.owns_server_transport_source
      source 'bind_host_bytes port **
    DS.top_server_driver_live
      d 'st0 'certificate_chain 'credential_identity **
    pts_to bind_host 'bind_host_bytes **
    pure (
      B.length 'bind_host_bytes == SZ.v bind_host_len /\
      CM.can_start_server 'st0)
  returns status:accept_status
  ensures
    BTrans.owns_server_transport_source
      source 'bind_host_bytes port **
    pts_to bind_host 'bind_host_bytes **
    (match status with
     | BufferedAcceptOk ->
       exists* wire_received wire_sent pending app_log.
         DS.top_server_channel_inv
           d wire_received wire_sent pending app_log
     | _ ->
       exists* st1.
         DS.top_server_driver_closed
           d st1 'certificate_chain 'credential_identity)
