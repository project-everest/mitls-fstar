module TLS13.Impl.Server.Driver.Handshake

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module DN = TLS13.Impl.Server.Driver.Network
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

open TLS13.Impl.Server.Driver.State
open TLS13.Impl.Server.Driver.Transport
open TLS13.Impl.Server.Driver.Network
open TLS13.Impl.Server.Driver.Local

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
