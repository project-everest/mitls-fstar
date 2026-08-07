module TLS13.Impl.Server.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BA = TLS13.Impl.Server.Driver.BufferedAccept
module BC = TLS13.Impl.Server.Driver.BufferedClose
module BChan = TLS13.Impl.Server.Driver.BufferedChannel
module BL = TLS13.Impl.Server.Driver.BufferedLifecycle
module BR = TLS13.Impl.Server.Driver.BufferedReceive
module BS = TLS13.Impl.Server.Driver.BufferedSend
module BT = TLS13.Impl.Server.Driver.BufferedTransport
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CI = Common.ChannelImplementation
module CImpl = TLS13.Impl.Server.ChannelImplementation
module CPI = Common.ProtocolImplementation
module CR = TLS13.Impl.ConnectionState.Repr
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Spec.Endpoint.Wire
module EAPI = TLS13.Spec.Endpoint.API
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module IO = Common.TCP
module O = TLS13.OpenSSL
module SP = TLS13.Impl.Server.CanonicalProtocol
module SZ = FStar.SizeT
module TChannel = TLS13.Impl.Channel
module Trace = TLS13.Trace
module U16 = FStar.UInt16
module U8 = FStar.UInt8

noextract
let server_driver_canonical = DS.top_server_driver_canonical

noextract
let server_driver_canonical_progress =
  DS.top_server_driver_canonical_progress

noextract
let server_driver_live = DS.top_server_driver_live

noextract
let server_driver_connected = DS.top_server_driver_connected

noextract
let server_driver_closed = DS.top_server_driver_closed

noextract
let server_driver_released = DS.top_server_driver_released

fn new_server_listener
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  requires
    pts_to bind_host 'bind_host_bytes **
    pure (B.length 'bind_host_bytes == SZ.v bind_host_len)
  returns result:option server_listener
  ensures
    pts_to bind_host 'bind_host_bytes **
    (match result with
     | Some listener -> IO.is_listener listener 'bind_host_bytes port
     | None -> emp)
{
  IO.listen_tcp bind_host bind_host_len port
}

fn free_server_listener
  (listener:server_listener)
  requires IO.is_listener listener 'bind_host_bytes 'port
  ensures emp
{
  IO.close_listener listener
}

fn new_server_credentials
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  requires
    pts_to certificate_chain 'certificate_chain_bytes **
    pts_to private_key 'private_key_bytes **
    pure (
      B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
      B.length 'private_key_bytes == SZ.v private_key_len)
  returns result:option server_credentials
  ensures
    exists* credential_identity.
      pts_to certificate_chain 'certificate_chain_bytes **
      pts_to private_key 'private_key_bytes **
      (match result with
       | Some credentials ->
         O.is_server_credentials
           credentials
           (Ghost.reveal 'certificate_chain_bytes)
           credential_identity
       | None -> emp)
{
  O.server_credentials_new
    certificate_chain
    certificate_chain_len
    private_key
    private_key_len
}

fn free_server_credentials
  (credentials:server_credentials)
  requires
    O.is_server_credentials
      credentials 'certificate_chain 'credential_identity
  ensures emp
{
  O.server_credentials_free credentials
}

fn new_server_with_credentials
  (credentials:server_credentials)
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  (#supported_profile_provider:erased SP.server_supported_profile_provider)
  requires
    (exists* credential_identity.
      O.is_server_credentials
        credentials
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity) **
    pts_to certificate_chain 'certificate_chain_bytes **
    pts_to private_key 'private_key_bytes **
    pure (
      B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
      B.length 'private_key_bytes == SZ.v private_key_len /\
      B.length 'certificate_chain_bytes <=
        Bounds.max_server_certificate_chain_len)
  returns result:option server_driver
  ensures
    pts_to certificate_chain 'certificate_chain_bytes **
    pts_to private_key 'private_key_bytes **
    (exists* credential_identity.
      O.is_server_credentials
        credentials
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity **
      (match result with
       | Some d ->
         server_driver_live
           d
           (CR.server_initial_state
             (Ghost.reveal 'certificate_chain_bytes)
             credential_identity)
           (Ghost.reveal 'certificate_chain_bytes)
           credential_identity **
         pure (
           TLS13.Impl.Server.Types.server_state_correct
             (CR.server_initial_state
               (Ghost.reveal 'certificate_chain_bytes)
               credential_identity) /\
           TLS13.Impl.Server.Types.server_end_to_end_invariant
             (CR.server_initial_state
               (Ghost.reveal 'certificate_chain_bytes)
               credential_identity))
       | None -> emp))
{
  BL.new_server_with_credentials
    credentials
    certificate_chain
    certificate_chain_len
    #supported_profile_provider
}

fn accept_with_listener
  (d:server_driver)
  (listener:server_listener)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires
    IO.is_listener listener 'bind_host_bytes port **
    server_driver_live d 'st0 'certificate_chain 'credential_identity **
    pts_to bind_host 'bind_host_bytes **
    pure (
      B.length 'bind_host_bytes == SZ.v bind_host_len /\
      TLS13.Impl.ConnectionState.Model.can_start_server 'st0)
  returns status:server_workflow_status
  ensures
    IO.is_listener listener 'bind_host_bytes port **
    pts_to bind_host 'bind_host_bytes **
    (match status with
     | ServerWorkflowOk ->
       exists* wire_received wire_sent pending app_log.
         DS.top_server_channel_inv
           d wire_received wire_sent pending app_log
     | _ ->
       exists* st1.
         DS.top_server_driver_closed
           d st1 'certificate_chain 'credential_identity)
{
  rewrite
    (server_driver_live
      d 'st0 'certificate_chain 'credential_identity)
    as
    (DS.top_server_driver_live
      d 'st0 'certificate_chain 'credential_identity);
  fold (BT.owns_server_transport_source
    (Some listener) 'bind_host_bytes port);
  let result =
    BA.run
      d
      (Some listener)
      bind_host
      bind_host_len
      port
      local_fuel
      network_fuel;
  unfold (BT.owns_server_transport_source
    (Some listener) 'bind_host_bytes port);
  match result {
    BA.BufferedAcceptOk -> { ServerWorkflowOk }
    BA.BufferedAcceptExhausted -> { ServerWorkflowExhausted }
    BA.BufferedAcceptListenFailed -> { ServerWorkflowStepFailed }
    BA.BufferedAcceptTransportFailed -> { ServerWorkflowStepFailed }
    BA.BufferedAcceptHandshakeFailed -> { ServerWorkflowStepFailed }
  }
}

fn send
  (d:server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (payload:array U8.t)
  (payload_bytes:Ghost.erased B.bytes)
  (payload_len:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0) **
    pts_to payload (Ghost.reveal payload_bytes) **
    pure (B.length (Ghost.reveal payload_bytes) == SZ.v payload_len)
  returns status:server_workflow_status
  ensures
    pts_to payload (Ghost.reveal payload_bytes) **
    (match status with
     | ServerWorkflowOk
     | ServerWorkflowPayloadTooLarge ->
       exists* wire_received1 wire_sent1 pending1 app_log1.
         DS.top_server_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
     | _ ->
       exists* st certificate_chain credential_identity.
         DS.top_server_driver_closed d st certificate_chain credential_identity)
{
  let status =
    BS.run
      d wire_received0 wire_sent0 pending0 app_log0
      payload payload_len;
  match status {
    BS.BufferedSendOk -> { ServerWorkflowOk }
    BS.BufferedSendPayloadTooLarge -> { ServerWorkflowPayloadTooLarge }
    BS.BufferedSendFailed -> {
      with wire_received1 wire_sent1 app_log1.
        assert (DS.top_server_channel_terminal
          d wire_received1 wire_sent1 app_log1);
      BC.abort_terminal
        d
        (Ghost.hide wire_received1)
        (Ghost.hide wire_sent1)
        (Ghost.hide app_log1);
      ServerWorkflowStepFailed
    }
  }
}

fn send_key_update
  (d:server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (request:bool)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0)
  returns status:server_workflow_status
  ensures
    (match status with
     | ServerWorkflowOk
     | ServerWorkflowPayloadTooLarge ->
       exists* wire_received1 wire_sent1 pending1 app_log1.
         DS.top_server_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
     | _ ->
       exists* st certificate_chain credential_identity.
         DS.top_server_driver_closed d st certificate_chain credential_identity)
{
  let status =
    BS.run_key_update
      d wire_received0 wire_sent0 pending0 app_log0
      request;
  match status {
    BS.BufferedSendOk -> { ServerWorkflowOk }
    BS.BufferedSendPayloadTooLarge -> { ServerWorkflowPayloadTooLarge }
    BS.BufferedSendFailed -> {
      with wire_received1 wire_sent1 app_log1.
        assert (DS.top_server_channel_terminal
          d wire_received1 wire_sent1 app_log1);
      BC.abort_terminal
        d
        (Ghost.hide wire_received1)
        (Ghost.hide wire_sent1)
        (Ghost.hide app_log1);
      ServerWorkflowStepFailed
    }
  }
}

fn receive
  (d:server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (out:array U8.t)
  (old_output:Ghost.erased B.bytes)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0) **
    pts_to out (Ghost.reveal old_output) **
    pure (B.length (Ghost.reveal old_output) == SZ.v out_len)
  returns result:server_receive_result
  ensures
    exists* output.
      pts_to out output **
      pure (
        B.length output == SZ.v out_len /\
        SZ.v result.server_receive_len <= SZ.v out_len) **
      (match result.server_receive_status with
       | ServerWorkflowOk
       | ServerWorkflowExhausted
       | ServerWorkflowOutputBufferTooSmall ->
         exists* wire_received1 wire_sent1 pending1 app_log1.
           DS.top_server_channel_inv
             d wire_received1 wire_sent1 pending1 app_log1
       | _ ->
         exists* st certificate_chain credential_identity.
           DS.top_server_driver_closed d st certificate_chain credential_identity)
{
  let received =
    BR.run
      d wire_received0 wire_sent0 pending0 app_log0
      out out_len network_fuel;
  match received.BR.receive_status {
    BR.BufferedReceiveOk -> {
      // RFC 8446 4.6.3: a peer KeyUpdate with update_requested must be answered
      // with our own update_not_requested *before* the next Application Data
      // record.  The receive above records the obligation; discharge it here,
      // while we still own the channel and before returning to the
      // application.  No-op when nothing is pending.
      with wire_received1 wire_sent1 pending1 app_log1.
        assert (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1);
      let ku =
        BS.run_key_update_response
          d
          (Ghost.hide wire_received1)
          (Ghost.hide wire_sent1)
          (Ghost.hide pending1)
          (Ghost.hide app_log1);
      match ku {
        BS.BufferedSendFailed -> {
          with wire_received2 wire_sent2 app_log2.
            assert (DS.top_server_channel_terminal
              d wire_received2 wire_sent2 app_log2);
          BC.abort_terminal
            d
            (Ghost.hide wire_received2)
            (Ghost.hide wire_sent2)
            (Ghost.hide app_log2);
          {
            server_receive_status = ServerWorkflowStepFailed;
            server_receive_len = received.BR.receive_len;
          }
        }
        BS.BufferedSendOk -> {
          {
            server_receive_status = ServerWorkflowOk;
            server_receive_len = received.BR.receive_len;
          }
        }
        BS.BufferedSendPayloadTooLarge -> {
          // Unreachable: run_key_update_response sends a fixed 27-byte record
          // into the driver's own output buffer, which is far larger.
          {
            server_receive_status = ServerWorkflowOk;
            server_receive_len = received.BR.receive_len;
          }
        }
      }
    }
    BR.BufferedReceiveExhausted -> {
      {
        server_receive_status = ServerWorkflowExhausted;
        server_receive_len = received.BR.receive_len;
      }
    }
    BR.BufferedReceiveOutputBufferTooSmall -> {
      {
        server_receive_status = ServerWorkflowOutputBufferTooSmall;
        server_receive_len = received.BR.receive_len;
      }
    }
    BR.BufferedReceiveClosed -> {
      with wire_received1 wire_sent1 app_log1.
        assert (DS.top_server_channel_terminal
          d wire_received1 wire_sent1 app_log1);
      BC.abort_terminal
        d
        (Ghost.hide wire_received1)
        (Ghost.hide wire_sent1)
        (Ghost.hide app_log1);
      {
        server_receive_status = ServerWorkflowClosed;
        server_receive_len = received.BR.receive_len;
      }
    }
    BR.BufferedReceiveFailed -> {
      with wire_received1 wire_sent1 app_log1.
        assert (DS.top_server_channel_terminal
          d wire_received1 wire_sent1 app_log1);
      BC.abort_terminal
        d
        (Ghost.hide wire_received1)
        (Ghost.hide wire_sent1)
        (Ghost.hide app_log1);
      {
        server_receive_status = ServerWorkflowStepFailed;
        server_receive_len = received.BR.receive_len;
      }
    }
  }
}

fn close
  (d:server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (wait_for_peer:bool)
  (network_fuel:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  returns status:server_workflow_status
  ensures
    exists* st certificate_chain credential_identity.
      DS.top_server_driver_closed d st certificate_chain credential_identity
{
  let status =
    BC.run
      d wire_received wire_sent pending app_log
      wait_for_peer network_fuel;
  match status {
    BC.BufferedCloseClosed -> { ServerWorkflowClosed }
    BC.BufferedCloseExhausted -> { ServerWorkflowExhausted }
    BC.BufferedCloseFailed -> { ServerWorkflowStepFailed }
  }
}

fn free
  (d:server_driver)
  requires
    DS.top_server_driver_closed d 'st 'certificate_chain 'credential_identity
  ensures DS.top_server_driver_released d 'st
{
  Trace.emit Trace.server_free 0UL 0UL 0UL;
  BL.free d
}

(* Convert the buffered layer's [match]-shaped postcondition into the
   [if]-shaped one the channel class demands. *)
fn channel_send_core
  (d:server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (payload:array U8.t)
  (payload_bytes:Ghost.erased B.bytes)
  (payload_len:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0) **
    pts_to payload (Ghost.reveal payload_bytes) **
    pure (B.length (Ghost.reveal payload_bytes) == SZ.v payload_len)
  returns status:BS.send_status
  ensures
    exists* wire_received1 wire_sent1 pending1 app_log1.
      (if channel_send_reusable status
       then
         DS.top_server_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
       else
         DS.top_server_channel_terminal
           d wire_received1 wire_sent1 app_log1) **
      pts_to payload (Ghost.reveal payload_bytes) **
      pure (
        CI.send_transition
          channel_message_of_bytes
          channel_send_succeeded
          status
          (Ghost.reveal payload_bytes)
          (Ghost.reveal wire_received0)
          (Ghost.reveal wire_sent0)
          (Ghost.reveal app_log0)
          wire_received1
          wire_sent1
          app_log1)
{
  let status =
    BS.run
      d wire_received0 wire_sent0 pending0 app_log0
      payload payload_len;
  match status {
    BS.BufferedSendOk -> {
      with wire_received1 wire_sent1 pending1 app_log1.
        assert (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1);
      rewrite
        (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1)
        as
        (if channel_send_reusable BS.BufferedSendOk
         then
           DS.top_server_channel_inv
             d wire_received1 wire_sent1 pending1 app_log1
         else
           DS.top_server_channel_terminal
             d wire_received1 wire_sent1 app_log1);
      BS.BufferedSendOk
    }
    BS.BufferedSendPayloadTooLarge -> {
      with wire_received1 wire_sent1 pending1 app_log1.
        assert (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1);
      rewrite
        (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1)
        as
        (if channel_send_reusable BS.BufferedSendPayloadTooLarge
         then
           DS.top_server_channel_inv
             d wire_received1 wire_sent1 pending1 app_log1
         else
           DS.top_server_channel_terminal
             d wire_received1 wire_sent1 app_log1);
      BS.BufferedSendPayloadTooLarge
    }
    BS.BufferedSendFailed -> {
      with wire_received1 wire_sent1 app_log1.
        assert (DS.top_server_channel_terminal
          d wire_received1 wire_sent1 app_log1);
      rewrite
        (DS.top_server_channel_terminal
          d wire_received1 wire_sent1 app_log1)
        as
        (if channel_send_reusable BS.BufferedSendFailed
         then
           DS.top_server_channel_inv
             d wire_received1 wire_sent1 wire_received1 app_log1
         else
           DS.top_server_channel_terminal
             d wire_received1 wire_sent1 app_log1);
      BS.BufferedSendFailed
    }
  }
}

fn channel_send
  (d:server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (payload:array U8.t)
  (payload_bytes:Ghost.erased B.bytes)
  (payload_len:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0) **
    pts_to payload (Ghost.reveal payload_bytes) **
    pure (B.length (Ghost.reveal payload_bytes) == SZ.v payload_len)
  returns status:BS.send_status
  ensures
    exists* wire_received1 wire_sent1 pending1 app_log1.
      (if channel_send_reusable status
       then
         DS.top_server_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
       else
         DS.top_server_channel_terminal
           d wire_received1 wire_sent1 app_log1) **
      pts_to payload (Ghost.reveal payload_bytes) **
      pure (
        CI.send_transition
          channel_message_of_bytes
          channel_send_succeeded
          status
          (Ghost.reveal payload_bytes)
          (Ghost.reveal wire_received0)
          (Ghost.reveal wire_sent0)
          (Ghost.reveal app_log0)
          wire_received1
          wire_sent1
          app_log1)
{
  let flush =
    BS.run_key_update_response d wire_received0 wire_sent0 pending0 app_log0;
  match flush {
    BS.BufferedSendFailed -> {
      with wire_received1 wire_sent1 app_log1.
        assert (DS.top_server_channel_terminal
          d wire_received1 wire_sent1 app_log1);
      rewrite
        (DS.top_server_channel_terminal
          d wire_received1 wire_sent1 app_log1)
        as
        (if channel_send_reusable BS.BufferedSendFailed
         then
           DS.top_server_channel_inv
             d wire_received1 wire_sent1 wire_received1 app_log1
         else
           DS.top_server_channel_terminal
             d wire_received1 wire_sent1 app_log1);
      BS.BufferedSendFailed
    }
    BS.BufferedSendOk -> {
      with wire_received1 wire_sent1 pending1 app_log1.
        assert (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1);
      let status =
        channel_send_core
          d
          (Ghost.hide wire_received1)
          (Ghost.hide wire_sent1)
          (Ghost.hide pending1)
          (Ghost.hide app_log1)
          payload
          payload_bytes
          payload_len;
      with wire_received2 wire_sent2 pending2 app_log2.
        assert ((if channel_send_reusable status
                 then
                   DS.top_server_channel_inv
                     d wire_received2 wire_sent2 pending2 app_log2
                 else
                   DS.top_server_channel_terminal
                     d wire_received2 wire_sent2 app_log2) **
                pts_to payload (Ghost.reveal payload_bytes));
      CPI.lemma_bytes_extends_trans
        (Ghost.reveal wire_received0) wire_received1 wire_received2;
      CPI.lemma_bytes_extends_trans
        (Ghost.reveal wire_sent0) wire_sent1 wire_sent2;
      status
    }
    BS.BufferedSendPayloadTooLarge -> {
      with wire_received1 wire_sent1 pending1 app_log1.
        assert (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1);
      let status =
        channel_send_core
          d
          (Ghost.hide wire_received1)
          (Ghost.hide wire_sent1)
          (Ghost.hide pending1)
          (Ghost.hide app_log1)
          payload
          payload_bytes
          payload_len;
      with wire_received2 wire_sent2 pending2 app_log2.
        assert ((if channel_send_reusable status
                 then
                   DS.top_server_channel_inv
                     d wire_received2 wire_sent2 pending2 app_log2
                 else
                   DS.top_server_channel_terminal
                     d wire_received2 wire_sent2 app_log2) **
                pts_to payload (Ghost.reveal payload_bytes));
      CPI.lemma_bytes_extends_trans
        (Ghost.reveal wire_received0) wire_received1 wire_received2;
      CPI.lemma_bytes_extends_trans
        (Ghost.reveal wire_sent0) wire_sent1 wire_sent2;
      status
    }
  }
}

fn channel_receive_core
  (d:server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (out:array U8.t)
  (old_output:Ghost.erased B.bytes)
  (out_len:SZ.t)
  (network_fuel:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0) **
    pts_to out (Ghost.reveal old_output) **
    pure (B.length (Ghost.reveal old_output) == SZ.v out_len)
  returns result:BR.receive_result
  ensures
    exists* wire_received1 wire_sent1 pending1 app_log1 output.
      (if channel_receive_reusable result
       then
         DS.top_server_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
       else
         DS.top_server_channel_terminal
           d wire_received1 wire_sent1 app_log1) **
      pts_to out output **
      pure (
        B.length output == SZ.v out_len /\
        SZ.v (channel_receive_length result) <= SZ.v out_len /\
        CI.receive_transition
          channel_message_of_bytes
          channel_receive_succeeded
          channel_receive_length
          result
          output
          (Ghost.reveal wire_received0)
          (Ghost.reveal wire_sent0)
          (Ghost.reveal app_log0)
          wire_received1
          wire_sent1
          app_log1)
{
  let result =
    BR.run
      d wire_received0 wire_sent0 pending0 app_log0
      out out_len network_fuel;
  match result.BR.receive_status {
    BR.BufferedReceiveOk -> {
      with wire_received1 wire_sent1 pending1 app_log1.
        assert (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1);
      rewrite
        (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1)
        as
        (if channel_receive_reusable result
         then
           DS.top_server_channel_inv
             d wire_received1 wire_sent1 pending1 app_log1
         else
           DS.top_server_channel_terminal
             d wire_received1 wire_sent1 app_log1);
      result
    }
    BR.BufferedReceiveExhausted -> {
      with wire_received1 wire_sent1 pending1 app_log1.
        assert (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1);
      rewrite
        (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1)
        as
        (if channel_receive_reusable result
         then
           DS.top_server_channel_inv
             d wire_received1 wire_sent1 pending1 app_log1
         else
           DS.top_server_channel_terminal
             d wire_received1 wire_sent1 app_log1);
      result
    }
    BR.BufferedReceiveOutputBufferTooSmall -> {
      with wire_received1 wire_sent1 pending1 app_log1.
        assert (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1);
      rewrite
        (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1)
        as
        (if channel_receive_reusable result
         then
           DS.top_server_channel_inv
             d wire_received1 wire_sent1 pending1 app_log1
         else
           DS.top_server_channel_terminal
             d wire_received1 wire_sent1 app_log1);
      result
    }
    BR.BufferedReceiveClosed -> {
      with wire_received1 wire_sent1 app_log1.
        assert (DS.top_server_channel_terminal
          d wire_received1 wire_sent1 app_log1);
      rewrite
        (DS.top_server_channel_terminal
          d wire_received1 wire_sent1 app_log1)
        as
        (if channel_receive_reusable result
         then
           DS.top_server_channel_inv
             d wire_received1 wire_sent1 wire_received1 app_log1
         else
           DS.top_server_channel_terminal
             d wire_received1 wire_sent1 app_log1);
      result
    }
    BR.BufferedReceiveFailed -> {
      with wire_received1 wire_sent1 app_log1.
        assert (DS.top_server_channel_terminal
          d wire_received1 wire_sent1 app_log1);
      rewrite
        (DS.top_server_channel_terminal
          d wire_received1 wire_sent1 app_log1)
        as
        (if channel_receive_reusable result
         then
           DS.top_server_channel_inv
             d wire_received1 wire_sent1 wire_received1 app_log1
         else
           DS.top_server_channel_terminal
             d wire_received1 wire_sent1 app_log1);
      result
    }
  }
}

fn channel_receive
  (d:server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (out:array U8.t)
  (old_output:Ghost.erased B.bytes)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0) **
    pts_to out (Ghost.reveal old_output) **
    pure (B.length (Ghost.reveal old_output) == SZ.v out_len)
  returns result:BR.receive_result
  ensures
    exists* wire_received1 wire_sent1 pending1 app_log1 output.
      (if channel_receive_reusable result
       then
         DS.top_server_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
       else
         DS.top_server_channel_terminal
           d wire_received1 wire_sent1 app_log1) **
      pts_to out output **
      pure (
        B.length output == SZ.v out_len /\
        SZ.v (channel_receive_length result) <= SZ.v out_len /\
        CI.receive_transition
          channel_message_of_bytes
          channel_receive_succeeded
          channel_receive_length
          result
          output
          (Ghost.reveal wire_received0)
          (Ghost.reveal wire_sent0)
          (Ghost.reveal app_log0)
          wire_received1
          wire_sent1
          app_log1)
{
  let flush =
    BS.run_key_update_response d wire_received0 wire_sent0 pending0 app_log0;
  match flush {
    BS.BufferedSendFailed -> {
      with wire_received1 wire_sent1 app_log1.
        assert (DS.top_server_channel_terminal
          d wire_received1 wire_sent1 app_log1);
      let failed = {
        BR.receive_status = BR.BufferedReceiveFailed;
        BR.receive_len = 0sz;
      };
      rewrite
        (DS.top_server_channel_terminal
          d wire_received1 wire_sent1 app_log1)
        as
        (if channel_receive_reusable failed
         then
           DS.top_server_channel_inv
             d wire_received1 wire_sent1 wire_received1 app_log1
         else
           DS.top_server_channel_terminal
             d wire_received1 wire_sent1 app_log1);
      failed
    }
    BS.BufferedSendOk -> {
      with wire_received1 wire_sent1 pending1 app_log1.
        assert (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1);
      let result =
        channel_receive_core
          d
          (Ghost.hide wire_received1)
          (Ghost.hide wire_sent1)
          (Ghost.hide pending1)
          (Ghost.hide app_log1)
          out
          old_output
          out_len
          network_fuel;
      with wire_received2 wire_sent2 pending2 app_log2 output.
        assert ((if channel_receive_reusable result
                 then
                   DS.top_server_channel_inv
                     d wire_received2 wire_sent2 pending2 app_log2
                 else
                   DS.top_server_channel_terminal
                     d wire_received2 wire_sent2 app_log2) **
                pts_to out output);
      CPI.lemma_bytes_extends_trans
        (Ghost.reveal wire_received0) wire_received1 wire_received2;
      CPI.lemma_bytes_extends_trans
        (Ghost.reveal wire_sent0) wire_sent1 wire_sent2;
      result
    }
    BS.BufferedSendPayloadTooLarge -> {
      with wire_received1 wire_sent1 pending1 app_log1.
        assert (DS.top_server_channel_inv
          d wire_received1 wire_sent1 pending1 app_log1);
      let result =
        channel_receive_core
          d
          (Ghost.hide wire_received1)
          (Ghost.hide wire_sent1)
          (Ghost.hide pending1)
          (Ghost.hide app_log1)
          out
          old_output
          out_len
          network_fuel;
      with wire_received2 wire_sent2 pending2 app_log2 output.
        assert ((if channel_receive_reusable result
                 then
                   DS.top_server_channel_inv
                     d wire_received2 wire_sent2 pending2 app_log2
                 else
                   DS.top_server_channel_terminal
                     d wire_received2 wire_sent2 app_log2) **
                pts_to out output);
      CPI.lemma_bytes_extends_trans
        (Ghost.reveal wire_received0) wire_received1 wire_received2;
      CPI.lemma_bytes_extends_trans
        (Ghost.reveal wire_sent0) wire_sent1 wire_sent2;
      result
    }
  }
}

noextract
let server_channel_implementation
  : CI.channel_implementation
      DS.top_server_driver
      SP.canonical_server
      CS.connection_state
      CW.wire_message
      CTypes.server_local_event
      EAPI.local_output
      B.bytes
      BS.send_status
      BR.receive_result
      SP.server_protocol_implementation
  =
  {
    CI.ci_protocol_impl = DS.top_server_driver_canonical;
    CI.ci_project = TChannel.application_log;
    CI.ci_message_of_bytes = channel_message_of_bytes;
    CI.ci_channel_inv = DS.top_server_channel_inv;
    CI.ci_terminal_inv = DS.top_server_channel_terminal;
    CI.ci_io_frame = DS.top_server_channel_io_frame;
    CI.ci_snapshot = DS.top_server_channel_snapshot;
    CI.ci_send_succeeded = channel_send_succeeded;
    CI.ci_send_usable = channel_send_reusable;
    CI.ci_receive_succeeded = channel_receive_succeeded;
    CI.ci_receive_usable = channel_receive_reusable;
    CI.ci_receive_length = channel_receive_length;
    CI.ci_open_io_channel = BChan.open_io_channel;
    CI.ci_close_io_channel = BChan.close_io_channel;
    CI.ci_invariant_valid = CImpl.channel_invariant_valid;
    CI.ci_take_snapshot = CImpl.take_channel_snapshot;
    CI.ci_recall_snapshot = CImpl.recall_channel_snapshot;
    CI.ci_send = channel_send;
    CI.ci_receive = channel_receive;
  }
