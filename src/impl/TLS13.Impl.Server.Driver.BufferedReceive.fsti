module TLS13.Impl.Server.Driver.BufferedReceive

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module CPI = Common.ProtocolImplementation
module DS = TLS13.Impl.Server.Driver.State
module SZ = FStar.SizeT
module U8 = FStar.UInt8

type receive_status =
  | BufferedReceiveOk
  | BufferedReceiveExhausted
  | BufferedReceiveOutputBufferTooSmall
  | BufferedReceiveClosed
  | BufferedReceiveFailed

noeq type receive_result = {
  receive_status: receive_status;
  receive_len: SZ.t;
}

(* The channel's view of received bytes is the bytes themselves. *)
noextract
let channel_message_of_bytes (bytes:B.bytes) : B.bytes = bytes

(* Only [BufferedReceiveOk] delivers application data; every other status
   leaves the application log where it was. *)
noextract
let receive_succeeded (result:receive_result) : bool =
  BufferedReceiveOk? result.receive_status

noextract
let receive_result_length (result:receive_result) : SZ.t = result.receive_len

fn run
  (d:DS.top_server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (out:array U8.t)
  (out_len:SZ.t)
  (network_fuel:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0) **
    pts_to out 'old_output **
    pure (B.length 'old_output == SZ.v out_len)
  returns result:receive_result
  ensures
    exists* output.
      pts_to out output **
      pure (
        B.length output == SZ.v out_len /\
        SZ.v result.receive_len <= SZ.v out_len) **
      (match result.receive_status with
       | BufferedReceiveOk
       | BufferedReceiveExhausted
       | BufferedReceiveOutputBufferTooSmall ->
         exists* wire_received1 wire_sent1 pending1 app_log1.
           DS.top_server_channel_inv
             d wire_received1 wire_sent1 pending1 app_log1 **
           pure (
             CI.receive_transition
               channel_message_of_bytes
               receive_succeeded
               receive_result_length
               result
               output
               (Ghost.reveal wire_received0)
               (Ghost.reveal wire_sent0)
               (Ghost.reveal app_log0)
               wire_received1
               wire_sent1
               app_log1)
       | BufferedReceiveClosed
       | BufferedReceiveFailed ->
         exists* wire_received1 wire_sent1 app_log1.
           DS.top_server_channel_terminal
             d wire_received1 wire_sent1 app_log1 **
           pure (
             CI.receive_transition
               channel_message_of_bytes
               receive_succeeded
               receive_result_length
               result
               output
               (Ghost.reveal wire_received0)
               (Ghost.reveal wire_sent0)
               (Ghost.reveal app_log0)
               wire_received1
               wire_sent1
               app_log1))

fn await_peer_close
  (d:DS.top_server_driver)
  (network_fuel:SZ.t)
  requires
    DS.top_server_driver_connected
      d 'st0 'certificate_chain 'credential_identity 'received0 'sent0 **
    pure (TLS13.Impl.Server.Types.server_connection_control_not_failed 'st0)
  returns status:receive_status
  ensures
    exists* st1 received1 sent1.
      DS.top_server_driver_connected
        d st1 'certificate_chain 'credential_identity received1 sent1 **
      pure (
        status <> BufferedReceiveOk /\
        status <> BufferedReceiveOutputBufferTooSmall /\
        (status == BufferedReceiveExhausted ==>
          TLS13.Impl.Server.Types.server_connection_control_not_failed st1))
