module TLS13.Impl.Server.Driver.BufferedSend

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module DS = TLS13.Impl.Server.Driver.State
module SZ = FStar.SizeT
module U8 = FStar.UInt8

type send_status =
  | BufferedSendOk
  | BufferedSendPayloadTooLarge
  | BufferedSendFailed

fn run
  (d:DS.top_server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0) **
    pts_to payload 'payload_bytes **
    pure (B.length 'payload_bytes == SZ.v payload_len)
  returns status:send_status
  ensures
    pts_to payload 'payload_bytes **
    (match status with
     | BufferedSendOk
     | BufferedSendPayloadTooLarge ->
       exists* wire_received1 wire_sent1 pending1 app_log1.
         DS.top_server_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
     | BufferedSendFailed ->
       exists* wire_received1 wire_sent1 app_log1.
         DS.top_server_channel_terminal
           d wire_received1 wire_sent1 app_log1)
