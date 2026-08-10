module TLS13.Impl.Server.Driver.BufferedSend

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module CPI = Common.ProtocolImplementation
module DS = TLS13.Impl.Server.Driver.State
module SZ = FStar.SizeT
module U8 = FStar.UInt8

type send_status =
  | BufferedSendOk
  | BufferedSendPayloadTooLarge
  | BufferedSendFailed

(* The channel's view of a payload is the payload itself: the server's
   application log records raw byte messages. *)
noextract
let channel_message_of_bytes (bytes:B.bytes) : B.bytes = bytes

(* Only [BufferedSendOk] actually appends the payload to the application sent
   log.  [BufferedSendPayloadTooLarge] rejects before stepping and
   [BufferedSendFailed] fails the connection, and neither moves the log. *)
noextract
let send_succeeded (status:send_status) : bool =
  match status with
  | BufferedSendOk -> true
  | _ -> false

fn query_application_ready
  (d:DS.top_server_driver)
  requires
    DS.top_server_driver_connected
      d
      'st
      'certificate_chain
      'credential_identity
      'received
      'sent
  returns ready:bool
  ensures
    DS.top_server_driver_connected
      d
      'st
      'certificate_chain
      'credential_identity
      'received
      'sent **
    pure (
      TLS13.Impl.Server.Types.server_end_to_end_invariant 'st /\
      (ready ==>
        'st.TLS13.Spec.StateMachine.cs_model
          .TLS13.Spec.StateMachine.model_control ==
            TLS13.Spec.StateMachine.ControlApplicationData /\
        TLS13.Spec.StateMachine.application_record_keys_installed_for_role
          TLS13.Spec.StateMachine.ServerEndpoint
          'st.TLS13.Spec.StateMachine.cs_model))

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
           d wire_received1 wire_sent1 pending1 app_log1 **
         pure (
           CI.send_transition
             channel_message_of_bytes
             send_succeeded
             status
             (Ghost.reveal 'payload_bytes)
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal app_log0)
             wire_received1
             wire_sent1
             app_log1)
     | BufferedSendFailed ->
       exists* wire_received1 wire_sent1 app_log1.
         DS.top_server_channel_terminal
           d wire_received1 wire_sent1 app_log1 **
         pure (
           CI.send_transition
             channel_message_of_bytes
             send_succeeded
             status
             (Ghost.reveal 'payload_bytes)
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal app_log0)
             wire_received1
             wire_sent1
             app_log1))

(* Server-initiated KeyUpdate (RFC 8446 4.6.3).  [request] selects the request
   form: [true] asks the peer to rotate its own sending key in reply,
   [false] is a bare rotation of our write key.  The connection stays in
   [ControlApplicationData] either way, so the channel invariant is
   re-established exactly as for an application-data send. *)
fn run_key_update
  (d:DS.top_server_driver)
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
  returns status:send_status
  ensures
    (match status with
     | BufferedSendOk
     | BufferedSendPayloadTooLarge ->
       exists* wire_received1 wire_sent1 pending1 app_log1.
         DS.top_server_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1 **
         pure (
           CPI.histories_ahead
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             wire_received1
             wire_sent1 /\
           app_log1 == Ghost.reveal app_log0)
     | BufferedSendFailed ->
       exists* wire_received1 wire_sent1 app_log1.
         DS.top_server_channel_terminal
           d wire_received1 wire_sent1 app_log1 **
         pure (
           CPI.histories_ahead
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             wire_received1
             wire_sent1 /\
           app_log1 == Ghost.reveal app_log0))

(* Discharges the RFC 8446 4.6.3 KeyUpdate response obligation if one is
   outstanding; a no-op otherwise.  Intended to be called after a receive. *)
fn run_key_update_response
  (d:DS.top_server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0)
  returns status:send_status
  ensures
    (match status with
     | BufferedSendOk
     | BufferedSendPayloadTooLarge ->
       exists* wire_received1 wire_sent1 pending1 app_log1.
         DS.top_server_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1 **
         pure (
           CPI.histories_ahead
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             wire_received1
             wire_sent1 /\
           app_log1 == Ghost.reveal app_log0)
     | BufferedSendFailed ->
       exists* wire_received1 wire_sent1 app_log1.
         DS.top_server_channel_terminal
           d wire_received1 wire_sent1 app_log1 **
         pure (
           CPI.histories_ahead
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             wire_received1
             wire_sent1 /\
           app_log1 == Ghost.reveal app_log0))
