module TLS13.Impl.Client.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module CP = TLS13.Impl.Client.CanonicalProtocol
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Spec.Endpoint.Wire
module DS = TLS13.Impl.Client.Driver.State
module EAPI = TLS13.Spec.Endpoint.API
module MR = Pulse.Lib.MonotonicGhostRef
module O = TLS13.OpenSSL
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

type client_driver = DS.client_driver
type client_auth_config = O.auth_config

noextract
let client_driver_wire_logs_match = DS.client_driver_wire_logs_match

noextract
let client_driver_live = DS.client_driver_live

noextract
let client_driver_connected = DS.client_driver_connected

noextract
let client_driver_closed = DS.client_driver_closed

noextract
let client_driver_released
  (d:client_driver)
  (st:CS.connection_state)
  : slprop =
  CR.connection_released d.DS.client_driver_client st **
  DS.client_driver_canonical_progress d st **
  (exists* h. MR.pts_to d.DS.client_driver_tcp_history #1.0R h)

noextract
let client_driver_application_ready = DS.client_driver_application_ready

noextract
let client_driver_sent_log_exact = DS.client_driver_sent_log_exact

noextract
let client_driver_received_log_accounted =
  DS.client_driver_received_log_accounted

noextract
let client_driver_received_log_exact_prefix =
  DS.client_driver_received_log_exact_prefix

noextract
let client_driver_received_no_read_ahead =
  DS.client_driver_received_no_read_ahead

type driver_workflow_status = DS.driver_workflow_status

noextract
let client_driver_local_write_correct = DS.client_driver_local_write_correct

noextract
let client_driver_send_status_correct = DS.client_driver_send_status_correct

noextract
let client_driver_payload_too_large = DS.client_driver_payload_too_large

noextract
let client_driver_send_correct = DS.client_driver_send_correct

noextract
let client_driver_close_status_correct = DS.client_driver_close_status_correct

noextract
let client_driver_close_correct = DS.client_driver_close_correct

type client_receive_result = DS.client_receive_result

noextract
type client_receive_observation = DS.client_receive_observation

noextract
let client_receive_observation_network_correct =
  DS.client_receive_observation_network_correct

noextract
let client_driver_receive_status_correct =
  DS.client_driver_receive_status_correct

noextract
let client_driver_receive_copyout_correct =
  DS.client_driver_receive_copyout_correct

noextract
let client_driver_receive_correct = DS.client_driver_receive_correct

fn new_auth_config
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len)
  returns config: client_auth_config
  ensures pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          O.is_auth_config
            config
            (Ghost.reveal 'server_name_bytes)
            (Ghost.reveal 'trust_anchors_bytes)
            validation_time_seconds

fn free_auth_config (config:client_auth_config)
  requires O.is_auth_config
    config
    'server_name_bytes
    'trust_anchors_bytes
    'validation_time_seconds
  ensures emp

fn new_client_with_auth_config
  (config:client_auth_config)
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires O.is_auth_config
             config
             (Ghost.reveal 'server_name_bytes)
             (Ghost.reveal 'trust_anchors_bytes)
             validation_time_seconds **
           pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_hostname_len /\
                 SZ.v trust_anchors_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_trust_anchors_len)
  returns result: client_driver
  ensures O.is_auth_config
            config
            (Ghost.reveal 'server_name_bytes)
            (Ghost.reveal 'trust_anchors_bytes)
            validation_time_seconds **
          pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          client_driver_live
            result
            (CR.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds) **
          pure (CT.client_state_correct
            (CR.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds) /\
                CT.client_end_to_end_invariant
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds))

noextract
let channel_message_of_bytes (bytes:B.bytes) : B.bytes = bytes

noextract
let channel_send_succeeded (status:driver_workflow_status) : bool =
  match status with
  | DS.DriverWorkflowOk -> true
  | _ -> false

noextract
let channel_receive_succeeded (result:client_receive_result) : bool =
  match result.DS.client_receive_status with
  | DS.DriverWorkflowOk -> true
  | _ -> false

noextract
let channel_receive_length (result:client_receive_result) : SZ.t =
  result.DS.client_receive_len

(* A send leaves the channel reusable (live) exactly for success and for the
   payload-too-large rejection (which does not touch the connection). A hard
   step failure is terminal. *)
noextract
let channel_send_reusable
  (status:driver_workflow_status)
  : bool =
  match status with
  | DS.DriverWorkflowOk -> true
  | DS.DriverWorkflowPayloadTooLarge -> true
  | _ -> false

(* A receive leaves the channel reusable (live) for exactly the statuses where
   the connection remains open: success, need-more-input, exhausted, and
   output-buffer-too-small.  Every other status — a hard step failure, a peer
   close, or any status that cannot arise on the receive path (e.g.
   payload-too-large, which is send-only) — is terminal.  The cases are listed
   explicitly so the live set is exactly {Ok, NeedMoreInput, Exhausted,
   OutputBufferTooSmall} and cannot silently admit an unintended status. *)
noextract
let channel_receive_reusable
  (result:client_receive_result)
  : bool =
  match result.DS.client_receive_status with
  | DS.DriverWorkflowOk -> true
  | DS.DriverWorkflowNeedMoreInput -> true
  | DS.DriverWorkflowExhausted -> true
  | DS.DriverWorkflowOutputBufferTooSmall -> true
  | _ -> false

noextract
let client_driver_is_closed
  (d:client_driver)
  : slprop =
  exists* st. client_driver_closed d st

noextract
let client_channel_after_operation
  (d:client_driver)
  (reusable:bool)
  (wire_received wire_sent pending:B.bytes)
  (app_log:CI.application_log B.bytes)
  : slprop =
  if reusable
  then DS.client_channel_inv d wire_received wire_sent pending app_log
  else client_driver_is_closed d

fn connect
  (d:client_driver)
  (connect_host:array U8.t)
  (connect_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires client_driver_live d 'st0 **
           pts_to connect_host 'connect_host_bytes **
           pure (B.length 'connect_host_bytes == SZ.v connect_host_len)
  returns status:driver_workflow_status
  ensures pts_to connect_host 'connect_host_bytes **
          (match status with
           | DS.DriverWorkflowOk ->
             exists* wire_received wire_sent pending app_log.
               DS.client_channel_inv d wire_received wire_sent pending app_log
           | _ ->
             exists* st1. client_driver_closed d st1)

(**
  Sends [payload] as one TLS 1.3 application-data record. Payloads above the
  16,384-byte record limit are rejected without changing the connection.
**)
fn send
  (d:client_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (payload:array U8.t)
  (payload_bytes:Ghost.erased B.bytes)
  (payload_len:SZ.t)
  requires DS.client_channel_inv
             d
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal pending0)
             (Ghost.reveal app_log0) **
           pts_to payload (Ghost.reveal payload_bytes) **
           pure (B.length (Ghost.reveal payload_bytes) == SZ.v payload_len)
  returns status:driver_workflow_status
  ensures exists* wire_received1 wire_sent1 pending1 app_log1.
          client_channel_after_operation
            d
            (channel_send_reusable status)
            wire_received1
            wire_sent1
            pending1
            app_log1 **
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

fn receive
  (d:client_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (out:array U8.t)
  (old_output:Ghost.erased B.bytes)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires DS.client_channel_inv
             d
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal pending0)
             (Ghost.reveal app_log0) **
           pts_to out (Ghost.reveal old_output) **
           pure (B.length (Ghost.reveal old_output) == SZ.v out_len)
  returns result:client_receive_result
  ensures exists* wire_received1 wire_sent1 pending1 app_log1 output.
          client_channel_after_operation
            d
            (channel_receive_reusable result)
            wire_received1
            wire_sent1
            pending1
            app_log1 **
          pts_to out output **
          pure (
            B.length output == SZ.v out_len /\
            SZ.v result.DS.client_receive_len <= SZ.v out_len /\
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

fn close
  (d:client_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (wait_for_peer:bool)
  (fuel:SZ.t)
  requires DS.client_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log)
  returns status:driver_workflow_status
  ensures exists* st1.
          client_driver_closed d st1 **
          pure (exists st0 st_close_notify.
            st1.CS.cs_model.CS.model_config ==
              st0.CS.cs_model.CS.model_config /\
            client_driver_close_correct
              st0
              st_close_notify
              status
              wait_for_peer)

(**
  Safely disposes a connected transport after a workflow failure without
  attempting to send close_notify.
**)
fn abort
  (d:client_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires DS.client_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log)
  ensures exists* st. client_driver_closed d st

fn free (d:client_driver)
  requires client_driver_closed d 'st
  ensures client_driver_released d 'st

noextract
val client_channel_implementation
  : CI.channel_implementation
      DS.client_driver
      CP.canonical_client
      CS.connection_state
      CW.wire_message
      CTypes.client_local_event
      EAPI.local_output
      B.bytes
      DS.driver_workflow_status
      DS.client_receive_result
      CP.client_protocol_implementation
