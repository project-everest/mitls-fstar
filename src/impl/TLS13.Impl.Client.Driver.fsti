module TLS13.Impl.Client.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module DS = TLS13.Impl.Client.Driver.State
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

type client_driver = DS.client_driver

noextract
let client_driver_wire_logs_match = DS.client_driver_wire_logs_match

noextract
let client_driver_live = DS.client_driver_live

noextract
let client_driver_connected = DS.client_driver_connected

noextract
let client_driver_closed = DS.client_driver_closed

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

fn new_client
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_hostname_len /\
                 SZ.v trust_anchors_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_trust_anchors_len)
  returns result: client_driver
  ensures pts_to server_name 'server_name_bytes **
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
  ensures exists* st1.
          pts_to connect_host 'connect_host_bytes **
          (match status with
           | DS.DriverWorkflowOk ->
             exists* received sent.
               client_driver_connected d st1 received sent **
               pure (client_driver_application_ready st1 /\
                     st1.CS.cs_model.CS.model_config ==
                       'st0.CS.cs_model.CS.model_config /\
                     client_driver_sent_log_exact st1 sent /\
                     client_driver_received_log_accounted st1 received /\
                     client_driver_received_log_exact_prefix st1 received /\
                     client_driver_received_no_read_ahead st1 received)
           | _ ->
             client_driver_closed d st1)

(**
  Sends [payload] as one TLS 1.3 application-data record. Payloads above the
  16,384-byte record limit are rejected without changing the connection.
**)
fn send
  (d:client_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires client_driver_connected d 'st0 'received0 'sent0 **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len)
  returns status:driver_workflow_status
  ensures exists* st1 received1 sent1.
          pts_to payload 'payload_bytes **
          client_driver_connected d st1 received1 sent1 **
          pure (client_driver_send_correct
                 'st0
                 st1
                 status
                 (Ghost.reveal 'payload_bytes)
                 (Ghost.reveal 'sent0)
                 sent1 /\
                st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config /\
                client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0) /\
                client_driver_received_log_accounted
                  'st0
                  (Ghost.reveal 'received0) /\
                client_driver_sent_log_exact st1 sent1 /\
                client_driver_received_log_accounted st1 received1)

fn receive
  (d:client_driver)
  (out:array U8.t)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires client_driver_connected d 'st0 'received0 'sent0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns result:client_receive_result
  ensures exists* st1 received1 sent1 out_bytes.
          client_driver_connected d st1 received1 sent1 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v result.DS.client_receive_len <= SZ.v out_len /\
                st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config /\
                client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0) /\
                client_driver_received_log_accounted
                  'st0
                  (Ghost.reveal 'received0) /\
                client_driver_sent_log_exact st1 sent1 /\
                client_driver_received_log_accounted st1 received1 /\
                (exists obs app_out.
                  client_driver_receive_correct
                    'st0
                    st1
                    result
                    obs
                    app_out
                    out_bytes))

fn close
  (d:client_driver)
  (wait_for_peer:bool)
  (fuel:SZ.t)
  requires client_driver_connected d 'st0 'received0 'sent0
  returns status:driver_workflow_status
  ensures exists* st1.
          client_driver_closed d st1 **
          pure (st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config /\
                client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0) /\
                client_driver_received_log_accounted
                  'st0
                  (Ghost.reveal 'received0) /\
                (exists st_close_notify.
                  client_driver_close_correct
                    'st0
                    st_close_notify
                    status
                    wait_for_peer))

(**
  Safely disposes a connected transport after a workflow failure without
  attempting to send close_notify.
**)
fn abort
  (d:client_driver)
  requires client_driver_connected d 'st0 'received0 'sent0
  ensures client_driver_closed d 'st0
