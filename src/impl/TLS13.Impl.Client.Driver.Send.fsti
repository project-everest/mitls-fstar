module TLS13.Impl.Client.Driver.Send

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
open TLS13.Impl.Client.Driver.State

(**
  Sends [payload] as one TLS 1.3 application-data record. Payloads above the
  16,384-byte record limit are rejected without changing the connection.
**)
fn run
  (d:client_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires client_driver_connected d 'st0 'received0 'sent0 **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len) **
           pure (CT.connection_control_not_failed 'st0)
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
                client_driver_received_log_accounted st1 received1 /\
                ((status == DriverWorkflowOk \/ status == DriverWorkflowPayloadTooLarge) ==>
                  CT.connection_control_not_failed st1))

(**
  Is a mandated KeyUpdate reply due?  RFC 8446 4.6.3 obliges an endpoint that
  received [update_requested] to answer with its own KeyUpdate.  The gate is
  exactly [run_key_update]'s own success condition with the pending flag added,
  so a [true] here cannot lead to a spurious step failure.
**)
fn query_key_update_response_pending
  (d:client_driver)
  requires client_driver_connected d 'st0 'received0 'sent0
  returns pending:bool
  ensures client_driver_connected d 'st0 'received0 'sent0

(**
  Client-initiated KeyUpdate (RFC 8446 4.6.3).  [request] selects the request
  form: [true] sends [update_requested], asking the peer to rotate its own
  sending key in reply; [false] sends [update_not_requested], rotating only our
  write key.  The payload is empty, so unlike [run] there is no length bound to
  test and no payload-too-large outcome.
**)
fn run_key_update
  (d:client_driver)
  (request:bool)
  requires client_driver_connected d 'st0 'received0 'sent0 **
           pure (CT.connection_control_not_failed 'st0)
  returns status:driver_workflow_status
  ensures exists* st1 received1 sent1.
          client_driver_connected d st1 received1 sent1 **
          pure (client_driver_key_update_correct
                 'st0
                 st1
                 status
                 (if request
                  then CT.LocalSendKeyUpdateRequested
                  else CT.LocalSendKeyUpdate)
                 (Ghost.reveal 'sent0)
                 sent1 /\
                st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config /\
                client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0) /\
                client_driver_received_log_accounted
                  'st0
                  (Ghost.reveal 'received0) /\
                client_driver_sent_log_exact st1 sent1 /\
                client_driver_received_log_accounted st1 received1 /\
                (status == DriverWorkflowOk ==>
                  CT.connection_control_not_failed st1))
