module TLS13.Impl.Client.Driver.Close

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

fn run
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
