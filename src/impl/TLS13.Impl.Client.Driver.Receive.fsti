module TLS13.Impl.Client.Driver.Receive

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module DS = TLS13.Impl.Client.Driver.State
module L = TLS13.Impl.Messages
module SZ = FStar.SizeT
module TChannel = TLS13.Impl.Channel
module U16 = FStar.UInt16
module U8 = FStar.UInt8
open TLS13.Impl.Client.Driver.State

fn run
  (d:client_driver)
  (out:array U8.t)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires client_driver_connected d 'st0 'received0 'sent0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 L.max_record_fragment_len <= SZ.v out_len)
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
                TChannel.application_log st1 ==
                  (if result.DS.client_receive_status == DriverWorkflowOk
                   then
                     CI.append_received
                       (TChannel.application_log 'st0)
                       (FStar.Seq.slice
                         out_bytes
                         0
                         (SZ.v result.DS.client_receive_len))
                   else TChannel.application_log 'st0) /\
                (exists obs app_out.
                  client_driver_receive_correct
                    'st0
                    st1
                    result
                    obs
                    app_out
                    out_bytes))
