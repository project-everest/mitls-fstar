module TLS13.Impl.Client.Driver.Connect

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module A = Pulse.Lib.Array
module C = TLS13.Impl.Client
module CP = TLS13.Impl.Client.CanonicalProtocol
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CQ = TLS13.Impl.ConnectionState.Queries
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module CTypes = TLS13.Impl.CanonicalTypes
module EC = TLS13.Spec.Endpoint.Client
module ID = FStar.IndefiniteDescription
module IO = Common.TCP
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Sem = TLS13.Wire.Semantics
module O = TLS13.OpenSSL
module Box = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.Spec.StateMachine.ClientTrace
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module DS = TLS13.Impl.Client.Driver.State
module DC = TLS13.Impl.Client.Driver.Core
module DCleanup = TLS13.Impl.Client.Driver.Cleanup
open TLS13.Impl.Client.Driver.State
open TLS13.Impl.Client.Driver.Core
open TLS13.Impl.Client.Driver.Cleanup
fn run
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
           | DriverWorkflowOk ->
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
{
  unfold (client_driver_live d 'st0);
  with buffered_len.
    assert (C.connection_exactly d.client_driver_client 'st0 **
            O.is_auth_context d.client_driver_auth **
            Box.pts_to d.client_driver_channel no_channel **
            client_driver_buffers d B.empty buffered_len **
            pure (client_driver_wire_logs_match 'st0 B.empty B.empty B.empty 0sz));
  unfold (client_driver_buffers d B.empty buffered_len);
  let current_buffered_len = Box.(!d.client_driver_buffered_len);
  assert (pure (current_buffered_len == buffered_len));
  assert (pure (current_buffered_len == 0sz));
  fold (client_driver_buffers d B.empty buffered_len);
  let ch_opt = IO.connect_tcp connect_host connect_host_len port;
  match ch_opt {
    None -> {
      free_disconnected_client_driver d current_buffered_len;
      DriverWorkflowStepFailed
    }
    Some ch -> {
      assert (pure (client_driver_wire_logs_match 'st0 B.empty B.empty B.empty current_buffered_len));
      fold (channel_open ch 'st0 B.empty current_buffered_len);
      unfold (client_driver_buffers d B.empty buffered_len);
      with empty_payload raw network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out local_app_out.
        assert (Box.pts_to d.client_driver_buffered_len buffered_len **
                V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
                V.pts_to d.client_driver_raw #1.0R raw **
                V.pts_to d.client_driver_network_out #1.0R network_out **
                V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
                V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
                V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
                V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
                V.pts_to d.client_driver_app_out #1.0R app_out **
                V.pts_to d.client_driver_local_app_out #1.0R local_app_out);
      V.to_array_pts_to d.client_driver_empty_payload;
      V.to_array_pts_to d.client_driver_raw;
      V.to_array_pts_to d.client_driver_network_out;
      V.to_array_pts_to d.client_driver_auth_leaf_der;
      V.to_array_pts_to d.client_driver_auth_payload;
      V.to_array_pts_to d.client_driver_auth_cv_input;
      V.to_array_pts_to d.client_driver_auth_signature;
      V.to_array_pts_to d.client_driver_app_out;
      let core = {
        driver_client = d.client_driver_client;
        driver_channel = ch;
        driver_progress = d.client_driver_progress;
        driver_initial = d.client_driver_initial;
      };
      let td = {
        top_driver_core = core;
        top_driver_auth = d.client_driver_auth;
      };
      unfold (client_driver_canonical_progress d 'st0);
      rewrite
        (MR.pts_to d.client_driver_progress #1.0R 'st0)
        as
        (MR.pts_to core.driver_progress #1.0R 'st0);
      rewrite
        (MR.snapshot d.client_driver_progress (Ghost.reveal d.client_driver_initial))
        as
        (MR.snapshot core.driver_progress (Ghost.reveal core.driver_initial));
      fold (driver_canonical_progress core 'st0);
      rewrite (C.connection_exactly d.client_driver_client 'st0) as
        (C.connection_exactly core.driver_client 'st0);
      rewrite (channel_open ch 'st0 B.empty current_buffered_len) as
        (channel_open core.driver_channel 'st0 B.empty current_buffered_len);
      fold (driver_exactly core 'st0 B.empty current_buffered_len);
      rewrite (driver_exactly core 'st0 B.empty current_buffered_len) as
        (driver_exactly td.top_driver_core 'st0 B.empty current_buffered_len);
      rewrite (O.is_auth_context d.client_driver_auth) as (O.is_auth_context td.top_driver_auth);
      fold (top_driver_exactly td 'st0 B.empty current_buffered_len);
      let result =
        driver_handshake
          td
          (V.vec_to_array d.client_driver_empty_payload)
          (V.vec_to_array d.client_driver_raw)
          driver_rx_capacity
          current_buffered_len
          (V.vec_to_array d.client_driver_network_out)
          driver_network_out_capacity
          (V.vec_to_array d.client_driver_auth_leaf_der)
          driver_auth_leaf_der_capacity
          (V.vec_to_array d.client_driver_auth_payload)
          (V.vec_to_array d.client_driver_auth_cv_input)
          driver_certificate_verify_input_capacity
          (V.vec_to_array d.client_driver_auth_signature)
          driver_signature_capacity
          driver_public_key_payload_capacity
          driver_server_finished_payload_len
          (V.vec_to_array d.client_driver_app_out)
          driver_app_out_capacity
          local_fuel
          fuel;
      with st1 buffered_after raw_bytes network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
        assert (top_driver_exactly td st1 buffered_after result.driver_workflow_rx_len **
                pts_to (V.vec_to_array d.client_driver_empty_payload) empty_payload **
                pts_to (V.vec_to_array d.client_driver_raw) raw_bytes **
                pts_to (V.vec_to_array d.client_driver_network_out) network_out_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_leaf_der) auth_leaf_der_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_payload) auth_payload_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_cv_input) auth_cv_input_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_signature) auth_signature_bytes **
                pts_to (V.vec_to_array d.client_driver_app_out) app_out_bytes);
      assert (pure (st1.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      unfold (top_driver_exactly td st1 buffered_after result.driver_workflow_rx_len);
      rewrite (driver_exactly td.top_driver_core st1 buffered_after result.driver_workflow_rx_len) as
        (driver_exactly core st1 buffered_after result.driver_workflow_rx_len);
      unfold (driver_exactly core st1 buffered_after result.driver_workflow_rx_len);
      unfold (driver_canonical_progress core st1);
      rewrite
        (MR.pts_to core.driver_progress #1.0R st1)
        as
        (MR.pts_to d.client_driver_progress #1.0R st1);
      rewrite
        (MR.snapshot core.driver_progress (Ghost.reveal core.driver_initial))
        as
        (MR.snapshot d.client_driver_progress (Ghost.reveal d.client_driver_initial));
      fold (client_driver_canonical_progress d st1);
      V.to_vec_pts_to d.client_driver_empty_payload;
      V.to_vec_pts_to d.client_driver_raw;
      V.to_vec_pts_to d.client_driver_network_out;
      V.to_vec_pts_to d.client_driver_auth_leaf_der;
      V.to_vec_pts_to d.client_driver_auth_payload;
      V.to_vec_pts_to d.client_driver_auth_cv_input;
      V.to_vec_pts_to d.client_driver_auth_signature;
      V.to_vec_pts_to d.client_driver_app_out;
      Box.(d.client_driver_buffered_len := result.driver_workflow_rx_len);
      assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v driver_rx_capacity));
      fold (client_driver_buffers d buffered_after result.driver_workflow_rx_len);
      rewrite (C.connection_exactly core.driver_client st1) as
        (C.connection_exactly d.client_driver_client st1);
      rewrite (channel_open core.driver_channel st1 buffered_after result.driver_workflow_rx_len) as
        (channel_open ch st1 buffered_after result.driver_workflow_rx_len);
      rewrite (O.is_auth_context td.top_driver_auth) as
        (O.is_auth_context d.client_driver_auth);
      match result.driver_workflow_status {
        DriverWorkflowOk -> {
         unfold (channel_open ch st1 buffered_after result.driver_workflow_rx_len);
         with received sent.
           assert (IO.is_channel ch received sent **
                   pure (client_driver_wire_logs_match st1 received sent buffered_after result.driver_workflow_rx_len));
         let retained_empty = result.driver_workflow_rx_len = 0sz;
         if retained_empty {
           assert (pure (client_driver_sent_log_exact st1 sent));
           lemma_client_driver_wire_logs_match_received_accounted
             st1
             received
             sent
             buffered_after
             result.driver_workflow_rx_len;
           assert (pure (client_driver_received_log_accounted st1 received));
           assert (pure (st1.CS.cs_model.CS.model_control == CS.ControlApplicationData));
           assert (pure (CT.connection_control_not_failed st1));
           lemma_client_driver_wire_logs_match_received_exact_prefix
             st1
             received
             sent
             buffered_after
             result.driver_workflow_rx_len;
           assert (pure (client_driver_received_log_exact_prefix st1 received));
           lemma_client_driver_wire_logs_match_received_no_read_ahead
             st1
             received
             sent
             buffered_after
             result.driver_workflow_rx_len;
           assert (pure (client_driver_received_no_read_ahead st1 received));
           rewrite (C.connection_exactly d.client_driver_client st1) as
             (CR.connection_exactly d.client_driver_client st1);
           let keys_installed =
             CQ.client_application_record_keys_installed_runtime
               d.client_driver_client;
           rewrite (CR.connection_exactly d.client_driver_client st1) as
             (C.connection_exactly d.client_driver_client st1);
           if keys_installed {
             assert (pure (CS.application_record_keys_installed_for_role
               CS.ClientEndpoint
               st1.CS.cs_model));
             CSL.lemma_client_application_ready_stable_x25519_key_share_projection
               st1;
             assert (pure (client_driver_application_ready st1));
             Box.(d.client_driver_channel := Some ch);
             fold (client_driver_connected d st1 received sent);
             DriverWorkflowOk
           } else {
             fold (channel_open ch st1 buffered_after result.driver_workflow_rx_len);
             close_failed_connect d ch result.driver_workflow_rx_len;
             DriverWorkflowStepFailed
           }
         } else {
           fold (channel_open ch st1 buffered_after result.driver_workflow_rx_len);
           close_failed_connect d ch result.driver_workflow_rx_len;
           DriverWorkflowStepFailed
         }
       }
        DriverWorkflowNeedMoreInput -> {
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowNeedMoreInput
        }
        DriverWorkflowStepFailed -> {
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowStepFailed
        }
        DriverWorkflowExhausted -> {
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowExhausted
        }
        DriverWorkflowClosed -> {
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowClosed
        }
        DriverWorkflowPayloadTooLarge -> {
          (* Unreachable: the handshake workflow never produces this status,
             which is specific to [send]'s own payload-length gate. Handled
             here only so the match is total over [driver_workflow_status]. *)
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowPayloadTooLarge
        }
        DriverWorkflowOutputBufferTooSmall -> {
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowOutputBufferTooSmall
        }
      }
    }
  }
}
