module TLS13.Impl.Client.Driver.Send

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
open TLS13.Impl.Client.Driver.State
open TLS13.Impl.Client.Driver.Core
fn send_application_data_once
  (c:C.client)
  (ch:IO.channel)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           channel_open ch 'st0 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           C.connection_exactly c st1 **
           channel_open ch st1 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                   'st0
                   st1
                   result.local_write_resp
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes)
                   network_out_bytes
                   app_out_bytes /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 result.local_write_written ==
                   result.local_write_resp.CT.network_out_len /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                  SZ.v result.local_write_written <=
                  SZ.v result.local_write_resp.CT.network_out_len))
{
  process_local_event_and_write_once
    c
    ch
    CT.LocalSendApplicationData
    payload
    payload_len
    network_out
    network_out_len
    app_out
    app_out_len
}

fn driver_send_application_data
  (d:driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                   'st0
                   st1
                   result.local_write_resp
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes)
                   network_out_bytes
                   app_out_bytes /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 result.local_write_written ==
                   result.local_write_resp.CT.network_out_len /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                 SZ.v result.local_write_written <=
                 SZ.v result.local_write_resp.CT.network_out_len))
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  unfold (driver_canonical_progress d 'st0);
  let result =
    send_application_data_once
      d.driver_client
      d.driver_channel
      payload
      payload_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (C.connection_exactly d.driver_client st1 **
            channel_open d.driver_channel st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
            pts_to payload 'payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  CT.lemma_local_event_end_to_end_correct_preserves_config
    'st0
    st1
    result.local_write_resp
    CT.LocalSendApplicationData
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  CP.lemma_client_local_progress
    'st0
    st1
    {
      CTypes.client_local_kind = CT.LocalSendApplicationData;
      CTypes.client_local_payload = Ghost.reveal 'payload_bytes;
    }
    result.local_write_resp
    network_out_bytes
    app_out_bytes;
  MR.update d.driver_progress st1;
  assert (pure (CT.client_end_to_end_invariant st1));
  fold (driver_canonical_progress d st1);
  fold (driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  result
}

fn top_driver_send_application_data
  (d:top_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires top_driver_exactly d 'st0 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                  'st0
                  CT.LocalSendApplicationData
                  (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           top_driver_exactly d st1 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                  'st0
                  st1
                  result.local_write_resp
                  CT.LocalSendApplicationData
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 result.local_write_written ==
                   result.local_write_resp.CT.network_out_len /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                 SZ.v result.local_write_written <=
                 SZ.v result.local_write_resp.CT.network_out_len))
{
  unfold (top_driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  let result =
    driver_send_application_data
      d.top_driver_core
      payload
      payload_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (driver_exactly d.top_driver_core st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
            pts_to payload 'payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  result
}

fn run
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
                 client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0) /\
                 client_driver_sent_log_exact st1 sent1 /\
                 client_driver_received_log_accounted st1 received1)
{
  unfold (client_driver_connected d 'st0 (Ghost.reveal 'received0) (Ghost.reveal 'sent0));
  with ch buffered buffered_len.
    assert (C.connection_exactly d.client_driver_client 'st0 **
            O.is_auth_context d.client_driver_auth **
            Box.pts_to d.client_driver_channel (Some ch) **
            IO.is_channel ch (Ghost.reveal 'received0) (Ghost.reveal 'sent0) **
            client_driver_buffers d buffered buffered_len **
            pure (client_driver_wire_logs_match
                    'st0
                    (Ghost.reveal 'received0)
                    (Ghost.reveal 'sent0)
                    buffered
                    buffered_len));
  assert (pure (client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0)));
  lemma_client_driver_wire_logs_match_received_accounted
    'st0
    (Ghost.reveal 'received0)
    (Ghost.reveal 'sent0)
    buffered
    buffered_len;
  assert (pure (client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0)));
  let current_channel = Box.(!d.client_driver_channel);
  assert (pure (current_channel == Some ch));
  unfold (client_driver_buffers d buffered buffered_len);
  let current_buffered_len = Box.(!d.client_driver_buffered_len);
  assert (pure (current_buffered_len == buffered_len));
  assert_norm (SM.max_application_data_fragment_len == 16384);
  let too_large = SZ.gt payload_len 16384sz;
  if too_large {
    (* TLS 1.3 caps a single application-data record's plaintext at 16384
       bytes.  Reject the oversized payload up front, authoritatively, and
       leave the connection exactly as it was so the caller may retry with a
       smaller chunk. *)
    assert (pure (SZ.v payload_len > SM.max_application_data_fragment_len));
    assert (pure (B.length (Ghost.reveal 'payload_bytes) > SM.max_application_data_fragment_len));
    assert (pure (client_driver_payload_too_large (Ghost.reveal 'payload_bytes)));
    assert (pure (client_driver_send_correct
      'st0
      'st0
      DriverWorkflowPayloadTooLarge
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal 'sent0)
      (Ghost.reveal 'sent0)));
    fold (client_driver_buffers d buffered current_buffered_len);
    fold (client_driver_connected d 'st0 (Ghost.reveal 'received0) (Ghost.reveal 'sent0));
    DriverWorkflowPayloadTooLarge
  } else {
    assert (pure (SZ.v payload_len <= SM.max_application_data_fragment_len));
    assert (pure (CT.local_input_wf
      'st0
      CT.LocalSendApplicationData
      (Ghost.reveal 'payload_bytes)));
  match current_channel {
    None -> {
      assert (pure False);
      fold (client_driver_buffers d buffered current_buffered_len);
      fold (client_driver_connected d 'st0 (Ghost.reveal 'received0) (Ghost.reveal 'sent0));
      DriverWorkflowStepFailed
    }
    Some concrete_ch -> {
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
      V.to_array_pts_to d.client_driver_network_out;
      V.to_array_pts_to d.client_driver_app_out;
      let core = {
        driver_client = d.client_driver_client;
        driver_channel = concrete_ch;
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
      assert (pure (concrete_ch == ch));
      assert (pure (client_driver_wire_logs_match
        'st0
        (Ghost.reveal 'received0)
        (Ghost.reveal 'sent0)
        buffered
        current_buffered_len));
      fold (channel_open ch 'st0 buffered current_buffered_len);
      rewrite (channel_open ch 'st0 buffered current_buffered_len) as
        (channel_open core.driver_channel 'st0 buffered current_buffered_len);
      fold (driver_exactly core 'st0 buffered current_buffered_len);
      rewrite (driver_exactly core 'st0 buffered current_buffered_len) as
        (driver_exactly td.top_driver_core 'st0 buffered current_buffered_len);
      rewrite (O.is_auth_context d.client_driver_auth) as (O.is_auth_context td.top_driver_auth);
      fold (top_driver_exactly td 'st0 buffered current_buffered_len);
      let result =
        top_driver_send_application_data
          td
          payload
          payload_len
          (V.vec_to_array d.client_driver_network_out)
          driver_network_out_capacity
          (V.vec_to_array d.client_driver_app_out)
          driver_app_out_capacity;
      with st1 network_out_bytes app_out_bytes.
        assert (top_driver_exactly td st1 buffered current_buffered_len **
                pts_to payload 'payload_bytes **
                pts_to (V.vec_to_array d.client_driver_network_out) network_out_bytes **
                pts_to (V.vec_to_array d.client_driver_app_out) app_out_bytes);
      assert (pure (st1.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      unfold (top_driver_exactly td st1 buffered current_buffered_len);
      rewrite (driver_exactly td.top_driver_core st1 buffered current_buffered_len) as
        (driver_exactly core st1 buffered current_buffered_len);
      unfold (driver_exactly core st1 buffered current_buffered_len);
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
      V.to_vec_pts_to d.client_driver_network_out;
      V.to_vec_pts_to d.client_driver_app_out;
      rewrite (C.connection_exactly core.driver_client st1) as
        (C.connection_exactly d.client_driver_client st1);
      rewrite (channel_open core.driver_channel st1 buffered current_buffered_len) as
        (channel_open ch st1 buffered current_buffered_len);
      rewrite (O.is_auth_context td.top_driver_auth) as
        (O.is_auth_context d.client_driver_auth);
      fold (client_driver_buffers d buffered current_buffered_len);
      unfold (channel_open ch st1 buffered current_buffered_len);
      with received1 sent1.
        assert (IO.is_channel ch received1 sent1 **
                pure (client_driver_wire_logs_match st1 received1 sent1 buffered current_buffered_len));
      lemma_local_event_wire_lengths
        'st0
        st1
        result.local_write_resp
        CT.LocalSendApplicationData
        (Ghost.reveal 'payload_bytes)
        network_out_bytes
        app_out_bytes;
      assert (pure (Seq.equal
        (Ghost.reveal 'sent0)
        'st0.CS.cs_wire_log.CL.raw_sent));
      assert (pure (Seq.equal sent1 st1.CS.cs_wire_log.CL.raw_sent));
      assert (pure (client_driver_sent_log_exact st1 sent1));
      lemma_client_driver_wire_logs_match_received_accounted
        st1
        received1
        sent1
        buffered
        current_buffered_len;
      assert (pure (client_driver_received_log_accounted st1 received1));
      assert (pure (Seq.equal
        st1.CS.cs_wire_log.CL.raw_sent
        (B.append
          'st0.CS.cs_wire_log.CL.raw_sent
          (CT.response_network_out result.local_write_resp network_out_bytes))));
      Seq.lemma_eq_elim
        (Ghost.reveal 'sent0)
        'st0.CS.cs_wire_log.CL.raw_sent;
      Seq.lemma_eq_elim
        sent1
        st1.CS.cs_wire_log.CL.raw_sent;
      assert (pure (Seq.equal
        sent1
        (B.append
          (Ghost.reveal 'sent0)
          (CT.response_network_out result.local_write_resp network_out_bytes))));
      assert (pure (client_driver_local_write_correct
        'st0
        st1
        result.local_write_resp
        CT.LocalSendApplicationData
        (Ghost.reveal 'payload_bytes)
        (Ghost.reveal 'sent0)
        sent1));
      assert (pure (result.local_write_written ==
        result.local_write_resp.CT.network_out_len));
      fold (client_driver_connected d st1 received1 sent1);
      let ok = result.local_write_resp.CT.status = CT.StepOk;
      let wrote_all = result.local_write_written = result.local_write_resp.CT.network_out_len;
      assert (pure (wrote_all == true));
      if (ok && wrote_all) {
        assert (pure (ok == true));
        assert (pure (result.local_write_resp.CT.status == CT.StepOk));
        assert (pure (client_driver_send_status_correct
          DriverWorkflowOk
          result.local_write_resp));
        assert (pure (client_driver_send_correct
          'st0
          st1
          DriverWorkflowOk
          (Ghost.reveal 'payload_bytes)
          (Ghost.reveal 'sent0)
          sent1));
        DriverWorkflowOk
      } else {
        assert (pure (ok == false));
        assert (pure (not (result.local_write_resp.CT.status == CT.StepOk)));
        assert (pure (client_driver_send_status_correct
          DriverWorkflowStepFailed
          result.local_write_resp));
        assert (pure (client_driver_send_correct
          'st0
          st1
          DriverWorkflowStepFailed
          (Ghost.reveal 'payload_bytes)
          (Ghost.reveal 'sent0)
          sent1));
        DriverWorkflowStepFailed
      }
    }
  }
  }
}
