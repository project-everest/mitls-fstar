module TLS13.Impl.Client.Driver.Close

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BN = TLS13.Impl.Client.Driver.BufferedNetwork
module BS = Common.BufferedStream
module BT = Common.BufferedTCP
module C = TLS13.Impl.Client
module CL = TLS13.ConnectionLog
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module DCleanup = TLS13.Impl.Client.Driver.Cleanup
module L = TLS13.Impl.Messages
module O = TLS13.OpenSSL
module Box = Pulse.Lib.Box
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module DS = TLS13.Impl.Client.Driver.State
module DC = TLS13.Impl.Client.Driver.Core

open TLS13.Impl.Client.Driver.State
open TLS13.Impl.Client.Driver.Core

noeq
type close_workflow_result = {
  close_workflow_status: driver_workflow_status;
  close_workflow_pending_len: SZ.t;
}

let lemma_control_snapshot_closed
  (snapshot:CR.control_snapshot)
  (st:CS.connection_state)
  : Lemma
      (requires
        CR.control_snapshot_matches snapshot st /\
        snapshot.CR.snapshot_control_tag == 4uy)
      (ensures st.CS.cs_model.CS.model_control == CS.ControlClosed)
=
  match st.CS.cs_model.CS.model_control with
  | CS.ControlNew
  | CS.ControlHandshaking _
  | CS.ControlApplicationData
  | CS.ControlClosing
  | CS.ControlFailed _ ->
    assert False
  | CS.ControlClosed ->
    ()

fn top_driver_send_close_notify
  (d:top_driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires
    top_driver_exactly d 'st0 'buffered 'pending_len **
    pts_to empty_payload 'empty_payload_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'empty_payload_bytes == 0 /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len)
  returns result:local_write_result
  ensures
    exists* st1 network_out_bytes app_out_bytes.
      top_driver_exactly d st1 'buffered 'pending_len **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len /\
        CT.local_event_end_to_end_correct
          'st0
          st1
          result.local_write_resp
          CT.LocalSendCloseNotify
          (Ghost.reveal 'empty_payload_bytes)
          network_out_bytes
          app_out_bytes /\
        st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config /\
        result.local_write_written ==
          result.local_write_resp.CT.network_out_len)
{
  assert (pure (CT.local_input_wf
    'st0
    CT.LocalSendCloseNotify
    (Ghost.reveal 'empty_payload_bytes)));
  rewrite
    (top_driver_exactly
      d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len))
    as
    (top_buffered_driver_exactly
      (top_driver_as_buffered d)
      'st0
      (Ghost.reveal 'buffered)
      (Ghost.reveal 'pending_len));
  let result =
    BN.process_local_event
      (top_driver_as_buffered d)
      CT.LocalSendCloseNotify
      empty_payload
      0sz
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (
      top_buffered_driver_exactly
        (top_driver_as_buffered d)
        st1
        (Ghost.reveal 'buffered)
        (Ghost.reveal 'pending_len) **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes);
  CT.lemma_local_event_end_to_end_correct_preserves_config
    'st0
    st1
    result.local_write_resp
    CT.LocalSendCloseNotify
    (Ghost.reveal 'empty_payload_bytes)
    network_out_bytes
    app_out_bytes;
  rewrite
    (top_buffered_driver_exactly
      (top_driver_as_buffered d)
      st1
      (Ghost.reveal 'buffered)
      (Ghost.reveal 'pending_len))
    as
    (top_driver_exactly
      d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  result
}

#push-options "--z3rlimit 20 --z3seed 17"
fn rec await_peer_close_notify
  (d:top_driver)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires
    top_driver_exactly d 'st0 'buffered buffered_len **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'buffered == SZ.v buffered_len /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len /\
      L.max_record_fragment_len <= SZ.v app_out_len)
  returns result:close_workflow_result
  ensures
    exists* st1 buffered_after network_out_bytes app_out_bytes.
      top_driver_exactly
        d st1 buffered_after result.close_workflow_pending_len **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length buffered_after ==
          SZ.v result.close_workflow_pending_len /\
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len /\
        st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config)
  decreases (SZ.v fuel)
{
  if (fuel = 0sz) {
    {
      close_workflow_status = DriverWorkflowExhausted;
      close_workflow_pending_len = buffered_len;
    }
  } else {
    unfold (top_driver_exactly d 'st0 'buffered buffered_len);
    let snapshot = driver_control_snapshot d.top_driver_core;
    assert (pure (CR.control_snapshot_matches snapshot 'st0));
    fold (top_driver_exactly d 'st0 'buffered buffered_len);
    let closed = snapshot.CR.snapshot_control_tag = 4uy;
    if closed {
      lemma_control_snapshot_closed snapshot 'st0;
      {
        close_workflow_status = DriverWorkflowClosed;
        close_workflow_pending_len = buffered_len;
      }
    } else {
      let network =
        driver_progress_buffered_network_step
          d
          buffered_len
          network_out
          network_out_len
          app_out
          app_out_len
          fuel;
      with st_network buffered_network network_out_network app_out_network.
        assert (
          top_driver_exactly
            d
            st_network
            buffered_network
            network.BN.completed_drive_pending_len **
          pts_to network_out network_out_network **
          pts_to app_out app_out_network);
      match network.BN.completed_drive_outcome {
        BS.DriveExhausted -> {
          let result = {
            close_workflow_status = DriverWorkflowExhausted;
            close_workflow_pending_len =
              network.BN.completed_drive_pending_len;
          };
          rewrite
            (top_driver_exactly
              d
              st_network
              buffered_network
              network.BN.completed_drive_pending_len)
            as
            (top_driver_exactly
              d
              st_network
              buffered_network
              result.close_workflow_pending_len);
          result
        }
        BS.DriveProgress _ _ _ -> {
          assert (pure False);
          {
            close_workflow_status = DriverWorkflowStepFailed;
            close_workflow_pending_len =
              network.BN.completed_drive_pending_len;
          }
        }
        BS.DriveBufferFull _ _ -> {
          assert (pure False);
          {
            close_workflow_status = DriverWorkflowStepFailed;
            close_workflow_pending_len =
              network.BN.completed_drive_pending_len;
          }
        }
        BS.DriveReject _ _ _ -> {
          let result = {
            close_workflow_status = DriverWorkflowStepFailed;
            close_workflow_pending_len =
              network.BN.completed_drive_pending_len;
          };
          rewrite
            (top_driver_exactly
              d
              st_network
              buffered_network
              network.BN.completed_drive_pending_len)
            as
            (top_driver_exactly
              d
              st_network
              buffered_network
              result.close_workflow_pending_len);
          result
        }
        BS.DriveYield _ _ _ _ -> {
          let next_fuel = SZ.sub fuel 1sz;
          assert (pure (SZ.v next_fuel < SZ.v fuel));
          await_peer_close_notify
            d
            network.BN.completed_drive_pending_len
            network_out
            network_out_len
            app_out
            app_out_len
            next_fuel
        }
      }
    }
  }
}
#pop-options

fn driver_close_workflow
  (d:top_driver)
  (wait_for_peer:bool)
  (empty_payload:array U8.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires
    top_driver_exactly d 'st0 'buffered buffered_len **
    pts_to empty_payload 'empty_payload_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'buffered == SZ.v buffered_len /\
      B.length 'empty_payload_bytes == 0 /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len /\
      L.max_record_fragment_len <= SZ.v app_out_len)
  returns result:close_workflow_result
  ensures
    exists* st1 buffered_after network_out_bytes app_out_bytes.
      top_driver_exactly
        d st1 buffered_after result.close_workflow_pending_len **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length buffered_after ==
          SZ.v result.close_workflow_pending_len /\
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len /\
        st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config /\
        (exists st_close_notify.
          client_driver_close_correct
            'st0
            st_close_notify
            result.close_workflow_status
            wait_for_peer))
{
  let close_result =
    top_driver_send_close_notify
      d
      empty_payload
      network_out
      network_out_len
      app_out
      app_out_len;
  with st_close network_out_close app_out_close.
    assert (
      top_driver_exactly d st_close 'buffered buffered_len **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to network_out network_out_close **
      pts_to app_out app_out_close);
  assert (pure (forall (i:nat{
      i < B.length (Ghost.reveal 'empty_payload_bytes)}).
    Seq.index (Ghost.reveal 'empty_payload_bytes) i ==
      Seq.index B.empty i));
  Seq.lemma_eq_intro (Ghost.reveal 'empty_payload_bytes) B.empty;
  Seq.lemma_eq_elim (Ghost.reveal 'empty_payload_bytes) B.empty;
  lemma_local_event_wire_lengths
    'st0
    st_close
    close_result.local_write_resp
    CT.LocalSendCloseNotify
    B.empty
    network_out_close
    app_out_close;
  assert (pure (client_driver_local_write_correct
    'st0
    st_close
    close_result.local_write_resp
    CT.LocalSendCloseNotify
    B.empty
    'st0.CS.cs_wire_log.CL.raw_sent
    st_close.CS.cs_wire_log.CL.raw_sent));
  let close_ok = close_result.local_write_resp.CT.status = CT.StepOk;
  if (close_ok = false) {
    let result = {
      close_workflow_status = DriverWorkflowStepFailed;
      close_workflow_pending_len = buffered_len;
    };
    assert (pure (client_driver_close_status_correct
      wait_for_peer
      result.close_workflow_status
      close_result.local_write_resp));
    assert (pure (client_driver_close_correct
      'st0
      st_close
      result.close_workflow_status
      wait_for_peer));
    rewrite
      (top_driver_exactly d st_close 'buffered buffered_len)
      as
      (top_driver_exactly
        d st_close 'buffered result.close_workflow_pending_len);
    result
  } else if (wait_for_peer = false) {
    let result = {
      close_workflow_status = DriverWorkflowClosed;
      close_workflow_pending_len = buffered_len;
    };
    assert (pure (client_driver_close_status_correct
      wait_for_peer
      result.close_workflow_status
      close_result.local_write_resp));
    assert (pure (client_driver_close_correct
      'st0
      st_close
      result.close_workflow_status
      wait_for_peer));
    rewrite
      (top_driver_exactly d st_close 'buffered buffered_len)
      as
      (top_driver_exactly
        d st_close 'buffered result.close_workflow_pending_len);
    result
  } else {
    let waited =
      await_peer_close_notify
        d
        buffered_len
        network_out
        network_out_len
        app_out
        app_out_len
        fuel;
    with st_wait buffered_wait network_out_wait app_out_wait.
      assert (
        top_driver_exactly
          d st_wait buffered_wait waited.close_workflow_pending_len **
        pts_to network_out network_out_wait **
        pts_to app_out app_out_wait);
    assert (pure (client_driver_close_status_correct
      wait_for_peer
      waited.close_workflow_status
      close_result.local_write_resp));
    assert (pure (client_driver_close_correct
      'st0
      st_close
      waited.close_workflow_status
      wait_for_peer));
    waited
  }
}

fn abort
  (d:client_driver)
  requires client_driver_connected d 'st0 'received0 'sent0
  ensures client_driver_closed d 'st0
{
  DCleanup.close_connected_client_driver d
}

fn run
  (d:client_driver)
  (wait_for_peer:bool)
  (fuel:SZ.t)
  requires client_driver_connected d 'st0 'received0 'sent0
  returns status:driver_workflow_status
  ensures
    exists* st1.
      client_driver_closed d st1 **
      pure (
        st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config /\
        client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0) /\
        client_driver_received_log_accounted
          'st0 (Ghost.reveal 'received0) /\
        (exists st_close_notify.
          client_driver_close_correct
            'st0
            st_close_notify
            status
            wait_for_peer))
{
  unfold (client_driver_connected
    d 'st0 (Ghost.reveal 'received0) (Ghost.reveal 'sent0));
  with channel model committed buffered_len.
    unfold (client_driver_connected_indexed
      d
      'st0
      (Ghost.reveal 'received0)
      (Ghost.reveal 'sent0)
      channel
      model
      committed
      buffered_len);
  unfold (buffered_driver_indexed
    (client_buffered_driver d channel)
    'st0
    (BT.pending model)
    buffered_len
    model
    (Ghost.reveal 'received0)
    committed
    (Ghost.reveal 'sent0));
  assert (pure (client_driver_sent_log_exact
    'st0 (Ghost.reveal 'sent0)));
  assert (pure (client_driver_wire_logs_match
    'st0
    (Ghost.reveal 'received0)
    (Ghost.reveal 'sent0)
    (BT.pending model)
    buffered_len));
  lemma_client_driver_wire_logs_match_received_accounted
    'st0
    (Ghost.reveal 'received0)
    (Ghost.reveal 'sent0)
    (BT.pending model)
    buffered_len;
  fold (buffered_driver_indexed
    (client_buffered_driver d channel)
    'st0
    (BT.pending model)
    buffered_len
    model
    (Ghost.reveal 'received0)
    committed
    (Ghost.reveal 'sent0));
  let current_channel = Box.(!d.client_driver_channel);
  assert (pure (current_channel == Some channel));
  assert (pure (Some? current_channel));
  let concrete_channel = Some?.v current_channel;
  assert (pure (concrete_channel == channel));
  rewrite
    (buffered_driver_indexed
      (client_buffered_driver d channel)
      'st0
      (BT.pending model)
      buffered_len
      model
      (Ghost.reveal 'received0)
      committed
      (Ghost.reveal 'sent0))
    as
    (buffered_driver_indexed
      (client_buffered_driver d concrete_channel)
      'st0
      (BT.pending model)
      buffered_len
      model
      (Ghost.reveal 'received0)
      committed
      (Ghost.reveal 'sent0));
  unfold (buffered_driver_indexed
    (client_buffered_driver d concrete_channel)
    'st0
    (BT.pending model)
    buffered_len
    model
    (Ghost.reveal 'received0)
    committed
    (Ghost.reveal 'sent0));
  let concrete_buffered_len = BT.pending_length concrete_channel;
  assert (pure (
    SZ.v concrete_buffered_len == B.length (BT.pending model)));
  fold (buffered_driver_indexed
    (client_buffered_driver d concrete_channel)
    'st0
    (BT.pending model)
    concrete_buffered_len
    model
    (Ghost.reveal 'received0)
    committed
    (Ghost.reveal 'sent0));
  unfold (client_driver_buffers d);
  with empty_payload network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out local_app_out.
    assert (
      V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.client_driver_network_out #1.0R network_out **
      V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
      V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
      V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
      V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
      V.pts_to d.client_driver_app_out #1.0R app_out **
      V.pts_to d.client_driver_local_app_out #1.0R local_app_out);
  V.to_array_pts_to d.client_driver_empty_payload;
  V.to_array_pts_to d.client_driver_network_out;
  V.to_array_pts_to d.client_driver_app_out;
  let core = {
    driver_client = d.client_driver_client;
    driver_channel = concrete_channel;
    driver_storage = d.client_driver_storage;
    driver_tcp_history = d.client_driver_tcp_history;
    driver_progress = d.client_driver_progress;
    driver_initial = d.client_driver_initial;
  };
  let td = {
    top_driver_core = core;
    top_driver_auth = d.client_driver_auth;
  };
  fold (buffered_driver_exactly
    (client_buffered_driver d concrete_channel)
    'st0
    (BT.pending model)
    concrete_buffered_len);
  rewrite
    (buffered_driver_exactly
      (client_buffered_driver d concrete_channel)
      'st0
      (BT.pending model)
      concrete_buffered_len)
    as
    (buffered_driver_exactly
      (driver_as_buffered td.top_driver_core)
      'st0
      (BT.pending model)
      concrete_buffered_len);
  fold (driver_exactly
    td.top_driver_core
    'st0
    (BT.pending model)
    concrete_buffered_len);
  rewrite
    (O.is_auth_context d.client_driver_auth)
    as
    (O.is_auth_context td.top_driver_auth);
  fold (top_driver_exactly
    td
    'st0
    (BT.pending model)
    concrete_buffered_len);
  let workflow =
    driver_close_workflow
      td
      wait_for_peer
      (V.vec_to_array d.client_driver_empty_payload)
      concrete_buffered_len
      (V.vec_to_array d.client_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.client_driver_app_out)
      driver_app_out_capacity
      fuel;
  with st1 buffered_after network_out_bytes app_out_bytes.
    assert (
      top_driver_exactly
        td st1 buffered_after workflow.close_workflow_pending_len **
      pts_to
        (V.vec_to_array d.client_driver_empty_payload)
        empty_payload **
      pts_to
        (V.vec_to_array d.client_driver_network_out)
        network_out_bytes **
      pts_to
        (V.vec_to_array d.client_driver_app_out)
        app_out_bytes);
  V.to_vec_pts_to d.client_driver_empty_payload;
  V.to_vec_pts_to d.client_driver_network_out;
  V.to_vec_pts_to d.client_driver_app_out;
  unfold (top_driver_exactly
    td st1 buffered_after workflow.close_workflow_pending_len);
  unfold (driver_exactly
    td.top_driver_core
    st1
    buffered_after
    workflow.close_workflow_pending_len);
  rewrite
    (buffered_driver_exactly
      (driver_as_buffered td.top_driver_core)
      st1
      buffered_after
      workflow.close_workflow_pending_len)
    as
    (buffered_driver_exactly
      (client_buffered_driver d concrete_channel)
      st1
      buffered_after
      workflow.close_workflow_pending_len);
  unfold (buffered_driver_exactly
    (client_buffered_driver d concrete_channel)
    st1
    buffered_after
    workflow.close_workflow_pending_len);
  with model1 received1 committed1 sent1.
    assert (buffered_driver_indexed
      (client_buffered_driver d concrete_channel)
      st1
      buffered_after
      workflow.close_workflow_pending_len
      model1
      received1
      committed1
      sent1);
  unfold (buffered_driver_indexed
    (client_buffered_driver d concrete_channel)
    st1
    buffered_after
    workflow.close_workflow_pending_len
    model1
    received1
    committed1
    sent1);
  assert (pure (Seq.equal (BT.pending model1) buffered_after));
  Seq.lemma_eq_elim (BT.pending model1) buffered_after;
  fold (buffered_driver_indexed
    (client_buffered_driver d concrete_channel)
    st1
    (BT.pending model1)
    workflow.close_workflow_pending_len
    model1
    received1
    committed1
    sent1);
  rewrite
    (O.is_auth_context td.top_driver_auth)
    as
    (O.is_auth_context d.client_driver_auth);
  fold (client_driver_buffers d);
  fold (client_driver_connected_indexed
    d
    st1
    received1
    sent1
    concrete_channel
    model1
    committed1
    workflow.close_workflow_pending_len);
  fold (client_driver_connected d st1 received1 sent1);
  abort d;
  workflow.close_workflow_status
}
