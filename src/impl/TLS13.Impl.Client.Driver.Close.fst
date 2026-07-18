module TLS13.Impl.Client.Driver.Close

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
fn rec driver_await_peer_close_notify
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires driver_exactly d 'st0 'buffered buffered_len **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'buffered == SZ.v buffered_len /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: driver_workflow_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 buffered_after result.driver_workflow_rx_len **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity /\
                 B.length buffered_after == SZ.v result.driver_workflow_rx_len /\
                 Seq.equal buffered_after
                   (Seq.slice raw_bytes 0 (SZ.v result.driver_workflow_rx_len)) /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config)
  decreases (SZ.v fuel)
{
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let no_op_buffer_resp = {
    CT.response = no_op_resp;
    CT.consumed_len = 0sz;
  };
  let no_op_read = {
    network_read_len = 0sz;
    network_read_buffer_resp = no_op_buffer_resp;
    network_read_written = 0sz;
    network_read_prefix = Ghost.hide B.empty;
  };
  let no_op_buffered = {
    buffered_network_read = no_op_read;
    buffered_network_new_len = buffered_len;
  };
  let no_op_io = {
    buffered_network_io_read_len = 0sz;
    buffered_network_io_buffered = no_op_buffered;
  };
  let no_op_action = {
    CT.next_local_ready = false;
    CT.next_local_kind = CT.LocalFail;
    CT.next_local_payload = CT.LocalPayloadNone;
  };
  let no_op_local = {
    ready_local_action = no_op_action;
    ready_local_processed = false;
    ready_local_resp = no_op_resp;
    ready_local_written = 0sz;
  };
  if (fuel = 0sz) {
    {
      driver_workflow_status = DriverWorkflowExhausted;
      driver_workflow_rx_len = buffered_len;
      driver_workflow_local = {
        driver_drain_last = no_op_local;
        driver_drain_exhausted = false;
      };
      driver_workflow_network = no_op_io;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    let snapshot = driver_control_snapshot d;
    with st_snapshot.
      assert (driver_exactly d st_snapshot 'buffered buffered_len);
    assert (pure (st_snapshot.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    let closed = snapshot.CR.snapshot_control_tag = 4uy;
    if closed {
      {
        driver_workflow_status = DriverWorkflowOk;
        driver_workflow_rx_len = buffered_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = no_op_io;
      }
    } else {
      let network =
        driver_progress_buffered_network_step
          d
          raw
          raw_capacity
          buffered_len
          network_out
          network_out_len
          app_out
          app_out_len;
      with st_network buffered_network raw_network network_out_network app_out_network.
        assert (driver_exactly d st_network
                  buffered_network
                  network.buffered_network_io_buffered.buffered_network_new_len **
                pts_to raw raw_network **
                pts_to network_out network_out_network **
                pts_to app_out app_out_network);
      assert (pure (st_network.CS.cs_model.CS.model_config ==
        st_snapshot.CS.cs_model.CS.model_config));
      assert (pure (st_network.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      let net_read =
        network.buffered_network_io_buffered.buffered_network_read;
      let net_resp = net_read.network_read_buffer_resp.CT.response;
      let net_ok = net_resp.CT.status = CT.StepOk;
      let net_need_more = net_resp.CT.status = CT.NeedMoreInput;
      let net_bad_status = (net_ok || net_need_more) = false;
      let net_wrote_all =
        net_read.network_read_written = net_resp.CT.network_out_len;
      let net_short_write = net_ok && (net_wrote_all = false);
      let net_failed = net_bad_status || net_short_write;
      if net_failed {
        let result = {
          driver_workflow_status = DriverWorkflowStepFailed;
          driver_workflow_rx_len =
            network.buffered_network_io_buffered.buffered_network_new_len;
          driver_workflow_local = {
            driver_drain_last = no_op_local;
            driver_drain_exhausted = false;
          };
          driver_workflow_network = network;
        };
        assert (pure (result.driver_workflow_rx_len ==
          network.buffered_network_io_buffered.buffered_network_new_len));
        assert (pure (B.length raw_network == SZ.v raw_capacity));
        assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity));
        assert (pure (B.length buffered_network == SZ.v result.driver_workflow_rx_len));
        assert (pure (Seq.equal buffered_network
          (Seq.slice raw_network 0 (SZ.v result.driver_workflow_rx_len))));
        assert (pure (B.length network_out_network == SZ.v network_out_len));
        assert (pure (B.length app_out_network == SZ.v app_out_len));
        rewrite (driver_exactly
          d
          st_network
          buffered_network
          network.buffered_network_io_buffered.buffered_network_new_len) as
          (driver_exactly
            d
            st_network
            buffered_network
            result.driver_workflow_rx_len);
        result
      } else {
        assert (pure (0 < SZ.v fuel));
        let next_fuel = SZ.sub fuel 1sz;
        assert (pure (SZ.v next_fuel < SZ.v fuel));
        let next_buffered_len =
          network.buffered_network_io_buffered.buffered_network_new_len;
        assert (pure (B.length raw_network == SZ.v raw_capacity));
        assert (pure (SZ.v next_buffered_len <= SZ.v raw_capacity));
        assert (pure (B.length buffered_network == SZ.v next_buffered_len));
        assert (pure (Seq.equal buffered_network
          (Seq.slice raw_network 0 (SZ.v next_buffered_len))));
        assert (pure (B.length network_out_network == SZ.v network_out_len));
        assert (pure (B.length app_out_network == SZ.v app_out_len));
        assert (pure (L.max_record_fragment_len <= SZ.v app_out_len));
        rewrite (driver_exactly
          d
          st_network
          buffered_network
          network.buffered_network_io_buffered.buffered_network_new_len) as
          (driver_exactly
            d
            st_network
            buffered_network
            next_buffered_len);
        driver_await_peer_close_notify
          d
          raw
          raw_capacity
          next_buffered_len
          network_out
          network_out_len
          app_out
          app_out_len
          next_fuel
      }
    }
  }
}

fn driver_send_close_notify
  (d:driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
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
                   result.local_write_resp.CT.network_out_len /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                  SZ.v result.local_write_written <=
                  SZ.v result.local_write_resp.CT.network_out_len))
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  assert (pure (CT.local_input_wf
    'st0
    CT.LocalSendCloseNotify
    (Ghost.reveal 'empty_payload_bytes)));
  let result =
    process_local_event_and_write_once
      d.driver_client
      d.driver_channel
      CT.LocalSendCloseNotify
      empty_payload
      0sz
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (C.connection_exactly d.driver_client st1 **
            channel_open d.driver_channel st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
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
  fold (driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  result
}

fn rec driver_close_workflow
  (d:top_driver)
  (wait_for_peer:bool)
  (empty_payload:array U8.t)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires top_driver_exactly d 'st0 'buffered buffered_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'buffered == SZ.v buffered_len /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: driver_workflow_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           C.connection_exactly d.top_driver_core.driver_client st1 **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (exists st_close_notify.
                   client_driver_close_correct
                     'st0
                     st_close_notify
                     result.driver_workflow_status
                     wait_for_peer))
  decreases (SZ.v fuel)
{
  unfold (top_driver_exactly d 'st0 'buffered buffered_len);
  let close_result =
    driver_send_close_notify
      d.top_driver_core
      empty_payload
      network_out
      network_out_len
      app_out
      app_out_len;
  with st_after_close_notify network_out_after_close app_out_after_close.
    assert (driver_exactly d.top_driver_core st_after_close_notify 'buffered buffered_len **
            pts_to empty_payload 'empty_payload_bytes **
            pts_to network_out network_out_after_close **
            pts_to app_out app_out_after_close);
  assert (pure (st_after_close_notify.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure (forall (i:nat{i < B.length (Ghost.reveal 'empty_payload_bytes)}).
    Seq.index (Ghost.reveal 'empty_payload_bytes) i == Seq.index B.empty i));
  Seq.lemma_eq_intro (Ghost.reveal 'empty_payload_bytes) B.empty;
  Seq.lemma_eq_elim (Ghost.reveal 'empty_payload_bytes) B.empty;
  lemma_local_event_wire_lengths
    'st0
    st_after_close_notify
    close_result.local_write_resp
    CT.LocalSendCloseNotify
    B.empty
    network_out_after_close
    app_out_after_close;
  assert (pure (Seq.equal
    st_after_close_notify.CS.cs_wire_log.CL.raw_sent
    (B.append
      'st0.CS.cs_wire_log.CL.raw_sent
      (CT.response_network_out close_result.local_write_resp network_out_after_close))));
  assert (pure (client_driver_local_write_correct
    'st0
    st_after_close_notify
    close_result.local_write_resp
    CT.LocalSendCloseNotify
    B.empty
    'st0.CS.cs_wire_log.CL.raw_sent
    st_after_close_notify.CS.cs_wire_log.CL.raw_sent));
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let no_op_buffer_resp = {
    CT.response = no_op_resp;
    CT.consumed_len = 0sz;
  };
  let no_op_read = {
    network_read_len = 0sz;
    network_read_buffer_resp = no_op_buffer_resp;
    network_read_written = 0sz;
    network_read_prefix = Ghost.hide B.empty;
  };
  let no_op_buffered = {
    buffered_network_read = no_op_read;
    buffered_network_new_len = buffered_len;
  };
  let no_op_io = {
    buffered_network_io_read_len = 0sz;
    buffered_network_io_buffered = no_op_buffered;
  };
  let no_op_action = {
    CT.next_local_ready = false;
    CT.next_local_kind = CT.LocalFail;
    CT.next_local_payload = CT.LocalPayloadNone;
  };
  let no_op_local = {
    ready_local_action = no_op_action;
    ready_local_processed = false;
    ready_local_resp = close_result.local_write_resp;
    ready_local_written = close_result.local_write_written;
  };
  let close_ok = close_result.local_write_resp.CT.status = CT.StepOk;
  let close_wrote_all =
    close_result.local_write_written = close_result.local_write_resp.CT.network_out_len;
  assert (pure (close_wrote_all == true));
  let close_failed = (close_ok && close_wrote_all) = false;
  if close_failed {
   assert (pure (close_ok == false));
   assert (pure (close_result.local_write_resp.CT.status <> CT.StepOk));
   assert (pure (client_driver_close_status_correct
     wait_for_peer
     DriverWorkflowStepFailed
     close_result.local_write_resp));
   assert (pure (client_driver_close_correct
     'st0
     st_after_close_notify
     DriverWorkflowStepFailed
     wait_for_peer));
   assert (pure (exists st_close_notify.
     client_driver_close_correct
       'st0
       st_close_notify
       DriverWorkflowStepFailed
       wait_for_peer));
   unfold (driver_exactly d.top_driver_core st_after_close_notify 'buffered buffered_len);
   unfold (channel_open d.top_driver_core.driver_channel st_after_close_notify 'buffered buffered_len);
   with received sent.
     assert (IO.is_channel d.top_driver_core.driver_channel received sent **
             pure (client_driver_wire_logs_match st_after_close_notify received sent 'buffered buffered_len));
    IO.close d.top_driver_core.driver_channel;
    O.auth_context_free d.top_driver_auth;
    {
      driver_workflow_status = DriverWorkflowStepFailed;
      driver_workflow_rx_len = buffered_len;
      driver_workflow_local = {
        driver_drain_last = no_op_local;
        driver_drain_exhausted = false;
      };
      driver_workflow_network = no_op_io;
    }
  } else if wait_for_peer {
    let waited =
      driver_await_peer_close_notify
        d.top_driver_core
        raw
        raw_capacity
        buffered_len
        network_out
        network_out_len
        app_out
        app_out_len
        fuel;
    with st_wait buffered_wait raw_wait network_out_wait app_out_wait.
      assert (driver_exactly d.top_driver_core st_wait buffered_wait waited.driver_workflow_rx_len **
              pts_to raw raw_wait **
              pts_to network_out network_out_wait **
              pts_to app_out app_out_wait);
    assert (pure (st_wait.CS.cs_model.CS.model_config ==
      st_after_close_notify.CS.cs_model.CS.model_config));
    assert (pure (st_wait.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    unfold (driver_exactly d.top_driver_core st_wait buffered_wait waited.driver_workflow_rx_len);
    unfold (channel_open d.top_driver_core.driver_channel st_wait buffered_wait waited.driver_workflow_rx_len);
    with received sent.
     assert (IO.is_channel d.top_driver_core.driver_channel received sent **
             pure (client_driver_wire_logs_match st_wait received sent buffered_wait waited.driver_workflow_rx_len));
    IO.close d.top_driver_core.driver_channel;
    O.auth_context_free d.top_driver_auth;
    let wait_ok = waited.driver_workflow_status = DriverWorkflowOk;
    if wait_ok {
      assert (pure (close_ok == true));
      assert (pure (client_driver_close_status_correct
        wait_for_peer
        DriverWorkflowClosed
        close_result.local_write_resp));
      assert (pure (client_driver_close_correct
        'st0
        st_after_close_notify
        DriverWorkflowClosed
        wait_for_peer));
      assert (pure (exists st_close_notify.
        client_driver_close_correct
          'st0
          st_close_notify
          DriverWorkflowClosed
          wait_for_peer));
      {
        driver_workflow_status = DriverWorkflowClosed;
        driver_workflow_rx_len = waited.driver_workflow_rx_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = waited.driver_workflow_network;
      }
    } else {
      assert (pure (close_ok == true));
      assert (pure (client_driver_close_status_correct
        wait_for_peer
        waited.driver_workflow_status
        close_result.local_write_resp));
      assert (pure (client_driver_close_correct
        'st0
        st_after_close_notify
        waited.driver_workflow_status
        wait_for_peer));
      assert (pure (exists st_close_notify.
        client_driver_close_correct
          'st0
          st_close_notify
          waited.driver_workflow_status
          wait_for_peer));
      {
        driver_workflow_status = waited.driver_workflow_status;
        driver_workflow_rx_len = waited.driver_workflow_rx_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = waited.driver_workflow_network;
      }
    }
  } else {
   unfold (driver_exactly d.top_driver_core st_after_close_notify 'buffered buffered_len);
   unfold (channel_open d.top_driver_core.driver_channel st_after_close_notify 'buffered buffered_len);
   with received sent.
     assert (IO.is_channel d.top_driver_core.driver_channel received sent **
             pure (client_driver_wire_logs_match st_after_close_notify received sent 'buffered buffered_len));
    IO.close d.top_driver_core.driver_channel;
    O.auth_context_free d.top_driver_auth;
   assert (pure (wait_for_peer == false));
   assert (pure (close_ok == true));
   assert (pure (client_driver_close_status_correct
     wait_for_peer
     DriverWorkflowClosed
     close_result.local_write_resp));
   assert (pure (client_driver_close_correct
     'st0
     st_after_close_notify
     DriverWorkflowClosed
     wait_for_peer));
   assert (pure (exists st_close_notify.
     client_driver_close_correct
       'st0
       st_close_notify
       DriverWorkflowClosed
       wait_for_peer));
   {
     driver_workflow_status = DriverWorkflowClosed;
     driver_workflow_rx_len = buffered_len;
     driver_workflow_local = {
        driver_drain_last = no_op_local;
        driver_drain_exhausted = false;
      };
      driver_workflow_network = no_op_io;
    }
  }
}


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
                client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0) /\
                (exists st_close_notify.
            client_driver_close_correct
              'st0
              st_close_notify
              status
              wait_for_peer))
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
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (concrete_ch == ch));
  unfold (client_driver_buffers d buffered buffered_len);
  let current_buffered_len = Box.(!d.client_driver_buffered_len);
  assert (pure (current_buffered_len == buffered_len));
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
  V.to_array_pts_to d.client_driver_app_out;
  let core = {
    driver_client = d.client_driver_client;
    driver_channel = concrete_ch;
  };
  let td = {
    top_driver_core = core;
    top_driver_auth = d.client_driver_auth;
  };
  rewrite (C.connection_exactly d.client_driver_client 'st0) as
    (C.connection_exactly core.driver_client 'st0);
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
  let workflow =
    driver_close_workflow
      td
      wait_for_peer
      (V.vec_to_array d.client_driver_empty_payload)
      (V.vec_to_array d.client_driver_raw)
      driver_rx_capacity
      current_buffered_len
      (V.vec_to_array d.client_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.client_driver_app_out)
      driver_app_out_capacity
      fuel;
  with st1 raw_bytes network_out_bytes app_out_bytes.
    assert (C.connection_exactly td.top_driver_core.driver_client st1 **
            pts_to (V.vec_to_array d.client_driver_empty_payload) empty_payload **
            pts_to (V.vec_to_array d.client_driver_raw) raw_bytes **
            pts_to (V.vec_to_array d.client_driver_network_out) network_out_bytes **
            pts_to (V.vec_to_array d.client_driver_app_out) app_out_bytes);
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  rewrite (C.connection_exactly td.top_driver_core.driver_client st1) as
    (C.connection_exactly d.client_driver_client st1);
  V.to_vec_pts_to d.client_driver_empty_payload;
  V.to_vec_pts_to d.client_driver_raw;
  V.to_vec_pts_to d.client_driver_network_out;
  V.to_vec_pts_to d.client_driver_app_out;
  Box.(d.client_driver_channel := no_channel);
  Box.free d.client_driver_channel;
  Box.(d.client_driver_buffered_len := workflow.driver_workflow_rx_len);
  assert (pure (SZ.v workflow.driver_workflow_rx_len <= SZ.v driver_rx_capacity));
  let close_buffered =
    Ghost.hide (Seq.slice raw_bytes 0 (SZ.v workflow.driver_workflow_rx_len));
  Seq.lemma_len_slice raw_bytes 0 (SZ.v workflow.driver_workflow_rx_len);
  fold (client_driver_buffers d (Ghost.reveal close_buffered) workflow.driver_workflow_rx_len);
  free_client_driver_buffers d workflow.driver_workflow_rx_len;
  fold (client_driver_closed d st1);
  assert (pure (client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0)));
  assert (pure (client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0)));
  assert (pure (exists st_close_notify.
    client_driver_close_correct
      'st0
      st_close_notify
      workflow.driver_workflow_status
      wait_for_peer));
  workflow.driver_workflow_status
}

(**
  Safely disposes a connected transport after a workflow failure.  This is
  deliberately independent of the TLS control state: callers use it when a
  receive or send workflow has reported a non-retryable status and therefore
  cannot establish the application-ready precondition of [close].
**)
fn abort
  (d:client_driver)
  requires client_driver_connected d 'st0 'received0 'sent0
  ensures client_driver_closed d 'st0
{
  unfold (client_driver_connected
    d
    'st0
    (Ghost.reveal 'received0)
    (Ghost.reveal 'sent0));
  with ch buffered buffered_len.
    assert (C.connection_exactly d.client_driver_client 'st0 **
            client_driver_canonical_seed d **
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
  let current_channel = Box.(!d.client_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (concrete_ch == ch));
  rewrite
    (IO.is_channel ch (Ghost.reveal 'received0) (Ghost.reveal 'sent0))
    as
    (IO.is_channel
      concrete_ch
      (Ghost.reveal 'received0)
      (Ghost.reveal 'sent0));
  unfold (client_driver_buffers d buffered buffered_len);
  let current_buffered_len = Box.(!d.client_driver_buffered_len);
  assert (pure (current_buffered_len == buffered_len));
  fold (client_driver_buffers d buffered current_buffered_len);
  Box.(d.client_driver_channel := no_channel);
  fold (channel_open concrete_ch 'st0 buffered current_buffered_len);
  close_failed_connect d concrete_ch current_buffered_len;
}
