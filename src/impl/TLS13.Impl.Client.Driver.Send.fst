module TLS13.Impl.Client.Driver.Send

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module A = Pulse.Lib.Array
module BT = Common.BufferedTCP
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
module BN = TLS13.Impl.Client.Driver.BufferedNetwork
open TLS13.Impl.Client.Driver.State
open TLS13.Impl.Client.Driver.Core

let lemma_client_driver_send_correct_from_local
  (st0 st1:CS.connection_state)
  (status:driver_workflow_status)
  (payload sent sent':B.bytes)
  (resp:CT.client_response)
  : Lemma
      (requires
        status <> DriverWorkflowPayloadTooLarge /\
        client_driver_local_write_correct
          st0
          st1
          resp
          CT.LocalSendApplicationData
          payload
          sent
          sent' /\
        client_driver_send_status_correct status resp /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          st0.CS.cs_wire_log.CL.raw_received)
      (ensures client_driver_send_correct
        st0 st1 status payload sent sent')
=
  assert (exists response.
    client_driver_local_write_correct
      st0
      st1
      response
      CT.LocalSendApplicationData
      payload
      sent
      sent' /\
    client_driver_send_status_correct status response);
  assert (client_driver_send_correct st0 st1 status payload sent sent')

let lemma_client_driver_send_failed_status
  (resp:CT.client_response)
  : Lemma
      (requires not (resp.CT.status == CT.StepOk))
      (ensures client_driver_send_status_correct
        DriverWorkflowStepFailed resp)
=
  if resp.CT.status = CT.StepOk
  then assert False
  else ()

let lemma_send_application_data_local_input_wf
  (st:CS.connection_state)
  (payload:B.bytes)
  : Lemma (CT.local_input_wf st CT.LocalSendApplicationData payload)
=
  ()

inline_for_extraction
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
      CT.LocalSendApplicationData
      payload
      payload_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (top_buffered_driver_exactly
              (top_driver_as_buffered d)
              st1
              (Ghost.reveal 'buffered)
              (Ghost.reveal 'pending_len) **
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
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
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

#push-options "--z3rlimit 100"
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
                 client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0) /\
                 client_driver_sent_log_exact st1 sent1 /\
                 client_driver_received_log_accounted st1 received1 /\
                 ((status == DriverWorkflowOk \/ status == DriverWorkflowPayloadTooLarge) ==>
                   CT.connection_control_not_failed st1))
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
      assert (pure (client_driver_wire_logs_match_witness
        'st0
        (Ghost.reveal 'received0)
        (Ghost.reveal 'sent0)
        committed
        (BT.pending model)
        buffered_len));
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
      fold (client_driver_connected_indexed
        d
        'st0
        (Ghost.reveal 'received0)
        (Ghost.reveal 'sent0)
        channel
        model
        committed
        buffered_len);
      assert_norm (SM.max_application_data_fragment_len == 16384);
      let too_large = SZ.gt payload_len 16384sz;
      if too_large {
        assert (pure (client_driver_payload_too_large
          (Ghost.reveal 'payload_bytes)));
        fold (client_driver_connected
          d 'st0 (Ghost.reveal 'received0) (Ghost.reveal 'sent0));
        DriverWorkflowPayloadTooLarge
      } else {
        lemma_send_application_data_local_input_wf
          'st0
          (Ghost.reveal 'payload_bytes);
        unfold (client_driver_connected_indexed
          d
          'st0
          (Ghost.reveal 'received0)
          (Ghost.reveal 'sent0)
          channel
          model
          committed
          buffered_len);
        let current_channel = Box.(!d.client_driver_channel);
        assert (pure (current_channel == Some channel));
        assert (pure (Some? current_channel));
        let concrete_channel = Some?.v current_channel;
        assert (pure (concrete_channel == channel));
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
        fold (buffered_driver_exactly
          (client_buffered_driver d concrete_channel)
          'st0
          (BT.pending model)
          buffered_len);
        rewrite
          (buffered_driver_exactly
            (client_buffered_driver d concrete_channel)
            'st0
            (BT.pending model)
            buffered_len)
          as
          (buffered_driver_exactly
            (driver_as_buffered td.top_driver_core)
            'st0
            (BT.pending model)
            buffered_len);
        fold (driver_exactly
          td.top_driver_core
          'st0
          (BT.pending model)
          buffered_len);
        rewrite
          (O.is_auth_context d.client_driver_auth)
          as
          (O.is_auth_context td.top_driver_auth);
        fold (top_driver_exactly
          td
          'st0
          (BT.pending model)
          buffered_len);
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
          assert (
            top_driver_exactly
              td
              st1
              (BT.pending model)
              buffered_len **
            pts_to payload 'payload_bytes **
            pts_to
              (V.vec_to_array d.client_driver_network_out)
              network_out_bytes **
            pts_to
              (V.vec_to_array d.client_driver_app_out)
              app_out_bytes);
        V.to_vec_pts_to d.client_driver_network_out;
        V.to_vec_pts_to d.client_driver_app_out;
        unfold (top_driver_exactly
          td st1 (BT.pending model) buffered_len);
        unfold (driver_exactly
          td.top_driver_core st1 (BT.pending model) buffered_len);
        rewrite
          (buffered_driver_exactly
            (driver_as_buffered td.top_driver_core)
            st1
            (BT.pending model)
            buffered_len)
          as
          (buffered_driver_exactly
            (client_buffered_driver d concrete_channel)
            st1
            (BT.pending model)
            buffered_len);
        unfold (buffered_driver_exactly
          (client_buffered_driver d concrete_channel)
          st1
          (BT.pending model)
          buffered_len);
        with model1 received1 committed1 sent1.
          assert (buffered_driver_indexed
            (client_buffered_driver d concrete_channel)
            st1
            (BT.pending model)
            buffered_len
            model1
            received1
            committed1
            sent1);
        unfold (buffered_driver_indexed
          (client_buffered_driver d concrete_channel)
          st1
          (BT.pending model)
          buffered_len
          model1
          received1
          committed1
          sent1);
        assert (pure (client_driver_sent_log_exact st1 sent1));
        assert (pure (client_driver_wire_logs_match_witness
          st1
          received1
          sent1
          committed1
          (BT.pending model)
          buffered_len));
        assert (pure (client_driver_wire_logs_match
          st1
          received1
          sent1
          (BT.pending model)
          buffered_len));
        lemma_client_driver_wire_logs_match_received_accounted
          st1 received1 sent1 (BT.pending model) buffered_len;
        assert (pure (client_driver_local_write_correct
          'st0
          st1
          result.local_write_resp
          CT.LocalSendApplicationData
          (Ghost.reveal 'payload_bytes)
          (Ghost.reveal 'sent0)
          sent1));
        assert (pure (Seq.equal
          (BT.pending model1)
          (BT.pending model)));
        Seq.lemma_eq_elim (BT.pending model1) (BT.pending model);
        fold (buffered_driver_indexed
          (client_buffered_driver d concrete_channel)
          st1
          (BT.pending model1)
          buffered_len
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
          buffered_len);
        fold (client_driver_connected d st1 received1 sent1);
        lemma_local_event_wire_lengths
          'st0
          st1
          result.local_write_resp
          CT.LocalSendApplicationData
          (Ghost.reveal 'payload_bytes)
          network_out_bytes
          app_out_bytes;
        assert (pure (Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          'st0.CS.cs_wire_log.CL.raw_received));
        let ok = result.local_write_resp.CT.status = CT.StepOk;
        if ok {
          CT.lemma_local_send_application_data_stepok_preserves_not_failed
            'st0
            st1
            result.local_write_resp
            (Ghost.reveal 'payload_bytes)
            network_out_bytes
            app_out_bytes;
          assert (pure (client_driver_send_status_correct
            DriverWorkflowOk
            result.local_write_resp));
          lemma_client_driver_send_correct_from_local
            'st0 st1 DriverWorkflowOk
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'sent0)
            sent1
            result.local_write_resp;
          DriverWorkflowOk
        } else {
          lemma_client_driver_send_failed_status result.local_write_resp;
          lemma_client_driver_send_correct_from_local
            'st0 st1 DriverWorkflowStepFailed
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'sent0)
            sent1
            result.local_write_resp;
          DriverWorkflowStepFailed
        }
      }
    }

#pop-options
let key_update_kind (request:bool) : CT.local_event_kind =
  if request then CT.LocalSendKeyUpdateRequested else CT.LocalSendKeyUpdate

let lemma_send_key_update_local_input_wf
  (st:CS.connection_state)
  (kind:CT.local_event_kind)
  (payload:B.bytes)
  : Lemma
      (requires
        kind == CT.LocalSendKeyUpdate \/
        kind == CT.LocalSendKeyUpdateRequested)
      (ensures CT.local_input_wf st kind payload)
=
  match kind with
  | CT.LocalSendKeyUpdate -> ()
  | CT.LocalSendKeyUpdateRequested -> ()

let lemma_client_driver_key_update_correct_from_local
  (st0 st1:CS.connection_state)
  (status:driver_workflow_status)
  (kind:CT.local_event_kind)
  (sent sent':B.bytes)
  (resp:CT.client_response)
  : Lemma
      (requires
        client_driver_local_write_correct
          st0
          st1
          resp
          kind
          B.empty
          sent
          sent' /\
        client_driver_send_status_correct status resp /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          st0.CS.cs_wire_log.CL.raw_received)
      (ensures client_driver_key_update_correct
        st0 st1 status kind sent sent')
=
  assert (exists response.
    client_driver_local_write_correct
      st0
      st1
      response
      kind
      B.empty
      sent
      sent' /\
    client_driver_send_status_correct status response);
  assert (client_driver_key_update_correct st0 st1 status kind sent sent')

(**
  Is a mandated KeyUpdate reply due?  RFC 8446 4.6.3 obliges an endpoint that
  received [update_requested] to answer with its own KeyUpdate.  The gate is
  exactly [run_key_update]'s own success condition -- control state, role,
  installed write key, room for one more record sequence number, and an output
  buffer big enough -- with the pending flag added, so a [true] here cannot
  lead to a spurious step failure.
**)
fn query_key_update_response_pending
  (d:client_driver)
  requires client_driver_connected d 'st0 'received0 'sent0
  returns pending:bool
  ensures client_driver_connected d 'st0 'received0 'sent0
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
  rewrite
    (C.connection_exactly
      (client_buffered_driver d channel).buffered_driver_client
      'st0)
    as
    (CR.connection_exactly d.client_driver_client 'st0);
  let pending =
    CQ.can_send_key_update_runtime
      d.client_driver_client
      driver_network_out_capacity;
  rewrite
    (CR.connection_exactly d.client_driver_client 'st0)
    as
    (C.connection_exactly
      (client_buffered_driver d channel).buffered_driver_client
      'st0);
  fold (buffered_driver_indexed
    (client_buffered_driver d channel)
    'st0
    (BT.pending model)
    buffered_len
    model
    (Ghost.reveal 'received0)
    committed
    (Ghost.reveal 'sent0));
  fold (client_driver_connected_indexed
    d
    'st0
    (Ghost.reveal 'received0)
    (Ghost.reveal 'sent0)
    channel
    model
    committed
    buffered_len);
  fold (client_driver_connected
    d 'st0 (Ghost.reveal 'received0) (Ghost.reveal 'sent0));
  pending
}

inline_for_extraction
fn top_driver_send_key_update
  (d:top_driver)
  (kind:CT.local_event_kind)
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
                 (kind == CT.LocalSendKeyUpdate \/
                  kind == CT.LocalSendKeyUpdateRequested))
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
                  kind
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
  lemma_send_key_update_local_input_wf
    'st0 kind (Ghost.reveal 'payload_bytes);
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
      kind
      payload
      payload_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (top_buffered_driver_exactly
              (top_driver_as_buffered d)
              st1
              (Ghost.reveal 'buffered)
              (Ghost.reveal 'pending_len) **
            pts_to payload 'payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  CT.lemma_local_event_end_to_end_correct_preserves_config
    'st0
    st1
    result.local_write_resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
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
{
  let kind = key_update_kind request;
  assert (pure (kind == CT.LocalSendKeyUpdate \/
                kind == CT.LocalSendKeyUpdateRequested));
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
  let concrete_channel = Some?.v current_channel;
  assert (pure (concrete_channel == channel));
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
  fold (buffered_driver_exactly
    (client_buffered_driver d concrete_channel)
    'st0
    (BT.pending model)
    buffered_len);
  rewrite
    (buffered_driver_exactly
      (client_buffered_driver d concrete_channel)
      'st0
      (BT.pending model)
      buffered_len)
    as
    (buffered_driver_exactly
      (driver_as_buffered td.top_driver_core)
      'st0
      (BT.pending model)
      buffered_len);
  fold (driver_exactly
    td.top_driver_core
    'st0
    (BT.pending model)
    buffered_len);
  rewrite
    (O.is_auth_context d.client_driver_auth)
    as
    (O.is_auth_context td.top_driver_auth);
  fold (top_driver_exactly
    td
    'st0
    (BT.pending model)
    buffered_len);
  let result =
    top_driver_send_key_update
      td
      kind
      (V.vec_to_array d.client_driver_empty_payload)
      0sz
      (V.vec_to_array d.client_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.client_driver_app_out)
      driver_app_out_capacity;
  with st1 empty_payload1 network_out_bytes app_out_bytes.
    assert (
      top_driver_exactly
        td
        st1
        (BT.pending model)
        buffered_len **
      pts_to
        (V.vec_to_array d.client_driver_empty_payload)
        empty_payload1 **
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
    td st1 (BT.pending model) buffered_len);
  unfold (driver_exactly
    td.top_driver_core st1 (BT.pending model) buffered_len);
  rewrite
    (buffered_driver_exactly
      (driver_as_buffered td.top_driver_core)
      st1
      (BT.pending model)
      buffered_len)
    as
    (buffered_driver_exactly
      (client_buffered_driver d concrete_channel)
      st1
      (BT.pending model)
      buffered_len);
  unfold (buffered_driver_exactly
    (client_buffered_driver d concrete_channel)
    st1
    (BT.pending model)
    buffered_len);
  with model1 received1 committed1 sent1.
    assert (buffered_driver_indexed
      (client_buffered_driver d concrete_channel)
      st1
      (BT.pending model)
      buffered_len
      model1
      received1
      committed1
      sent1);
  unfold (buffered_driver_indexed
    (client_buffered_driver d concrete_channel)
    st1
    (BT.pending model)
    buffered_len
    model1
    received1
    committed1
    sent1);
  assert (pure (client_driver_sent_log_exact st1 sent1));
  lemma_client_driver_wire_logs_match_received_accounted
    st1 received1 sent1 (BT.pending model) buffered_len;
  assert (pure (Seq.equal empty_payload1 B.empty));
  Seq.lemma_eq_elim empty_payload1 B.empty;
  assert (pure (client_driver_local_write_correct
    'st0
    st1
    result.local_write_resp
    kind
    B.empty
    (Ghost.reveal 'sent0)
    sent1));
  assert (pure (Seq.equal
    (BT.pending model1)
    (BT.pending model)));
  Seq.lemma_eq_elim (BT.pending model1) (BT.pending model);
  fold (buffered_driver_indexed
    (client_buffered_driver d concrete_channel)
    st1
    (BT.pending model1)
    buffered_len
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
    buffered_len);
  fold (client_driver_connected d st1 received1 sent1);
  lemma_local_event_wire_lengths
    'st0
    st1
    result.local_write_resp
    kind
    B.empty
    network_out_bytes
    app_out_bytes;
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received));
  let ok = result.local_write_resp.CT.status = CT.StepOk;
  if ok {
    CT.lemma_local_send_key_update_stepok_preserves_not_failed
      'st0
      st1
      result.local_write_resp
      kind
      B.empty
      network_out_bytes
      app_out_bytes;
    assert (pure (client_driver_send_status_correct
      DriverWorkflowOk
      result.local_write_resp));
    lemma_client_driver_key_update_correct_from_local
      'st0 st1 DriverWorkflowOk kind
      (Ghost.reveal 'sent0)
      sent1
      result.local_write_resp;
    DriverWorkflowOk
  } else {
    lemma_client_driver_send_failed_status result.local_write_resp;
    lemma_client_driver_key_update_correct_from_local
      'st0 st1 DriverWorkflowStepFailed kind
      (Ghost.reveal 'sent0)
      sent1
      result.local_write_resp;
    DriverWorkflowStepFailed
  }
}
