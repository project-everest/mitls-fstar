module TLS13.Impl.Client.Driver.Receive

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
#push-options "--z3refresh --z3rlimit 10 --split_queries always --z3seed 17"
fn rec driver_receive_application_data
  (d:top_driver)
  (empty_payload:array U8.t)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (auth_leaf_der:array U8.t)
  (auth_leaf_der_len:SZ.t)
  (auth_payload:array U8.t)
  (auth_cv_input:array U8.t)
  (auth_cv_input_len:SZ.t)
  (auth_signature:array U8.t)
  (auth_signature_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires top_driver_exactly d 'st0 'buffered buffered_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to auth_leaf_der 'old_auth_leaf_der **
           pts_to auth_payload 'old_auth_payload **
           pts_to auth_cv_input 'old_auth_cv_input **
           pts_to auth_signature 'old_auth_signature **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'buffered == SZ.v buffered_len /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_auth_leaf_der == SZ.v auth_leaf_der_len /\
                 B.length 'old_auth_payload == SZ.v certificate_public_key_len /\
                 B.length 'old_auth_cv_input == SZ.v auth_cv_input_len /\
                 B.length 'old_auth_signature == SZ.v auth_signature_len /\
                 Bounds.max_handshake_flight_len <= SZ.v auth_leaf_der_len /\
                 SZ.v certificate_public_key_len <= Bounds.max_public_key_len /\
                 Bounds.max_certificate_verify_input_len <= SZ.v auth_cv_input_len /\
                 L.max_signature_len <= SZ.v auth_signature_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: driver_workflow_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
           top_driver_exactly d st1 buffered_after result.driver_workflow_rx_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to auth_leaf_der auth_leaf_der_bytes **
           pts_to auth_payload auth_payload_bytes **
           pts_to auth_cv_input auth_cv_input_bytes **
           pts_to auth_signature auth_signature_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 B.length auth_leaf_der_bytes == SZ.v auth_leaf_der_len /\
                 B.length auth_payload_bytes == SZ.v certificate_public_key_len /\
                 B.length auth_cv_input_bytes == SZ.v auth_cv_input_len /\
                 B.length auth_signature_bytes == SZ.v auth_signature_len /\
                 SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity /\
                 B.length buffered_after == SZ.v result.driver_workflow_rx_len /\
                 Seq.equal buffered_after
                   (Seq.slice raw_bytes 0 (SZ.v result.driver_workflow_rx_len)) /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 client_receive_observation_network_correct
                   'st0
                   st1
                   (client_driver_workflow_observation result)
                   app_out_bytes /\
                 (CT.client_end_to_end_invariant 'st0 ==>
                  CT.client_end_to_end_invariant st1))
  decreases (SZ.v fuel)
{
  if (fuel = 0sz) {
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
    unfold (top_driver_exactly d 'st0 'buffered buffered_len);
    let network =
      driver_progress_buffered_network_step
        d.top_driver_core
        raw
        raw_capacity
        buffered_len
        network_out
        network_out_len
        app_out
        app_out_len;
    with st_network buffered_network raw_network network_out_network app_out_network.
      assert (driver_exactly d.top_driver_core st_network
                buffered_network
                network.buffered_network_io_buffered.buffered_network_new_len **
              pts_to raw raw_network **
              pts_to network_out network_out_network **
              pts_to app_out app_out_network);
    assert (pure (st_network.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    (* Take a control-state snapshot of the post-network-step state while the
       underlying driver resource is still directly available, so that the
       peer close_notify (ControlClosed) case can be detected below without
       recursing to fuel exhaustion. *)
    let snapshot = driver_control_snapshot d.top_driver_core;
    assert (pure (CR.control_snapshot_matches snapshot st_network));
    let net_closed = snapshot.CR.snapshot_control_tag = 4uy;
    fold (top_driver_exactly d st_network
      buffered_network
      network.buffered_network_io_buffered.buffered_network_new_len);
    assert (pure (CT.client_end_to_end_invariant 'st0 ==>
      CT.client_end_to_end_invariant st_network));
    let no_op_resp = {
      CT.network_out_len = 0sz;
      CT.app_out_len = 0sz;
      CT.status = CT.NeedMoreInput;
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
      assert (pure (result.driver_workflow_status == DriverWorkflowStepFailed));
      assert (pure (result.driver_workflow_status <> DriverWorkflowExhausted));
      assert (pure (result.driver_workflow_network == network));
      assert (pure (result.driver_workflow_rx_len ==
        network.buffered_network_io_buffered.buffered_network_new_len));
      assert (pure (client_buffered_network_io_step_correct
        st_network
        network
        network_out_network
        app_out_network));
      lemma_client_receive_observation_network_correct_from_buffered
        'st0
        st_network
        st_network
        result
        network_out_network
        app_out_network
        app_out_network;
      assert (pure (B.length raw_network == SZ.v raw_capacity));
      assert (pure (B.length 'old_auth_leaf_der == SZ.v auth_leaf_der_len));
      assert (pure (B.length 'old_auth_payload == SZ.v certificate_public_key_len));
      assert (pure (B.length 'old_auth_cv_input == SZ.v auth_cv_input_len));
      assert (pure (B.length 'old_auth_signature == SZ.v auth_signature_len));
      assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity));
      assert (pure (B.length buffered_network == SZ.v result.driver_workflow_rx_len));
      assert (pure (Seq.equal buffered_network
        (Seq.slice raw_network 0 (SZ.v result.driver_workflow_rx_len))));
      assert (pure (B.length network_out_network == SZ.v network_out_len));
      assert (pure (B.length app_out_network == SZ.v app_out_len));
      assert (pure (client_receive_observation_network_correct
        'st0
        st_network
        (client_driver_workflow_observation result)
        app_out_network));
      assert (pure (CT.client_end_to_end_invariant 'st0 ==>
        CT.client_end_to_end_invariant st_network));
      rewrite (top_driver_exactly
        d
        st_network
        buffered_network
        network.buffered_network_io_buffered.buffered_network_new_len) as
        (top_driver_exactly
          d
          st_network
          buffered_network
          result.driver_workflow_rx_len);
      result
    } else {
    let app_ready =
      network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.app_out_len =
      0sz;
    if (app_ready = false) {
      assert (pure (client_buffered_network_io_step_correct
        st_network
        network
        network_out_network
        app_out_network));
      let result = {
        driver_workflow_status = DriverWorkflowOk;
        driver_workflow_rx_len =
          network.buffered_network_io_buffered.buffered_network_new_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = network;
      };
      assert (pure (result.driver_workflow_status == DriverWorkflowOk));
      assert (pure (result.driver_workflow_network == network));
      lemma_client_receive_observation_network_correct_from_buffered
        'st0
        st_network
        st_network
        result
        network_out_network
        app_out_network
        app_out_network;
      assert (pure (client_receive_observation_network_correct
        'st0
        st_network
        (client_driver_workflow_observation result)
        app_out_network));
      assert (pure (result.driver_workflow_rx_len ==
        network.buffered_network_io_buffered.buffered_network_new_len));
      assert (pure (B.length raw_network == SZ.v raw_capacity));
      assert (pure (B.length 'old_auth_leaf_der == SZ.v auth_leaf_der_len));
      assert (pure (B.length 'old_auth_payload == SZ.v certificate_public_key_len));
      assert (pure (B.length 'old_auth_cv_input == SZ.v auth_cv_input_len));
      assert (pure (B.length 'old_auth_signature == SZ.v auth_signature_len));
      assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity));
      assert (pure (B.length buffered_network == SZ.v result.driver_workflow_rx_len));
      assert (pure (Seq.equal buffered_network
        (Seq.slice raw_network 0 (SZ.v result.driver_workflow_rx_len))));
      assert (pure (B.length network_out_network == SZ.v network_out_len));
      assert (pure (B.length app_out_network == SZ.v app_out_len));
      assert (pure (CT.client_end_to_end_invariant 'st0 ==>
        CT.client_end_to_end_invariant st_network));
      rewrite (top_driver_exactly
        d
        st_network
        buffered_network
        network.buffered_network_io_buffered.buffered_network_new_len) as
        (top_driver_exactly
          d
          st_network
          buffered_network
          result.driver_workflow_rx_len);
      result
    } else if (net_ok && net_closed) {
      (* A StepOk network step produced zero application bytes and the
         connection control state is ControlClosed: the peer sent
         close_notify. Report this to the caller directly instead of
         draining local actions (none is legal once ControlClosed) and
         recursing until [fuel] is exhausted. *)
      assert (pure (st_network.CS.cs_model.CS.model_control == CS.ControlClosed));
      assert (pure (client_buffered_network_io_step_correct
        st_network
        network
        network_out_network
        app_out_network));
      let result = {
        driver_workflow_status = DriverWorkflowClosed;
        driver_workflow_rx_len =
          network.buffered_network_io_buffered.buffered_network_new_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = network;
      };
      assert (pure (result.driver_workflow_status == DriverWorkflowClosed));
      assert (pure (result.driver_workflow_status <> DriverWorkflowExhausted));
      assert (pure (result.driver_workflow_network == network));
      assert (pure (result.driver_workflow_network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.app_out_len == 0sz));
      lemma_client_receive_observation_network_correct_from_buffered
        'st0
        st_network
        st_network
        result
        network_out_network
        app_out_network
        app_out_network;
      assert (pure (client_receive_observation_network_correct
        'st0
        st_network
        (client_driver_workflow_observation result)
        app_out_network));
      assert (pure (result.driver_workflow_rx_len ==
        network.buffered_network_io_buffered.buffered_network_new_len));
      assert (pure (B.length raw_network == SZ.v raw_capacity));
      assert (pure (B.length 'old_auth_leaf_der == SZ.v auth_leaf_der_len));
      assert (pure (B.length 'old_auth_payload == SZ.v certificate_public_key_len));
      assert (pure (B.length 'old_auth_cv_input == SZ.v auth_cv_input_len));
      assert (pure (B.length 'old_auth_signature == SZ.v auth_signature_len));
      assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity));
      assert (pure (B.length buffered_network == SZ.v result.driver_workflow_rx_len));
      assert (pure (Seq.equal buffered_network
        (Seq.slice raw_network 0 (SZ.v result.driver_workflow_rx_len))));
      assert (pure (B.length network_out_network == SZ.v network_out_len));
      assert (pure (B.length app_out_network == SZ.v app_out_len));
      assert (pure (CT.client_end_to_end_invariant 'st0 ==>
        CT.client_end_to_end_invariant st_network));
      rewrite (top_driver_exactly
        d
        st_network
        buffered_network
        network.buffered_network_io_buffered.buffered_network_new_len) as
        (top_driver_exactly
          d
          st_network
          buffered_network
          result.driver_workflow_rx_len);
      result
    } else {
      let local =
        top_driver_process_one_local_action
          d
          empty_payload
          network_out
          network_out_len
          auth_leaf_der
          auth_leaf_der_len
          auth_payload
          certificate_public_key_len
          auth_cv_input
          auth_cv_input_len
          auth_signature
          auth_signature_len
          server_finished_payload_len
          app_out
          app_out_len;
      with st_local network_out_local auth_leaf_der_local auth_payload_local auth_cv_input_local auth_signature_local app_out_local.
        assert (top_driver_exactly d st_local
                  buffered_network
                  network.buffered_network_io_buffered.buffered_network_new_len **
                pts_to network_out network_out_local **
                pts_to auth_leaf_der auth_leaf_der_local **
                pts_to auth_payload auth_payload_local **
                pts_to auth_cv_input auth_cv_input_local **
                pts_to auth_signature auth_signature_local **
                pts_to app_out app_out_local);
      assert (pure (st_local.CS.cs_model.CS.model_config ==
        st_network.CS.cs_model.CS.model_config));
      assert (pure (st_local.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      if local.ready_local_processed {
        assert (pure (local.ready_local_processed == true));
        assert (pure (local.ready_local_processed == true ==>
          (CT.client_end_to_end_invariant st_network ==>
           CT.client_end_to_end_invariant st_local)));
        assert (pure (CT.client_end_to_end_invariant st_network ==>
          CT.client_end_to_end_invariant st_local));
        assert (pure (CT.client_end_to_end_invariant 'st0 ==>
          CT.client_end_to_end_invariant st_local))
      } else {
        assert (pure (st_local == st_network));
        assert (pure (CT.client_end_to_end_invariant 'st0 ==>
          CT.client_end_to_end_invariant st_local))
      };
      let local_processed = local.ready_local_processed;
      let local_ready = local.ready_local_action.CT.next_local_ready;
      let local_ok = local.ready_local_resp.CT.status = CT.StepOk;
      let local_wrote_all =
        local.ready_local_written = local.ready_local_resp.CT.network_out_len;
      let local_short_write = local_processed && local_ok && (local_wrote_all = false);
      let local_failed =
        (local_processed && ((local_ok = false) || local_short_write)) ||
        ((local_processed = false) && local_ready);
      if local_failed {
        let result = {
          driver_workflow_status = DriverWorkflowStepFailed;
          driver_workflow_rx_len =
            network.buffered_network_io_buffered.buffered_network_new_len;
          driver_workflow_local = {
            driver_drain_last = local;
            driver_drain_exhausted = false;
          };
          driver_workflow_network = network;
        };
        assert (pure (result.driver_workflow_status == DriverWorkflowStepFailed));
        assert (pure (result.driver_workflow_status <> DriverWorkflowExhausted));
        assert (pure (result.driver_workflow_network == network));
        assert (pure (result.driver_workflow_rx_len ==
          network.buffered_network_io_buffered.buffered_network_new_len));
        assert (pure (result.driver_workflow_status == DriverWorkflowOk ==>
          st_network == st_local /\ Seq.equal app_out_network app_out_local));
        assert (pure (client_buffered_network_io_step_correct
          st_network
          network
          network_out_network
          app_out_network));
        lemma_client_receive_observation_network_correct_from_buffered
          'st0
          st_local
          st_network
          result
          network_out_network
          app_out_network
          app_out_local;
        assert (pure (client_receive_observation_network_correct
          'st0
          st_local
          (client_driver_workflow_observation result)
          app_out_local));
        assert (pure (B.length raw_network == SZ.v raw_capacity));
        assert (pure (B.length auth_leaf_der_local == SZ.v auth_leaf_der_len));
        assert (pure (B.length auth_payload_local == SZ.v certificate_public_key_len));
        assert (pure (B.length auth_cv_input_local == SZ.v auth_cv_input_len));
        assert (pure (B.length auth_signature_local == SZ.v auth_signature_len));
        assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity));
        assert (pure (B.length buffered_network == SZ.v result.driver_workflow_rx_len));
        assert (pure (Seq.equal buffered_network
          (Seq.slice raw_network 0 (SZ.v result.driver_workflow_rx_len))));
        assert (pure (B.length network_out_local == SZ.v network_out_len));
        assert (pure (B.length app_out_local == SZ.v app_out_len));
        assert (pure (CT.client_end_to_end_invariant 'st0 ==>
          CT.client_end_to_end_invariant st_local));
        rewrite (top_driver_exactly
          d
          st_local
          buffered_network
          network.buffered_network_io_buffered.buffered_network_new_len) as
          (top_driver_exactly
            d
            st_local
            buffered_network
            result.driver_workflow_rx_len);
        result
      } else {
        let next_fuel = SZ.sub fuel 1sz;
        assert (pure (SZ.v next_fuel < SZ.v fuel));
        driver_receive_application_data
          d
          empty_payload
          raw
          raw_capacity
          network.buffered_network_io_buffered.buffered_network_new_len
          network_out
          network_out_len
          auth_leaf_der
          auth_leaf_der_len
          auth_payload
          auth_cv_input
          auth_cv_input_len
          auth_signature
          auth_signature_len
          certificate_public_key_len
          server_finished_payload_len
          app_out
          app_out_len
          local_fuel
          next_fuel
      }
    }
    }
  }
}
#pop-options

fn run
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
                SZ.v result.client_receive_len <= SZ.v out_len /\
          st1.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config /\
          client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0) /\
          client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0) /\
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
  match current_channel {
    None -> {
      assert (pure False);
      fold (client_driver_buffers d buffered current_buffered_len);
      fold (client_driver_connected d 'st0 (Ghost.reveal 'received0) (Ghost.reveal 'sent0));
      {
        client_receive_status = DriverWorkflowStepFailed;
        client_receive_len = 0sz;
      }
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
      let workflow =
        driver_receive_application_data
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
      with st1 workflow_buffered raw_bytes network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
        assert (top_driver_exactly td st1 workflow_buffered workflow.driver_workflow_rx_len **
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
      let response =
        workflow.driver_workflow_network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response;
      let copy_len = response.CT.app_out_len;
      let app_fits = SZ.lte copy_len out_len;
      let app_src_fits = SZ.lte copy_len driver_app_out_capacity;
      let workflow_ok = workflow.driver_workflow_status = DriverWorkflowOk;
      if (workflow_ok && app_fits && app_src_fits) {
        A.pts_to_len (V.vec_to_array d.client_driver_app_out);
        A.pts_to_len out;
        assert (pure (SZ.v copy_len <= SZ.v out_len));
        assert (pure (SZ.v copy_len <= B.length app_out_bytes));
        assert (pure (A.length (V.vec_to_array d.client_driver_app_out) == B.length app_out_bytes));
        assert (pure (A.length out == SZ.v out_len));
        assert (pure (SZ.v copy_len <= A.length (V.vec_to_array d.client_driver_app_out)));
        assert (pure (SZ.v copy_len <= A.length out));
        let _ = A.memcpy_l copy_len (V.vec_to_array d.client_driver_app_out) out;
        with out_bytes.
          assert (pts_to out out_bytes);
        A.pts_to_len out;
        assert (pure (B.length out_bytes == SZ.v out_len));
        assert (pure (SZ.v copy_len <= B.length app_out_bytes));
        assert (pure (Seq.equal
          (CT.response_app_out response app_out_bytes)
          (Seq.slice app_out_bytes 0 (SZ.v copy_len))));
        Seq.lemma_len_slice out_bytes 0 (SZ.v copy_len);
        Seq.lemma_len_slice app_out_bytes 0 (SZ.v copy_len);
        assert (pure (Seq.equal
          (Seq.slice out_bytes 0 (SZ.v copy_len))
          (Seq.slice app_out_bytes 0 (SZ.v copy_len))));
        let receive_result = {
          client_receive_status = DriverWorkflowOk;
          client_receive_len = copy_len;
        };
        assert (pure (client_driver_receive_copyout_correct
          receive_result
          response
          app_out_bytes
          out_bytes));
        assert (pure (client_driver_receive_status_correct
          receive_result
          (client_driver_workflow_observation workflow)
          app_out_bytes
          out_bytes));
        assert (pure (client_driver_receive_correct
          'st0
          st1
          receive_result
          (client_driver_workflow_observation workflow)
          app_out_bytes
          out_bytes));
        assert (pure (exists obs app_out.
          client_driver_receive_correct
            'st0
            st1
            receive_result
            obs
            app_out
            out_bytes));
        unfold (top_driver_exactly td st1 workflow_buffered workflow.driver_workflow_rx_len);
        rewrite (driver_exactly td.top_driver_core st1 workflow_buffered workflow.driver_workflow_rx_len) as
          (driver_exactly core st1 workflow_buffered workflow.driver_workflow_rx_len);
        unfold (driver_exactly core st1 workflow_buffered workflow.driver_workflow_rx_len);
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
        Box.(d.client_driver_buffered_len := workflow.driver_workflow_rx_len);
        assert (pure (SZ.v workflow.driver_workflow_rx_len <= SZ.v driver_rx_capacity));
        rewrite (C.connection_exactly core.driver_client st1) as
          (C.connection_exactly d.client_driver_client st1);
        rewrite (channel_open core.driver_channel st1 workflow_buffered workflow.driver_workflow_rx_len) as
          (channel_open ch st1 workflow_buffered workflow.driver_workflow_rx_len);
        rewrite (O.is_auth_context td.top_driver_auth) as
          (O.is_auth_context d.client_driver_auth);
        fold (client_driver_buffers d workflow_buffered workflow.driver_workflow_rx_len);
        unfold (channel_open ch st1 workflow_buffered workflow.driver_workflow_rx_len);
        with received1 sent1.
          assert (IO.is_channel ch received1 sent1 **
                  pure (client_driver_wire_logs_match st1 received1 sent1 workflow_buffered workflow.driver_workflow_rx_len));
        assert (pure (client_driver_sent_log_exact st1 sent1));
        lemma_client_driver_wire_logs_match_received_accounted
          st1
          received1
          sent1
          workflow_buffered
          workflow.driver_workflow_rx_len;
        assert (pure (client_driver_received_log_accounted st1 received1));
        fold (client_driver_connected d st1 received1 sent1);
        receive_result
      } else {
        with out_bytes.
          assert (pts_to out out_bytes);
        assert (pure (B.length out_bytes == SZ.v out_len));
        let receive_result = {
          client_receive_status =
            if workflow_ok then DriverWorkflowStepFailed else workflow.driver_workflow_status;
          client_receive_len = 0sz;
        };
        assert (pure (client_driver_receive_status_correct
          receive_result
          (client_driver_workflow_observation workflow)
          app_out_bytes
          out_bytes));
        assert (pure (client_driver_receive_correct
          'st0
          st1
          receive_result
          (client_driver_workflow_observation workflow)
          app_out_bytes
          out_bytes));
        assert (pure (exists obs app_out.
          client_driver_receive_correct
            'st0
            st1
            receive_result
            obs
            app_out
            out_bytes));
        unfold (top_driver_exactly td st1 workflow_buffered workflow.driver_workflow_rx_len);
        rewrite (driver_exactly td.top_driver_core st1 workflow_buffered workflow.driver_workflow_rx_len) as
          (driver_exactly core st1 workflow_buffered workflow.driver_workflow_rx_len);
        unfold (driver_exactly core st1 workflow_buffered workflow.driver_workflow_rx_len);
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
        Box.(d.client_driver_buffered_len := workflow.driver_workflow_rx_len);
        assert (pure (SZ.v workflow.driver_workflow_rx_len <= SZ.v driver_rx_capacity));
        rewrite (C.connection_exactly core.driver_client st1) as
          (C.connection_exactly d.client_driver_client st1);
        rewrite (channel_open core.driver_channel st1 workflow_buffered workflow.driver_workflow_rx_len) as
          (channel_open ch st1 workflow_buffered workflow.driver_workflow_rx_len);
        rewrite (O.is_auth_context td.top_driver_auth) as
          (O.is_auth_context d.client_driver_auth);
        fold (client_driver_buffers d workflow_buffered workflow.driver_workflow_rx_len);
        unfold (channel_open ch st1 workflow_buffered workflow.driver_workflow_rx_len);
        with received1 sent1.
          assert (IO.is_channel ch received1 sent1 **
                  pure (client_driver_wire_logs_match st1 received1 sent1 workflow_buffered workflow.driver_workflow_rx_len));
        assert (pure (client_driver_sent_log_exact st1 sent1));
        lemma_client_driver_wire_logs_match_received_accounted
          st1
          received1
          sent1
          workflow_buffered
          workflow.driver_workflow_rx_len;
        assert (pure (client_driver_received_log_accounted st1 received1));
        fold (client_driver_connected d st1 received1 sent1);
        receive_result
      }
    }
  }
}
