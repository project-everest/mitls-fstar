module TLS13.Impl.Client.Driver.Receive

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BS = Common.BufferedStream
module BT = Common.BufferedTCP
module CI = Common.ChannelImplementation
module CChannel = TLS13.Impl.Client.ChannelImplementation
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module D = TLS13.Impl.Client.Drain
module L = TLS13.Impl.Messages
module O = TLS13.OpenSSL
module Box = Pulse.Lib.Box
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TChannel = TLS13.Impl.Channel
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module BN = TLS13.Impl.Client.Driver.BufferedNetwork
open TLS13.Impl.Client.Driver.State
open TLS13.Impl.Client.Driver.Core

noeq type receive_workflow_result = {
  receive_workflow_status: driver_workflow_status;
  receive_workflow_pending_len: SZ.t;
  receive_workflow_response: CT.client_buffer_response;
}

noextract
let receive_workflow_observation
  (result:receive_workflow_result)
  : client_receive_observation =
  {
    client_receive_observed_status = result.receive_workflow_status;
    client_receive_observed_response = result.receive_workflow_response;
  }

noextract
let receive_workflow_application_log
  (st0 st1:CS.connection_state)
  (result:receive_workflow_result)
  (app_out:B.bytes)
  : prop =
  let output =
    CT.response_app_out
      result.receive_workflow_response.CT.response
      app_out in
  TChannel.application_log st1 ==
    (if result.receive_workflow_status == DriverWorkflowOk
     then CI.append_received (TChannel.application_log st0) output
     else TChannel.application_log st0)

noextract
let lemma_receive_observation_network_witness
  (st0 st1:CS.connection_state)
  (buffer_resp:CT.client_buffer_response)
  (input old_network_out network_out old_app_out app_out:B.bytes)
  : Lemma
      (requires
        D.drained_network_bytes_end_to_end_correct
          st0 st1 buffer_resp input
          old_network_out network_out old_app_out app_out)
      (ensures
        exists st_network st_before observed_input
               observed_old_network_out observed_network_out
               observed_old_app_out observed_app_out.
          D.drained_network_bytes_end_to_end_correct
            st_before
            st_network
            buffer_resp
            observed_input
            observed_old_network_out
            observed_network_out
            observed_old_app_out
            observed_app_out /\
          st_network == st1 /\
          Seq.equal observed_app_out app_out)
=
  introduce exists st_network st_before observed_input
                   observed_old_network_out observed_network_out
                   observed_old_app_out observed_app_out.
      D.drained_network_bytes_end_to_end_correct
        st_before
        st_network
        buffer_resp
        observed_input
        observed_old_network_out
        observed_network_out
        observed_old_app_out
        observed_app_out /\
      st_network == st1 /\
      Seq.equal observed_app_out app_out
  with st1 st0 input old_network_out network_out old_app_out app_out and ()

noextract
let lemma_receive_observation_network_ok
  (st0 st1:CS.connection_state)
  (buffer_resp:CT.client_buffer_response)
  (input old_network_out network_out old_app_out app_out:B.bytes)
  : Lemma
      (requires
        D.drained_network_bytes_end_to_end_correct
          st0 st1 buffer_resp input
          old_network_out network_out old_app_out app_out)
      (ensures
        client_receive_observation_network_correct
          st0
          st1
          {
            client_receive_observed_status = DriverWorkflowOk;
            client_receive_observed_response = buffer_resp;
          }
          app_out)
=
  lemma_receive_observation_network_witness
    st0 st1 buffer_resp input
    old_network_out network_out old_app_out app_out;
  eliminate exists st_network st_before observed_input
                   observed_old_network_out observed_network_out
                   observed_old_app_out observed_app_out.
    D.drained_network_bytes_end_to_end_correct
      st_before
      st_network
      buffer_resp
      observed_input
      observed_old_network_out
      observed_network_out
      observed_old_app_out
      observed_app_out /\
    st_network == st1 /\
    Seq.equal observed_app_out app_out
  returns
    client_receive_observation_network_correct
      st0
      st1
      {
        client_receive_observed_status = DriverWorkflowOk;
        client_receive_observed_response = buffer_resp;
      }
      app_out
  with _.
  (
    introduce
      (DriverWorkflowOk <> DriverWorkflowExhausted) ==>
      exists st_observed st_before' observed_input'
             observed_old_network_out' observed_network_out'
             observed_old_app_out' observed_app_out'.
        D.drained_network_bytes_end_to_end_correct
          st_before'
          st_observed
          buffer_resp
          observed_input'
          observed_old_network_out'
          observed_network_out'
          observed_old_app_out'
          observed_app_out' /\
        (DriverWorkflowOk == DriverWorkflowOk ==>
          st_observed == st1 /\ Seq.equal observed_app_out' app_out) /\
        (DriverWorkflowOk == DriverWorkflowClosed ==>
          st_observed == st1 /\
          st1.CS.cs_model.CS.model_control == CS.ControlClosed /\
          buffer_resp.CT.response.CT.app_out_len == 0sz)
    with _not_exhausted. begin
      introduce exists st_observed st_before' observed_input'
                       observed_old_network_out' observed_network_out'
                       observed_old_app_out' observed_app_out'.
        D.drained_network_bytes_end_to_end_correct
          st_before'
          st_observed
          buffer_resp
          observed_input'
          observed_old_network_out'
          observed_network_out'
          observed_old_app_out'
          observed_app_out' /\
        (DriverWorkflowOk == DriverWorkflowOk ==>
          st_observed == st1 /\ Seq.equal observed_app_out' app_out) /\
        (DriverWorkflowOk == DriverWorkflowClosed ==>
          st_observed == st1 /\
          st1.CS.cs_model.CS.model_control == CS.ControlClosed /\
          buffer_resp.CT.response.CT.app_out_len == 0sz)
      with st_network st_before observed_input
           observed_old_network_out observed_network_out
           observed_old_app_out observed_app_out and ()
    end
  )

noextract
let lemma_receive_observation_reclassify_failed
  (st0 st_network st_final:CS.connection_state)
  (network_app_out final_app_out:B.bytes)
  (network_observation failed_observation:client_receive_observation)
  : Lemma
      (requires
        network_observation.client_receive_observed_status ==
          DriverWorkflowOk /\
        failed_observation.client_receive_observed_status ==
          DriverWorkflowStepFailed /\
        failed_observation.client_receive_observed_response ==
          network_observation.client_receive_observed_response /\
        client_receive_observation_network_correct
          st0 st_network network_observation network_app_out)
      (ensures
        client_receive_observation_network_correct
          st0 st_final failed_observation final_app_out)
=
  ()

noextract
let lemma_receive_observation_reclassify_closed
  (st0 st_network:CS.connection_state)
  (app_out:B.bytes)
  (network_observation closed_observation:client_receive_observation)
  : Lemma
      (requires
        network_observation.client_receive_observed_status ==
          DriverWorkflowOk /\
        closed_observation.client_receive_observed_status ==
          DriverWorkflowClosed /\
        closed_observation.client_receive_observed_response ==
          network_observation.client_receive_observed_response /\
        client_receive_observation_network_correct
          st0 st_network network_observation app_out /\
        st_network.CS.cs_model.CS.model_control == CS.ControlClosed /\
        closed_observation.client_receive_observed_response
          .CT.response.CT.app_out_len == 0sz)
      (ensures
        client_receive_observation_network_correct
          st0 st_network closed_observation app_out)
=
  ()

inline_for_extraction
let empty_receive_response () : CT.client_buffer_response =
  {
    CT.response = {
      CT.network_out_len = 0sz;
      CT.app_out_len = 0sz;
      CT.status = CT.NeedMoreInput;
    };
    CT.consumed_len = 0sz;
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

let lemma_control_snapshot_not_failed
  (snapshot:CR.control_snapshot)
  (st:CS.connection_state)
  : Lemma
      (requires
        CR.control_snapshot_matches snapshot st /\
        snapshot.CR.snapshot_control_tag <> 5uy)
      (ensures CT.connection_control_not_failed st)
=
  match st.CS.cs_model.CS.model_control with
  | CS.ControlFailed _ ->
    assert (U8.v snapshot.CR.snapshot_control_tag == 5);
    assert False
  | CS.ControlNew
  | CS.ControlHandshaking _
  | CS.ControlApplicationData
  | CS.ControlClosing
  | CS.ControlClosed ->
    ()

#push-options "--z3rlimit 20 --split_queries always --z3seed 17"
fn rec receive_application_data
  (d:top_driver)
  (empty_payload:array U8.t)
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
  (fuel:SZ.t)
  requires
    top_driver_exactly d 'st0 'buffered buffered_len **
    pts_to empty_payload 'empty_payload_bytes **
    pts_to network_out 'old_network_out **
    pts_to auth_leaf_der 'old_auth_leaf_der **
    pts_to auth_payload 'old_auth_payload **
    pts_to auth_cv_input 'old_auth_cv_input **
    pts_to auth_signature 'old_auth_signature **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'buffered == SZ.v buffered_len /\
      B.length 'empty_payload_bytes == 0 /\
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
      L.max_record_fragment_len <= SZ.v app_out_len) **
    pure (CT.connection_control_not_failed 'st0)
  returns result:receive_workflow_result
  ensures
    exists* st1 buffered_after network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
      top_driver_exactly
        d st1 buffered_after result.receive_workflow_pending_len **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to auth_leaf_der auth_leaf_der_bytes **
      pts_to auth_payload auth_payload_bytes **
      pts_to auth_cv_input auth_cv_input_bytes **
      pts_to auth_signature auth_signature_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length buffered_after == SZ.v result.receive_workflow_pending_len /\
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length auth_leaf_der_bytes == SZ.v auth_leaf_der_len /\
        B.length auth_payload_bytes == SZ.v certificate_public_key_len /\
        B.length auth_cv_input_bytes == SZ.v auth_cv_input_len /\
        B.length auth_signature_bytes == SZ.v auth_signature_len /\
        B.length app_out_bytes == SZ.v app_out_len /\
        st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config /\
        client_receive_observation_network_correct
          'st0
          st1
          (receive_workflow_observation result)
          app_out_bytes /\
        receive_workflow_application_log
          'st0 st1 result app_out_bytes /\
        (CT.client_end_to_end_invariant 'st0 ==>
         CT.client_end_to_end_invariant st1) /\
        ((result.receive_workflow_status <> DriverWorkflowStepFailed /\
          result.receive_workflow_status <> DriverWorkflowClosed) ==>
          CT.connection_control_not_failed st1))
  decreases (SZ.v fuel)
{
  if (fuel = 0sz) {
    let result = {
      receive_workflow_status = DriverWorkflowExhausted;
      receive_workflow_pending_len = buffered_len;
      receive_workflow_response = empty_receive_response ();
    };
    assert (pure (
      result.receive_workflow_status == DriverWorkflowExhausted));
    assert (pure (
      result.receive_workflow_pending_len == buffered_len));
    assert (pure (client_receive_observation_network_correct
      'st0
      'st0
      (receive_workflow_observation result)
      (Ghost.reveal 'old_app_out)));
    assert (pure (receive_workflow_application_log
      'st0
      'st0
      result
      (Ghost.reveal 'old_app_out)));
    rewrite
      (top_driver_exactly d 'st0 'buffered buffered_len)
      as
      (top_driver_exactly
        d 'st0 'buffered result.receive_workflow_pending_len);
    result
  } else {
    assert (pure (0 < SZ.v fuel));
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
    assert (pure (BN.completed_drive_correct
      'st0
      st_network
      (Ghost.reveal 'old_network_out)
      network_out_network
      (Ghost.reveal 'old_app_out)
      app_out_network
      network));
    match network.BN.completed_drive_outcome {
      BS.DriveExhausted -> {
        let result = {
          receive_workflow_status = DriverWorkflowExhausted;
          receive_workflow_pending_len =
            network.BN.completed_drive_pending_len;
          receive_workflow_response = empty_receive_response ();
        };
        assert (pure (
          result.receive_workflow_status == DriverWorkflowExhausted));
        assert (pure (
          result.receive_workflow_pending_len ==
            network.BN.completed_drive_pending_len));
        assert (pure (st_network == 'st0));
        assert (pure (Seq.equal
          app_out_network
          (Ghost.reveal 'old_app_out)));
        Seq.lemma_eq_elim
          app_out_network
          (Ghost.reveal 'old_app_out);
        assert (pure (client_receive_observation_network_correct
          'st0
          st_network
          (receive_workflow_observation result)
          app_out_network));
        assert (pure (receive_workflow_application_log
          'st0 st_network result app_out_network));
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
            result.receive_workflow_pending_len);
        result
      }
      BS.DriveProgress _ _ _ -> {
        assert (pure False);
        let result = {
          receive_workflow_status = DriverWorkflowStepFailed;
          receive_workflow_pending_len =
            network.BN.completed_drive_pending_len;
          receive_workflow_response = empty_receive_response ();
        };
        assert (pure (
          result.receive_workflow_pending_len ==
            network.BN.completed_drive_pending_len));
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
            result.receive_workflow_pending_len);
        result
      }
      BS.DriveBufferFull _ _ -> {
        assert (pure False);
        let result = {
          receive_workflow_status = DriverWorkflowStepFailed;
          receive_workflow_pending_len =
            network.BN.completed_drive_pending_len;
          receive_workflow_response = empty_receive_response ();
        };
        assert (pure (
          result.receive_workflow_pending_len ==
            network.BN.completed_drive_pending_len));
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
            result.receive_workflow_pending_len);
        result
      }
      BS.DriveReject network_result error _ -> {
        let buffer_resp =
          network_result.buffered_network_read.network_read_buffer_resp;
        let result = {
          receive_workflow_status = DriverWorkflowStepFailed;
          receive_workflow_pending_len =
            network.BN.completed_drive_pending_len;
          receive_workflow_response = buffer_resp;
        };
        assert (pure (D.drained_network_bytes_end_to_end_correct
          'st0
          st_network
          buffer_resp
          (Ghost.reveal
            network_result.buffered_network_read.network_read_prefix)
          (Ghost.reveal 'old_network_out)
          network_out_network
          (Ghost.reveal 'old_app_out)
          app_out_network));
        assert (pure (
          result.receive_workflow_status == DriverWorkflowStepFailed));
        assert (pure (
          (receive_workflow_observation result)
            .client_receive_observed_status ==
              DriverWorkflowStepFailed));
        assert (pure (
          (receive_workflow_observation result)
            .client_receive_observed_status <> DriverWorkflowOk));
        assert (pure (
          (receive_workflow_observation result)
            .client_receive_observed_status <> DriverWorkflowClosed));
        assert (pure (
          (receive_workflow_observation result)
            .client_receive_observed_response == buffer_resp));
        assert (pure (D.drained_network_bytes_end_to_end_correct
          'st0
          st_network
          (receive_workflow_observation result)
            .client_receive_observed_response
          (Ghost.reveal
            network_result.buffered_network_read.network_read_prefix)
          (Ghost.reveal 'old_network_out)
          network_out_network
          (Ghost.reveal 'old_app_out)
          app_out_network));
        assert (pure (exists st_observed st_before input
                            old_network_out observed_network_out
                            old_app_out observed_app_out.
          D.drained_network_bytes_end_to_end_correct
            st_before
            st_observed
            (receive_workflow_observation result)
              .client_receive_observed_response
            input
            old_network_out
            observed_network_out
            old_app_out
            observed_app_out));
        assert (pure (exists st_observed st_before input
                            old_network_out observed_network_out
                            old_app_out observed_app_out.
          D.drained_network_bytes_end_to_end_correct
            st_before
            st_observed
            (receive_workflow_observation result)
              .client_receive_observed_response
            input
            old_network_out
            observed_network_out
            old_app_out
            observed_app_out /\
          ((receive_workflow_observation result)
              .client_receive_observed_status == DriverWorkflowOk ==>
            st_observed == st_network /\
            Seq.equal observed_app_out app_out_network) /\
          ((receive_workflow_observation result)
              .client_receive_observed_status == DriverWorkflowClosed ==>
            st_observed == st_network /\
            st_network.CS.cs_model.CS.model_control == CS.ControlClosed /\
            (receive_workflow_observation result)
              .client_receive_observed_response.CT.response.CT.app_out_len ==
                0sz)));
        assert (pure (client_receive_observation_network_correct
          'st0
          st_network
          (receive_workflow_observation result)
          app_out_network));
        CChannel.lemma_network_bytes_application_log
          'st0
          st_network
          buffer_resp
          (Ghost.reveal
            network_result.buffered_network_read.network_read_prefix)
          (Ghost.reveal 'old_network_out)
          network_out_network
          (Ghost.reveal 'old_app_out)
          app_out_network;
        BN.lemma_completed_drive_reject_app_out_zero
          'st0
          st_network
          (Ghost.reveal 'old_network_out)
          network_out_network
          (Ghost.reveal 'old_app_out)
          app_out_network
          network;
        assert (pure (
          SZ.v buffer_resp.CT.response.CT.app_out_len == 0));
        Seq.lemma_len_slice app_out_network 0 0;
        assert (pure (
          B.length
            (CT.response_app_out buffer_resp.CT.response app_out_network) ==
            0));
        assert (pure (
          result.receive_workflow_pending_len ==
            network.BN.completed_drive_pending_len));
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
            result.receive_workflow_pending_len);
        result
      }
      BS.DriveYield network_result _ _ _ -> {
        let buffer_resp =
          network_result.buffered_network_read.network_read_buffer_resp;
        assert (pure (D.drained_network_bytes_end_to_end_correct
          'st0
          st_network
          buffer_resp
          (Ghost.reveal
            network_result.buffered_network_read.network_read_prefix)
          (Ghost.reveal 'old_network_out)
          network_out_network
          (Ghost.reveal 'old_app_out)
          app_out_network));
        let proof_observation : erased client_receive_observation =
          Ghost.hide {
            client_receive_observed_status = DriverWorkflowOk;
            client_receive_observed_response = buffer_resp;
          };
        lemma_receive_observation_network_ok
          'st0
          st_network
          buffer_resp
          (Ghost.reveal
            network_result.buffered_network_read.network_read_prefix)
          (Ghost.reveal 'old_network_out)
          network_out_network
          (Ghost.reveal 'old_app_out)
          app_out_network;
        assert (pure (client_receive_observation_network_correct
          'st0
          st_network
          (Ghost.reveal proof_observation)
          app_out_network));
        CChannel.lemma_receive_observation_app_out_length
          'st0
          st_network
          (Ghost.reveal proof_observation)
          app_out_network;
        CChannel.lemma_network_bytes_application_log
          'st0
          st_network
          buffer_resp
          (Ghost.reveal
            network_result.buffered_network_read.network_read_prefix)
          (Ghost.reveal 'old_network_out)
          network_out_network
          (Ghost.reveal 'old_app_out)
          app_out_network;
        let has_application_data =
          buffer_resp.CT.response.CT.app_out_len <> 0sz;
        if has_application_data {
          assert (pure (
            SZ.v buffer_resp.CT.response.CT.app_out_len > 0));
          D.lemma_drained_network_app_out_positive_not_failed
            'st0
            st_network
            buffer_resp
            (Ghost.reveal
              network_result.buffered_network_read.network_read_prefix)
            (Ghost.reveal 'old_network_out)
            network_out_network
            (Ghost.reveal 'old_app_out)
            app_out_network;
          let result = {
            receive_workflow_status = DriverWorkflowOk;
            receive_workflow_pending_len =
              network.BN.completed_drive_pending_len;
            receive_workflow_response = buffer_resp;
          };
          assert (pure (
            result.receive_workflow_pending_len ==
              network.BN.completed_drive_pending_len));
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
              result.receive_workflow_pending_len);
          result
        } else {
          assert (pure (
            buffer_resp.CT.response.CT.app_out_len == 0sz));
          assert (pure (
            B.length
              (CT.response_app_out
                buffer_resp.CT.response
                app_out_network) == 0));
          unfold (top_driver_exactly
            d
            st_network
            buffered_network
            network.BN.completed_drive_pending_len);
          let snapshot =
            driver_control_snapshot d.top_driver_core;
          assert (pure (
            CR.control_snapshot_matches snapshot st_network));
          fold (top_driver_exactly
            d
            st_network
            buffered_network
            network.BN.completed_drive_pending_len);
          let closed = snapshot.CR.snapshot_control_tag = 4uy;
          if closed {
            lemma_control_snapshot_closed snapshot st_network;
            let result = {
              receive_workflow_status = DriverWorkflowClosed;
              receive_workflow_pending_len =
                network.BN.completed_drive_pending_len;
              receive_workflow_response = buffer_resp;
            };
            assert (pure (
              result.receive_workflow_status == DriverWorkflowClosed));
            lemma_receive_observation_reclassify_closed
              'st0
              st_network
              app_out_network
              (Ghost.reveal proof_observation)
              (receive_workflow_observation result);
            assert (pure (client_receive_observation_network_correct
              'st0
              st_network
              (receive_workflow_observation result)
              app_out_network));
            assert (pure (receive_workflow_application_log
              'st0 st_network result app_out_network));
            assert (pure (
              result.receive_workflow_pending_len ==
                network.BN.completed_drive_pending_len));
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
                result.receive_workflow_pending_len);
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
              assert (
                top_driver_exactly
                  d
                  st_local
                  buffered_network
                  network.BN.completed_drive_pending_len **
                pts_to network_out network_out_local **
                pts_to auth_leaf_der auth_leaf_der_local **
                pts_to auth_payload auth_payload_local **
                pts_to auth_cv_input auth_cv_input_local **
                pts_to auth_signature auth_signature_local **
                pts_to app_out app_out_local);
            let local_processed = local.ready_local_processed;
            let local_ready =
              local.ready_local_action.CT.next_local_ready;
            let local_ok =
              local.ready_local_resp.CT.status = CT.StepOk;
            let local_wrote_all =
              local.ready_local_written =
                local.ready_local_resp.CT.network_out_len;
            unfold (top_driver_exactly
              d
              st_local
              buffered_network
              network.BN.completed_drive_pending_len);
            let local_snapshot =
              driver_control_snapshot d.top_driver_core;
            assert (pure (
              CR.control_snapshot_matches local_snapshot st_local));
            fold (top_driver_exactly
              d
              st_local
              buffered_network
              network.BN.completed_drive_pending_len);
            let local_control_failed =
              local_snapshot.CR.snapshot_control_tag = 5uy;
            let local_failed =
              (local_processed &&
                ((local_ok = false) || (local_wrote_all = false))) ||
              ((local_processed = false) && local_ready) ||
              local_control_failed;
            if local_failed {
              let result = {
                receive_workflow_status = DriverWorkflowStepFailed;
                receive_workflow_pending_len =
                  network.BN.completed_drive_pending_len;
                receive_workflow_response = buffer_resp;
              };
              lemma_receive_observation_reclassify_failed
                'st0
                st_network
                st_local
                app_out_network
                app_out_local
                (Ghost.reveal proof_observation)
                (receive_workflow_observation result);
              assert (pure (client_receive_observation_network_correct
                'st0
                st_local
                (receive_workflow_observation result)
                app_out_local));
              assert (pure (
                result.receive_workflow_pending_len ==
                  network.BN.completed_drive_pending_len));
              rewrite
                (top_driver_exactly
                  d
                  st_local
                  buffered_network
                  network.BN.completed_drive_pending_len)
                as
                (top_driver_exactly
                  d
                  st_local
                  buffered_network
                  result.receive_workflow_pending_len);
              result
            } else {
              assert (pure (
                local_snapshot.CR.snapshot_control_tag <> 5uy));
              lemma_control_snapshot_not_failed
                local_snapshot st_local;
              let next_fuel = SZ.sub fuel 1sz;
              assert (pure (SZ.v next_fuel < SZ.v fuel));
              receive_application_data
                d
                empty_payload
                network.BN.completed_drive_pending_len
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
                next_fuel
            }
          }
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
           pure (B.length 'old_out == SZ.v out_len /\
                 L.max_record_fragment_len <= SZ.v out_len) **
           pure (CT.connection_control_not_failed 'st0)
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
                TChannel.application_log st1 ==
                  (if result.client_receive_status == DriverWorkflowOk
                   then
                     CI.append_received
                       (TChannel.application_log 'st0)
                       (Seq.slice
                         out_bytes
                         0
                         (SZ.v result.client_receive_len))
                   else TChannel.application_log 'st0) /\
                (exists obs app_out.
                  client_driver_receive_correct
                   'st0
                   st1
                    result
                    obs
                    app_out
                    out_bytes) /\
                ((result.client_receive_status <> DriverWorkflowStepFailed /\
                  result.client_receive_status <> DriverWorkflowClosed) ==>
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
  V.to_array_pts_to d.client_driver_auth_leaf_der;
  V.to_array_pts_to d.client_driver_auth_payload;
  V.to_array_pts_to d.client_driver_auth_cv_input;
  V.to_array_pts_to d.client_driver_auth_signature;
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
    receive_application_data
      td
      (V.vec_to_array d.client_driver_empty_payload)
      concrete_buffered_len
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
      out
      out_len
      fuel;
  with st1 buffered_after network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes out_bytes.
    assert (
      top_driver_exactly
        td st1 buffered_after workflow.receive_workflow_pending_len **
      pts_to
        (V.vec_to_array d.client_driver_empty_payload)
        empty_payload **
      pts_to
        (V.vec_to_array d.client_driver_network_out)
        network_out_bytes **
      pts_to
        (V.vec_to_array d.client_driver_auth_leaf_der)
        auth_leaf_der_bytes **
      pts_to
        (V.vec_to_array d.client_driver_auth_payload)
        auth_payload_bytes **
      pts_to
        (V.vec_to_array d.client_driver_auth_cv_input)
        auth_cv_input_bytes **
      pts_to
        (V.vec_to_array d.client_driver_auth_signature)
        auth_signature_bytes **
      pts_to out out_bytes);
  V.to_vec_pts_to d.client_driver_empty_payload;
  V.to_vec_pts_to d.client_driver_network_out;
  V.to_vec_pts_to d.client_driver_auth_leaf_der;
  V.to_vec_pts_to d.client_driver_auth_payload;
  V.to_vec_pts_to d.client_driver_auth_cv_input;
  V.to_vec_pts_to d.client_driver_auth_signature;
  let observation : erased client_receive_observation =
    Ghost.hide (receive_workflow_observation workflow);
  CChannel.lemma_receive_observation_app_out_length
    'st0 st1 (Ghost.reveal observation) out_bytes;
  let workflow_ok =
    workflow.receive_workflow_status = DriverWorkflowOk;
  let response = workflow.receive_workflow_response.CT.response;
  let app_fits = SZ.lte response.CT.app_out_len out_len;
  assert (pure (workflow_ok ==> app_fits == true));
  let result = {
    client_receive_status =
      if workflow_ok
      then DriverWorkflowOk
      else workflow.receive_workflow_status;
    client_receive_len =
      if workflow_ok then response.CT.app_out_len else 0sz;
  };
  assert (pure (client_driver_receive_status_correct
    result (Ghost.reveal observation) out_bytes out_bytes));
  assert (pure (client_driver_receive_correct
    'st0 st1 result (Ghost.reveal observation) out_bytes out_bytes));
  if workflow_ok {
    assert (pure (
      result.client_receive_status == DriverWorkflowOk));
    assert (pure (
      result.client_receive_len == response.CT.app_out_len));
    assert (pure (Seq.equal
      (CT.response_app_out response out_bytes)
      (Seq.slice out_bytes 0 (SZ.v result.client_receive_len))));
    assert (pure (
      TChannel.application_log st1 ==
        CI.append_received
          (TChannel.application_log 'st0)
          (Seq.slice
            out_bytes
            0
            (SZ.v result.client_receive_len))))
  } else {
    assert (pure (
      result.client_receive_status ==
        workflow.receive_workflow_status));
    assert (pure (result.client_receive_len == 0sz));
    assert (pure (
      TChannel.application_log st1 ==
        TChannel.application_log 'st0))
  };
  unfold (top_driver_exactly
    td st1 buffered_after workflow.receive_workflow_pending_len);
  unfold (driver_exactly
    td.top_driver_core
    st1
    buffered_after
    workflow.receive_workflow_pending_len);
  rewrite
    (buffered_driver_exactly
      (driver_as_buffered td.top_driver_core)
      st1
      buffered_after
      workflow.receive_workflow_pending_len)
    as
    (buffered_driver_exactly
      (client_buffered_driver d concrete_channel)
      st1
      buffered_after
      workflow.receive_workflow_pending_len);
  unfold (buffered_driver_exactly
    (client_buffered_driver d concrete_channel)
    st1
    buffered_after
    workflow.receive_workflow_pending_len);
  with model1 received1 committed1 sent1.
    assert (buffered_driver_indexed
      (client_buffered_driver d concrete_channel)
      st1
      buffered_after
      workflow.receive_workflow_pending_len
      model1
      received1
      committed1
      sent1);
  unfold (buffered_driver_indexed
    (client_buffered_driver d concrete_channel)
    st1
    buffered_after
    workflow.receive_workflow_pending_len
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
    buffered_after
    workflow.receive_workflow_pending_len));
  assert (pure (client_driver_wire_logs_match
    st1
    received1
    sent1
    buffered_after
    workflow.receive_workflow_pending_len));
  lemma_client_driver_wire_logs_match_received_accounted
    st1
    received1
    sent1
    buffered_after
    workflow.receive_workflow_pending_len;
  assert (pure (Seq.equal (BT.pending model1) buffered_after));
  Seq.lemma_eq_elim (BT.pending model1) buffered_after;
  fold (buffered_driver_indexed
    (client_buffered_driver d concrete_channel)
    st1
    (BT.pending model1)
    workflow.receive_workflow_pending_len
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
    workflow.receive_workflow_pending_len);
  fold (client_driver_connected d st1 received1 sent1);
  result
}
