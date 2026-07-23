module TLS13.Impl.Server.Driver.BufferedReceive

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BC = TLS13.Impl.Server.Driver.BufferedChannel
module BN = TLS13.Impl.Server.Driver.BufferedNetwork
module BS = Common.BufferedStream
module BT = Common.BufferedTCP
module CI = Common.ChannelImplementation
module CQ = TLS13.Impl.ConnectionState.Queries
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module ID = FStar.IndefiniteDescription
module IM = TLS13.Impl.Messages
module S = TLS13.Impl.Server
module Seq = FStar.Seq
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module Box = Pulse.Lib.Box

noeq type receive_loop_result = {
  loop_status: receive_status;
  loop_len: SZ.t;
}

let receive_status_reusable (status:receive_status) : bool =
  match status with
  | BufferedReceiveOk
  | BufferedReceiveExhausted
  | BufferedReceiveOutputBufferTooSmall -> true
  | BufferedReceiveClosed
  | BufferedReceiveFailed -> false

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
  | CS.ControlClosed -> ()
  | _ -> assert False

fn query_control
  (d:DS.top_server_driver)
  requires
    DS.top_server_driver_connected
      d 'st 'certificate_chain 'credential_identity 'received 'sent
  returns snapshot:CR.control_snapshot
  ensures
    DS.top_server_driver_connected
      d 'st 'certificate_chain 'credential_identity 'received 'sent **
    pure (CR.control_snapshot_matches snapshot 'st)
{
  unfold (DS.top_server_driver_connected
    d 'st 'certificate_chain 'credential_identity 'received 'sent);
  with channel model committed buffered_len.
    unfold (DS.top_server_driver_connected_indexed
      d 'st 'certificate_chain 'credential_identity
      'received 'sent channel model committed buffered_len);
  unfold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d channel)
    'st 'certificate_chain 'credential_identity
    (BT.pending model) buffered_len model
    'received committed 'sent);
  rewrite
    (S.connection_exactly d.top_server_driver_server 'st)
    as
    (CR.connection_exactly d.top_server_driver_server 'st);
  let snapshot = CQ.get_control_snapshot d.top_server_driver_server;
  rewrite
    (CR.connection_exactly d.top_server_driver_server 'st)
    as
    (S.connection_exactly d.top_server_driver_server 'st);
  fold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d channel)
    'st 'certificate_chain 'credential_identity
    (BT.pending model) buffered_len model
    'received committed 'sent);
  fold (DS.top_server_driver_connected_indexed
    d 'st 'certificate_chain 'credential_identity
    'received 'sent channel model committed buffered_len);
  fold (DS.top_server_driver_connected
    d 'st 'certificate_chain 'credential_identity 'received 'sent);
  snapshot
}

fn drive_connected_once
  (d:DS.top_server_driver)
  (out:array U8.t)
  (out_len:SZ.t)
  (fuel:SZ.t)
  requires
    DS.top_server_driver_connected
      d 'st0 'certificate_chain 'credential_identity 'received0 'sent0 **
    pts_to out 'old_output **
    pure (
      B.length 'old_output == SZ.v out_len /\
      IM.max_record_fragment_len <= SZ.v out_len)
  returns result:BN.completed_drive
  ensures
    exists* st1 received1 sent1 output.
      DS.top_server_driver_connected
        d st1 'certificate_chain 'credential_identity received1 sent1 **
      pts_to out output **
      pure (
        B.length output == SZ.v out_len /\
        ST.server_end_to_end_invariant st1 /\
        (exists old_network_out network_out.
          BN.completed_drive_correct
            'st0 st1 old_network_out network_out
            'old_output output result))
{
  unfold (DS.top_server_driver_connected
    d 'st0 'certificate_chain 'credential_identity 'received0 'sent0);
  with channel model committed buffered_len.
    unfold (DS.top_server_driver_connected_indexed
      d 'st0 'certificate_chain 'credential_identity
      'received0 'sent0 channel model committed buffered_len);
  let current_channel = Box.(!d.top_server_driver_channel);
  assert (pure (current_channel == Some channel));
  let concrete_channel = Some?.v current_channel;
  assert (pure (concrete_channel == channel));
  rewrite
    (DS.buffered_driver_indexed
      (DS.top_server_as_buffered d channel)
      'st0 'certificate_chain 'credential_identity
      (BT.pending model) buffered_len model
      'received0 committed 'sent0)
    as
    (DS.buffered_driver_indexed
      (DS.top_server_as_buffered d concrete_channel)
      'st0 'certificate_chain 'credential_identity
      (BT.pending model) buffered_len model
      'received0 committed 'sent0);
  unfold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d concrete_channel)
    'st0 'certificate_chain 'credential_identity
    (BT.pending model) buffered_len model
    'received0 committed 'sent0);
  let concrete_buffered_len = BT.pending_length concrete_channel;
  fold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d concrete_channel)
    'st0 'certificate_chain 'credential_identity
    (BT.pending model) concrete_buffered_len model
    'received0 committed 'sent0);
  unfold (DS.top_server_driver_buffers d);
  with empty_payload material network_out cv_input signature app_out local_app_out.
    assert (V.pts_to
      d.top_server_driver_network_out #1.0R network_out);
  V.to_array_pts_to d.top_server_driver_network_out;
  fold (DS.buffered_driver_exactly
    (DS.top_server_as_buffered d concrete_channel)
    'st0 'certificate_chain 'credential_identity
    (BT.pending model) concrete_buffered_len);
  let result =
    BN.drive
      (DS.top_server_as_buffered d concrete_channel)
      (V.vec_to_array d.top_server_driver_network_out)
      DS.driver_network_out_capacity
      out
      out_len
      concrete_buffered_len
      fuel;
  with st1 buffered_after network_out1 output.
    assert (
      DS.buffered_driver_exactly
        (DS.top_server_as_buffered d concrete_channel)
        st1 'certificate_chain 'credential_identity
        buffered_after result.BN.completed_drive_pending_len **
      pts_to
        (V.vec_to_array d.top_server_driver_network_out)
        network_out1 **
      pts_to out output);
  unfold (DS.buffered_driver_exactly
    (DS.top_server_as_buffered d concrete_channel)
    st1 'certificate_chain 'credential_identity
    buffered_after result.BN.completed_drive_pending_len);
  with model1 received1 committed1 sent1.
    unfold (DS.buffered_driver_indexed
      (DS.top_server_as_buffered d concrete_channel)
      st1 'certificate_chain 'credential_identity
      buffered_after result.BN.completed_drive_pending_len
      model1 received1 committed1 sent1);
  assert (pure (Seq.equal (BT.pending model1) buffered_after));
  Seq.lemma_eq_elim (BT.pending model1) buffered_after;
  fold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d concrete_channel)
    st1 'certificate_chain 'credential_identity
    (BT.pending model1) result.BN.completed_drive_pending_len
    model1 received1 committed1 sent1);
  V.to_vec_pts_to d.top_server_driver_network_out;
  fold (DS.top_server_driver_buffers d);
  fold (DS.top_server_driver_connected_indexed
    d st1 'certificate_chain 'credential_identity
    received1 sent1 concrete_channel model1 committed1
    result.BN.completed_drive_pending_len);
  fold (DS.top_server_driver_connected
    d st1 'certificate_chain 'credential_identity received1 sent1);
  result
}

let lemma_received_step_ok_not_failed
  (st0 st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (input:B.bytes)
  : Lemma
      (requires
        ST.server_network_step_ok_consumed_prefix st0 st1 resp input /\
        resp.ST.response.ST.status == ST.StepOk /\
        ST.server_connection_control_not_failed st0)
      (ensures ST.server_connection_control_not_failed st1)
=
  ()

let lemma_yield_preserves_not_failed
  (st0 st1:CS.connection_state)
  (old_output output:B.bytes)
  (result:BN.completed_drive)
  : Lemma
      (requires
        ST.server_connection_control_not_failed st0 /\
        (exists old_network_out network_out.
          BN.completed_drive_correct
            st0 st1 old_network_out network_out
            old_output output result) /\
        (exists network consumed proof output.
          result.BN.completed_drive_outcome ==
            BS.DriveYield network consumed proof output))
      (ensures ST.server_connection_control_not_failed st1)
=
  let old_network_out =
    ID.indefinite_description_ghost
      B.bytes
      (fun old_network_out -> exists network_out.
        BN.completed_drive_correct
          st0 st1 old_network_out network_out old_output output result) in
  let network_out =
    ID.indefinite_description_ghost
      B.bytes
      (fun network_out ->
        BN.completed_drive_correct
          st0 st1 old_network_out network_out old_output output result) in
  match result.BN.completed_drive_outcome with
  | BS.DriveYield network _ _ _ ->
    let buffer_resp =
      network.BN.buffered_network_read.BN.network_read_buffer_resp in
    assert (ST.server_network_consumed_input_projection
      st0
      st1
      buffer_resp
      (Ghost.reveal
        network.BN.buffered_network_read.BN.network_read_prefix)
      network_out
      output);
    assert (buffer_resp.ST.response.ST.status == ST.StepOk);
    lemma_received_step_ok_not_failed
      st0
      st1
      buffer_resp
      (Ghost.reveal
        network.BN.buffered_network_read.BN.network_read_prefix)
  | _ -> assert False

#push-options "--z3refresh --z3rlimit 20 --split_queries always --z3seed 17"
fn rec receive_loop
  (d:DS.top_server_driver)
  (out:array U8.t)
  (out_len:SZ.t)
  (fuel:SZ.t)
  requires
    DS.top_server_driver_connected
      d 'st0 'certificate_chain 'credential_identity 'received0 'sent0 **
    pts_to out 'old_output **
    pure (
      B.length 'old_output == SZ.v out_len /\
      IM.max_record_fragment_len <= SZ.v out_len /\
      ST.server_connection_control_not_failed 'st0)
  returns result:receive_loop_result
  ensures
    exists* st1 received1 sent1 output.
      DS.top_server_driver_connected
        d st1 'certificate_chain 'credential_identity received1 sent1 **
      pts_to out output **
      pure (
        B.length output == SZ.v out_len /\
        SZ.v result.loop_len <= SZ.v out_len /\
        (receive_status_reusable result.loop_status ==>
          ST.server_connection_control_not_failed st1))
  decreases (SZ.v fuel)
{
  if (fuel = 0sz) {
    {
      loop_status = BufferedReceiveExhausted;
      loop_len = 0sz;
    }
  } else {
    let drive = drive_connected_once d out out_len fuel;
    with st1 received1 sent1 output.
      assert (
        DS.top_server_driver_connected
          d st1 'certificate_chain 'credential_identity received1 sent1 **
        pts_to out output);
    match drive.BN.completed_drive_outcome {
      BS.DriveExhausted -> {
        {
          loop_status = BufferedReceiveExhausted;
          loop_len = 0sz;
        }
      }
      BS.DriveReject _ _ _ -> {
        {
          loop_status = BufferedReceiveFailed;
          loop_len = 0sz;
        }
      }
      BS.DriveProgress _ _ _ -> {
        assert (pure False);
        {
          loop_status = BufferedReceiveFailed;
          loop_len = 0sz;
        }
      }
      BS.DriveBufferFull _ _ -> {
        assert (pure False);
        {
          loop_status = BufferedReceiveFailed;
          loop_len = 0sz;
        }
      }
      BS.DriveYield network consumed proof response -> {
        lemma_yield_preserves_not_failed
          'st0 st1 (Ghost.reveal 'old_output) output drive;
        let buffer_resp =
          network.BN.buffered_network_read.BN.network_read_buffer_resp;
        let application_len =
          buffer_resp.ST.response.ST.app_out_len;
        if (application_len <> 0sz) {
          assert (pure (SZ.v application_len <= SZ.v out_len));
          {
            loop_status = BufferedReceiveOk;
            loop_len = application_len;
          }
        } else {
          let control = query_control d;
          let closed = control.CR.snapshot_control_tag = 4uy;
          if closed {
            lemma_control_snapshot_closed control st1;
            {
              loop_status = BufferedReceiveClosed;
              loop_len = 0sz;
            }
          } else {
            let next_fuel = SZ.sub fuel 1sz;
            assert (pure (SZ.v next_fuel < SZ.v fuel));
            receive_loop d out out_len next_fuel
          }
        }
      }
    }
  }
}
#pop-options

fn run
  (d:DS.top_server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (out:array U8.t)
  (out_len:SZ.t)
  (network_fuel:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0) **
    pts_to out 'old_output **
    pure (B.length 'old_output == SZ.v out_len)
  returns result:receive_result
  ensures
    exists* output.
      pts_to out output **
      pure (
        B.length output == SZ.v out_len /\
        SZ.v result.receive_len <= SZ.v out_len) **
      (match result.receive_status with
       | BufferedReceiveOk
       | BufferedReceiveExhausted
       | BufferedReceiveOutputBufferTooSmall ->
         exists* wire_received1 wire_sent1 pending1 app_log1.
           DS.top_server_channel_inv
             d wire_received1 wire_sent1 pending1 app_log1
       | BufferedReceiveClosed
       | BufferedReceiveFailed ->
         exists* wire_received1 wire_sent1 app_log1.
           DS.top_server_channel_terminal
             d wire_received1 wire_sent1 app_log1)
{
  let output_fits = SZ.lte DS.driver_app_out_capacity out_len;
  if (output_fits = false) {
    {
      receive_status = BufferedReceiveOutputBufferTooSmall;
      receive_len = 0sz;
    }
  } else {
    BC.open_channel_invariant
      d wire_received0 wire_sent0 pending0 app_log0;
    with st0 certificate_chain credential_identity.
      assert (DS.top_server_driver_connected
        d st0 certificate_chain credential_identity
        (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0));
    assert (pure (IM.max_record_fragment_len <= SZ.v out_len));
    let loop = receive_loop d out out_len network_fuel;
    with st1 received1 sent1 output.
      assert (
        DS.top_server_driver_connected
          d st1 certificate_chain credential_identity received1 sent1 **
        pts_to out output);
    match loop.loop_status {
      BufferedReceiveOk -> {
        BC.pack_connected_channel
          d
          (Ghost.hide st1)
          (Ghost.hide certificate_chain)
          (Ghost.hide credential_identity)
          (Ghost.hide received1)
          (Ghost.hide sent1);
        {
          receive_status = BufferedReceiveOk;
          receive_len = loop.loop_len;
        }
      }
      BufferedReceiveExhausted -> {
        BC.pack_connected_channel
          d
          (Ghost.hide st1)
          (Ghost.hide certificate_chain)
          (Ghost.hide credential_identity)
          (Ghost.hide received1)
          (Ghost.hide sent1);
        {
          receive_status = BufferedReceiveExhausted;
          receive_len = loop.loop_len;
        }
      }
      BufferedReceiveOutputBufferTooSmall -> {
        BC.pack_connected_channel
          d
          (Ghost.hide st1)
          (Ghost.hide certificate_chain)
          (Ghost.hide credential_identity)
          (Ghost.hide received1)
          (Ghost.hide sent1);
        {
          receive_status = BufferedReceiveOutputBufferTooSmall;
          receive_len = loop.loop_len;
        }
      }
      BufferedReceiveClosed -> {
        BC.pack_connected_channel_terminal
          d
          (Ghost.hide st1)
          (Ghost.hide certificate_chain)
          (Ghost.hide credential_identity)
          (Ghost.hide received1)
          (Ghost.hide sent1);
        {
          receive_status = BufferedReceiveClosed;
          receive_len = loop.loop_len;
        }
      }
      BufferedReceiveFailed -> {
        BC.pack_connected_channel_terminal
          d
          (Ghost.hide st1)
          (Ghost.hide certificate_chain)
          (Ghost.hide credential_identity)
          (Ghost.hide received1)
          (Ghost.hide sent1);
        {
          receive_status = BufferedReceiveFailed;
          receive_len = loop.loop_len;
        }
      }
    }
  }
}
