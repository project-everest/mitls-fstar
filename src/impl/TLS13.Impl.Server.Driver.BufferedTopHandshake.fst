module TLS13.Impl.Server.Driver.BufferedTopHandshake

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module BT = Common.BufferedTCP
module BW = TLS13.Impl.Server.Driver.BufferedWorkflow
module CM = TLS13.Impl.ConnectionState.Model
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module Box = Pulse.Lib.Box
module Seq = FStar.Seq
module SZ = FStar.SizeT
module V = Pulse.Lib.Vec

fn run_connected
  (d:DS.top_server_driver)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires
    DS.top_server_driver_connected
      d
      'st0
      'certificate_chain
      'credential_identity
      'received0
      'sent0 **
    pure (CM.can_start_server 'st0)
  returns status:BW.handshake_status
  ensures
    exists* st1 received1 sent1.
      DS.top_server_driver_connected
        d
        st1
        'certificate_chain
        'credential_identity
        received1
        sent1 **
      pure (
        status == BW.HandshakeOk ==>
        st1.CS.cs_model.CS.model_control == CS.ControlApplicationData)
{
  unfold (DS.top_server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    (Ghost.reveal 'received0)
    (Ghost.reveal 'sent0));
  with channel model committed buffered_len.
    assert (DS.top_server_driver_connected_indexed
      d
      'st0
      'certificate_chain
      'credential_identity
      (Ghost.reveal 'received0)
      (Ghost.reveal 'sent0)
      channel
      model
      committed
      buffered_len);
  unfold (DS.top_server_driver_connected_indexed
    d
    'st0
    'certificate_chain
    'credential_identity
    (Ghost.reveal 'received0)
    (Ghost.reveal 'sent0)
    channel
    model
    committed
    buffered_len);
  let current_channel = Box.(!d.top_server_driver_channel);
  assert (pure (current_channel == Some channel));
  let concrete_channel = Some?.v current_channel;
  assert (pure (concrete_channel == channel));
  rewrite
    (DS.buffered_driver_indexed
      (DS.top_server_as_buffered d channel)
      'st0
      'certificate_chain
      'credential_identity
      (BT.pending model)
      buffered_len
      model
      (Ghost.reveal 'received0)
      committed
      (Ghost.reveal 'sent0))
    as
    (DS.buffered_driver_indexed
      (DS.top_server_as_buffered d concrete_channel)
      'st0
      'certificate_chain
      'credential_identity
      (BT.pending model)
      buffered_len
      model
      (Ghost.reveal 'received0)
      committed
      (Ghost.reveal 'sent0));
  unfold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d concrete_channel)
    'st0
    'certificate_chain
    'credential_identity
    (BT.pending model)
    buffered_len
    model
    (Ghost.reveal 'received0)
    committed
    (Ghost.reveal 'sent0));
  let concrete_buffered_len =
    BT.pending_length concrete_channel;
  assert (pure (SZ.v concrete_buffered_len == SZ.v buffered_len));
  fold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d concrete_channel)
    'st0
    'certificate_chain
    'credential_identity
    (BT.pending model)
    concrete_buffered_len
    model
    (Ghost.reveal 'received0)
    committed
    (Ghost.reveal 'sent0));
  unfold (DS.top_server_driver_buffers d);
  with empty_payload material network_out app_out.
    assert (
      V.pts_to d.top_server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.top_server_driver_material_payload #1.0R material **
      V.pts_to d.top_server_driver_network_out #1.0R network_out **
      V.pts_to d.top_server_driver_app_out #1.0R app_out);
  V.to_array_pts_to d.top_server_driver_empty_payload;
  V.to_array_pts_to d.top_server_driver_material_payload;
  V.to_array_pts_to d.top_server_driver_network_out;
  V.to_array_pts_to d.top_server_driver_app_out;
  fold (DS.buffered_driver_exactly
    (DS.top_server_as_buffered d concrete_channel)
    'st0
    'certificate_chain
    'credential_identity
    (BT.pending model)
    concrete_buffered_len);
  let result =
    BW.run
      (DS.top_server_as_buffered d concrete_channel)
      (V.vec_to_array d.top_server_driver_empty_payload)
      (V.vec_to_array d.top_server_driver_material_payload)
      (V.vec_to_array d.top_server_driver_network_out)
      DS.driver_network_out_capacity
      (V.vec_to_array d.top_server_driver_app_out)
      DS.driver_app_out_capacity
      concrete_buffered_len
      local_fuel
      network_fuel;
  with st1 buffered_after material_after network_out_after app_out_after.
    assert (
      DS.buffered_driver_exactly
        (DS.top_server_as_buffered d concrete_channel)
        st1
        'certificate_chain
        'credential_identity
        buffered_after
        result.BW.handshake_pending_len **
      pts_to
        (V.vec_to_array d.top_server_driver_empty_payload)
        empty_payload **
      pts_to
        (V.vec_to_array d.top_server_driver_material_payload)
        material_after **
      pts_to
        (V.vec_to_array d.top_server_driver_network_out)
        network_out_after **
      pts_to
        (V.vec_to_array d.top_server_driver_app_out)
        app_out_after);
  unfold (DS.buffered_driver_exactly
    (DS.top_server_as_buffered d concrete_channel)
    st1
    'certificate_chain
    'credential_identity
    buffered_after
    result.BW.handshake_pending_len);
  with model1 received1 committed1 sent1.
    assert (DS.buffered_driver_indexed
      (DS.top_server_as_buffered d concrete_channel)
      st1
      'certificate_chain
      'credential_identity
      buffered_after
      result.BW.handshake_pending_len
      model1
      received1
      committed1
      sent1);
  unfold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d concrete_channel)
    st1
    'certificate_chain
    'credential_identity
    buffered_after
    result.BW.handshake_pending_len
    model1
    received1
    committed1
    sent1);
  assert (pure (Seq.equal (BT.pending model1) buffered_after));
  Seq.lemma_eq_elim (BT.pending model1) buffered_after;
  fold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d concrete_channel)
    st1
    'certificate_chain
    'credential_identity
    (BT.pending model1)
    result.BW.handshake_pending_len
    model1
    received1
    committed1
    sent1);
  V.to_vec_pts_to d.top_server_driver_empty_payload;
  V.to_vec_pts_to d.top_server_driver_material_payload;
  V.to_vec_pts_to d.top_server_driver_network_out;
  V.to_vec_pts_to d.top_server_driver_app_out;
  fold (DS.top_server_driver_buffers d);
  fold (DS.top_server_driver_connected_indexed
    d
    st1
    'certificate_chain
    'credential_identity
    received1
    sent1
    concrete_channel
    model1
    committed1
    result.BW.handshake_pending_len);
  fold (DS.top_server_driver_connected
    d
    st1
    'certificate_chain
    'credential_identity
    received1
    sent1);
  result.BW.handshake_status
}
