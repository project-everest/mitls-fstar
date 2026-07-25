module TLS13.Impl.Client.Driver.Cleanup

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
open TLS13.Impl.Client.Driver.State
inline_for_extraction
fn free_client_driver_buffers
  (d:client_driver)
  requires client_driver_buffers d
  ensures emp
{
  unfold (client_driver_buffers d);
  with empty_payload network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out local_app_out.
    assert (V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
            V.pts_to d.client_driver_network_out #1.0R network_out **
            V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
            V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
            V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
            V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
            V.pts_to d.client_driver_app_out #1.0R app_out **
            V.pts_to d.client_driver_local_app_out #1.0R local_app_out);
  V.free d.client_driver_empty_payload;
  V.free d.client_driver_network_out;
  V.free d.client_driver_auth_leaf_der;
  V.free d.client_driver_auth_payload;
  V.free d.client_driver_auth_cv_input;
  V.free d.client_driver_auth_signature;
  V.free d.client_driver_app_out;
  V.free d.client_driver_local_app_out;
}

inline_for_extraction
fn free_disconnected_client_driver
  (d:client_driver)
  requires C.connection_exactly d.client_driver_client 'st0 **
           client_driver_canonical_progress d 'st0 **
           O.is_auth_context d.client_driver_auth **
           Box.pts_to d.client_driver_channel no_channel **
           (exists* h. MR.pts_to d.client_driver_tcp_history #1.0R h) **
           client_driver_buffers d **
           (exists* model. BT.is_storage d.client_driver_storage model)
  ensures client_driver_closed d 'st0
{
  with model.
    assert (BT.is_storage d.client_driver_storage model);
  BT.free_storage d.client_driver_storage;
  O.auth_context_free d.client_driver_auth;
  Box.free d.client_driver_channel;
  free_client_driver_buffers d;
  fold (client_driver_closed d 'st0);
}

inline_for_extraction
fn close_failed_connect
  (d:client_driver)
  (channel:BT.t)
  requires top_buffered_driver_exactly
             (client_top_buffered_driver d channel)
             'st0
             'buffered
             'buffered_len **
           Box.pts_to d.client_driver_channel no_channel **
           client_driver_buffers d
  ensures client_driver_closed d 'st0
{
  unfold (top_buffered_driver_exactly
    (client_top_buffered_driver d channel)
    'st0
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'buffered_len));
  unfold (buffered_driver_exactly
    (client_buffered_driver d channel)
    'st0
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'buffered_len));
  with model received committed sent.
    assert (buffered_driver_indexed
      (client_buffered_driver d channel)
      'st0
      (Ghost.reveal 'buffered)
      (Ghost.reveal 'buffered_len)
      model
      received
      committed
      sent);
  unfold (buffered_driver_indexed
    (client_buffered_driver d channel)
    'st0
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'buffered_len)
    model
    received
    committed
    sent);
  let storage = BT.close_detach channel;
  with storage_model.
    assert (BT.is_storage storage storage_model);
  BT.lemma_same_storage_unique
    channel
    d.client_driver_storage
    storage;
  rewrite (BT.is_storage storage storage_model) as
    (BT.is_storage d.client_driver_storage storage_model);
  rewrite
    (buffered_driver_canonical_progress
      (client_buffered_driver d channel)
      'st0)
    as
    (client_driver_canonical_progress d 'st0);
  free_disconnected_client_driver d;
}

inline_for_extraction
fn close_connected_client_driver
  (d:DS.client_driver)
  requires DS.client_driver_connected d 'st0 'received 'sent
  ensures DS.client_driver_closed d 'st0
{
  unfold (DS.client_driver_connected
    d
    (Ghost.reveal 'st0)
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent));
  with channel model committed buffered_len.
    assert (DS.client_driver_connected_indexed
      d
      (Ghost.reveal 'st0)
      (Ghost.reveal 'received)
      (Ghost.reveal 'sent)
      channel
      model
      committed
      buffered_len);
  unfold (DS.client_driver_connected_indexed
    d
    (Ghost.reveal 'st0)
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent)
    channel
    model
    committed
    buffered_len);
  let current_channel = Box.(!d.DS.client_driver_channel);
  assert (pure (current_channel == Some channel));
  assert (pure (Some? current_channel));
  let concrete_channel = Some?.v current_channel;
  assert (pure (concrete_channel == channel));
  rewrite
    (DS.buffered_driver_indexed
      (DS.client_buffered_driver d channel)
      (Ghost.reveal 'st0)
      (BT.pending model)
      buffered_len
      model
      (Ghost.reveal 'received)
      committed
      (Ghost.reveal 'sent))
    as
    (DS.buffered_driver_indexed
      (DS.client_buffered_driver d concrete_channel)
      (Ghost.reveal 'st0)
      (BT.pending model)
      buffered_len
      model
      (Ghost.reveal 'received)
      committed
      (Ghost.reveal 'sent));
  unfold (DS.buffered_driver_indexed
    (DS.client_buffered_driver d concrete_channel)
    (Ghost.reveal 'st0)
    (BT.pending model)
    buffered_len
    model
    (Ghost.reveal 'received)
    committed
    (Ghost.reveal 'sent));
  let detached = BT.close_detach concrete_channel;
  with detached_model.
    assert (BT.is_storage detached detached_model);
  assert (pure (BT.same_storage
    concrete_channel
    d.DS.client_driver_storage));
  assert (pure (BT.same_storage concrete_channel detached));
  BT.lemma_same_storage_unique
    concrete_channel
    d.DS.client_driver_storage
    detached;
  assert (pure (detached == d.DS.client_driver_storage));
  rewrite (BT.is_storage detached detached_model) as
    (BT.is_storage d.DS.client_driver_storage detached_model);
  Box.(d.DS.client_driver_channel := DS.no_channel);
  rewrite
    (DS.buffered_driver_canonical_progress
      (DS.client_buffered_driver d concrete_channel)
      (Ghost.reveal 'st0))
    as
    (DS.client_driver_canonical_progress d (Ghost.reveal 'st0));
  free_disconnected_client_driver d
}
