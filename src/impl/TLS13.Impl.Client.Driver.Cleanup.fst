module TLS13.Impl.Client.Driver.Cleanup

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
open TLS13.Impl.Client.Driver.State
inline_for_extraction
fn free_client_driver_buffers
  (d:client_driver)
  (buffered_len:SZ.t)
  requires (exists* buffered. client_driver_buffers d buffered buffered_len)
  ensures emp
{
  with buffered.
    assert (client_driver_buffers d buffered buffered_len);
  unfold (client_driver_buffers d buffered buffered_len);
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
  V.free d.client_driver_empty_payload;
  V.free d.client_driver_raw;
  V.free d.client_driver_network_out;
  V.free d.client_driver_auth_leaf_der;
  V.free d.client_driver_auth_payload;
  V.free d.client_driver_auth_cv_input;
  V.free d.client_driver_auth_signature;
  V.free d.client_driver_app_out;
  V.free d.client_driver_local_app_out;
  Box.free d.client_driver_buffered_len;
}

inline_for_extraction
fn free_disconnected_client_driver
  (d:client_driver)
  (buffered_len:SZ.t)
  requires C.connection_exactly d.client_driver_client 'st0 **
           client_driver_canonical_progress d 'st0 **
           O.is_auth_context d.client_driver_auth **
           Box.pts_to d.client_driver_channel no_channel **
           (exists* h. MR.pts_to d.client_driver_tcp_history #1.0R h) **
           (exists* buffered. client_driver_buffers d buffered buffered_len)
  ensures client_driver_closed d 'st0
{
  O.auth_context_free d.client_driver_auth;
  Box.free d.client_driver_channel;
  free_client_driver_buffers d buffered_len;
  fold (client_driver_closed d 'st0);
}

inline_for_extraction
fn close_failed_connect
  (d:client_driver)
  (ch:IO.channel)
  (buffered_len:SZ.t)
  requires C.connection_exactly d.client_driver_client 'st0 **
           client_driver_canonical_progress d 'st0 **
           O.is_auth_context d.client_driver_auth **
           channel_open d.client_driver_tcp_history ch 'st0 'buffered buffered_len **
           Box.pts_to d.client_driver_channel no_channel **
           client_driver_buffers d (Ghost.reveal 'buffered) buffered_len
  ensures client_driver_closed d 'st0
{
  unfold (channel_open d.client_driver_tcp_history ch 'st0 'buffered buffered_len);
  with received sent.
    assert (IO.is_channel ch received sent **
            pure (client_driver_wire_logs_match 'st0 received sent (Ghost.reveal 'buffered) buffered_len));
  IO.close ch;
  free_disconnected_client_driver d buffered_len;
}
