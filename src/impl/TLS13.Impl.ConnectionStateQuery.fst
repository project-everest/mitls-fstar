module TLS13.Impl.ConnectionStateQuery

#lang-pulse

open Pulse.Lib.Pervasives

module Seq = FStar.Seq
module SZ = FStar.SizeT
module TCP = Common.TCP
module U8 = FStar.UInt8

// TLS-internal compatibility shim used by endpoint adapters that still split
// scheduling into immediate local actions and endpoint-material-backed deferred
// locals.  The executable driver-facing class lives in Common.ProtocolEndpoint.

type next_action
  (network_frame:Type0)
  (local_event:Type0)
  (local_frame:Type0)
  (deferred_action:Type0)
  =
  | NextNeedInput:
      frame:network_frame ->
        next_action network_frame local_event local_frame deferred_action
  | NextLocal:
      ev:local_event ->
      frame:local_frame ->
        next_action network_frame local_event local_frame deferred_action
  | NextDeferredLocal:
      action:deferred_action ->
        next_action network_frame local_event local_frame deferred_action
  | NextDone:
        next_action network_frame local_event local_frame deferred_action
  | NextFailed:
        next_action network_frame local_event local_frame deferred_action

[@@pulse_unfold]
let network_buffers
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (input_contents:TCP.bytes)
  (old_out:TCP.bytes)
  : slprop =
  pts_to input input_contents **
  pts_to out old_out **
  pure (
    Seq.length input_contents == SZ.v input_len /\
    Seq.length old_out == SZ.v out_len)

[@@pulse_unfold]
let local_output_buffer
  (out:array U8.t)
  (out_len:SZ.t)
  (old_out:TCP.bytes)
  : slprop =
  pts_to out old_out **
  pure (Seq.length old_out == SZ.v out_len)
