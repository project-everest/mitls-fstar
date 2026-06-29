module Common.ConnectionStateQuery

#lang-pulse

open Pulse.Lib.Pervasives

module CPI = Common.ProtocolImplementation
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TCP = Common.TCP
module U8 = FStar.UInt8

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

noextract
class connection_state_query
  (impl:Type0)
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  (local_output:Type0)
  (deferred_action:Type0)
  (protocol:CPI.protocol_implementation
    impl
    state
    wire_message
    local_event
    local_output)
  =
{
  csq_config:
    Type0;

  csq_frame:
    Type0;

  csq_frame_ready:
    impl ->
    csq_config ->
    csq_frame ->
    state ->
    slprop;

  csq_action_frame:
    impl ->
    csq_config ->
    csq_frame ->
    state ->
    next_action
      protocol.CPI.pi_network_frame
      local_event
      protocol.CPI.pi_local_frame
      deferred_action ->
    slprop;

  csq_network_continuation:
    impl ->
    csq_config ->
    csq_frame ->
    state ->
    protocol.CPI.pi_network_frame ->
    slprop;

  csq_local_continuation:
    impl ->
    csq_config ->
    csq_frame ->
    state ->
    local_event ->
    protocol.CPI.pi_local_frame ->
    slprop;

  csq_next_action:
    i:impl ->
    cfg:csq_config ->
    frame:csq_frame ->
    received:Ghost.erased TCP.bytes ->
    sent:Ghost.erased TCP.bytes ->
    st:Ghost.erased state ->
      stt (next_action
        protocol.CPI.pi_network_frame
        local_event
        protocol.CPI.pi_local_frame
        deferred_action)
        (protocol.CPI.pi_invariant
           i
           (Ghost.reveal received)
           (Ghost.reveal sent)
           (Ghost.reveal st) **
         csq_frame_ready
           i
           cfg
           frame
           (Ghost.reveal st))
        (fun action ->
          protocol.CPI.pi_invariant
            i
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st) **
          csq_action_frame
            i
            cfg
            frame
            (Ghost.reveal st)
            action);

  csq_cancel_action:
    i:impl ->
    cfg:csq_config ->
    frame:csq_frame ->
    st:Ghost.erased state ->
    action:next_action
      protocol.CPI.pi_network_frame
      local_event
      protocol.CPI.pi_local_frame
      deferred_action ->
      stt unit
        (csq_action_frame
          i
          cfg
          frame
          (Ghost.reveal st)
          action)
        (fun _ ->
          csq_frame_ready
            i
            cfg
            frame
            (Ghost.reveal st));

  csq_prepare_network:
    i:impl ->
    cfg:csq_config ->
    frame:csq_frame ->
    network_frame:protocol.CPI.pi_network_frame ->
    input:array U8.t ->
    input_len:SZ.t ->
    out:array U8.t ->
    out_len:SZ.t ->
    st:Ghost.erased state ->
    input_contents:Ghost.erased TCP.bytes ->
    old_out:Ghost.erased TCP.bytes ->
      stt unit
        (csq_action_frame
          i
          cfg
          frame
          (Ghost.reveal st)
          (NextNeedInput network_frame) **
         network_buffers
          input
          input_len
          out
          out_len
          (Ghost.reveal input_contents)
          (Ghost.reveal old_out))
        (fun _ ->
          protocol.CPI.pi_network_frame_pre
            network_frame
            input
            input_len
            out
            out_len
            (Ghost.reveal input_contents)
            (Ghost.reveal old_out) **
          csq_network_continuation
            i
            cfg
            frame
            (Ghost.reveal st)
            network_frame **
          network_buffers
            input
            input_len
            out
            out_len
            (Ghost.reveal input_contents)
            (Ghost.reveal old_out) **
          pure (
            CPI.buffers_wf
              (Ghost.reveal input_contents)
              input_len
              (Ghost.reveal old_out)
              out_len));

  csq_finish_network:
    i:impl ->
    cfg:csq_config ->
    frame:csq_frame ->
    network_frame:protocol.CPI.pi_network_frame ->
    result:CPI.process_result ->
    input_contents:Ghost.erased TCP.bytes ->
    input_len:SZ.t ->
    old_out:Ghost.erased TCP.bytes ->
    out_contents:Ghost.erased TCP.bytes ->
    st0:Ghost.erased state ->
    st1:Ghost.erased state ->
    consumed:Ghost.erased TCP.bytes ->
    wire_outputs:Ghost.erased (list wire_message) ->
    local_outputs:Ghost.erased (list local_output) ->
      stt unit
        (csq_network_continuation
          i
          cfg
          frame
          (Ghost.reveal st0)
          network_frame **
         protocol.CPI.pi_network_frame_post
          network_frame
          result
          (Ghost.reveal input_contents)
          input_len
          (Ghost.reveal old_out)
          (Ghost.reveal out_contents)
          (Ghost.reveal st0)
          (Ghost.reveal st1)
          (Ghost.reveal consumed)
          (Ghost.reveal wire_outputs)
          (Ghost.reveal local_outputs))
        (fun _ ->
          csq_frame_ready
            i
            cfg
            frame
            (Ghost.reveal st1));

  csq_prepare_local:
    i:impl ->
    cfg:csq_config ->
    frame:csq_frame ->
    ev:local_event ->
    local_frame:protocol.CPI.pi_local_frame ->
    out:array U8.t ->
    out_len:SZ.t ->
    st:Ghost.erased state ->
    old_out:Ghost.erased TCP.bytes ->
      stt unit
        (csq_action_frame
          i
          cfg
          frame
          (Ghost.reveal st)
          (NextLocal ev local_frame) **
         local_output_buffer
          out
          out_len
          (Ghost.reveal old_out))
        (fun _ ->
          protocol.CPI.pi_local_frame_pre
            ev
            local_frame
            (Ghost.reveal st)
            out
            out_len
            (Ghost.reveal old_out) **
          csq_local_continuation
            i
            cfg
            frame
            (Ghost.reveal st)
            ev
            local_frame **
          local_output_buffer
            out
            out_len
            (Ghost.reveal old_out));

  csq_finish_local:
    i:impl ->
    cfg:csq_config ->
    frame:csq_frame ->
    ev:local_event ->
    local_frame:protocol.CPI.pi_local_frame ->
    result:CPI.process_result ->
    old_out:Ghost.erased TCP.bytes ->
    out_contents:Ghost.erased TCP.bytes ->
    st0:Ghost.erased state ->
    st1:Ghost.erased state ->
    wire_outputs:Ghost.erased (list wire_message) ->
    local_outputs:Ghost.erased (list local_output) ->
      stt unit
        (csq_local_continuation
          i
          cfg
          frame
          (Ghost.reveal st0)
          ev
          local_frame **
         protocol.CPI.pi_local_frame_post
          ev
          local_frame
          result
          (Ghost.reveal old_out)
          (Ghost.reveal out_contents)
          (Ghost.reveal st0)
          (Ghost.reveal st1)
          (Ghost.reveal wire_outputs)
          (Ghost.reveal local_outputs))
        (fun _ ->
          csq_frame_ready
            i
            cfg
            frame
            (Ghost.reveal st1));
}
