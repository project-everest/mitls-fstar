module Common.ConnectionStateQuery

#lang-pulse

open Pulse.Lib.Pervasives

module CPI = Common.ProtocolImplementation
module SZ = FStar.SizeT
module TCP = Common.TCP
module U8 = FStar.UInt8

type next_action
  (local_event:Type0)
  (external_action:Type0)
  =
  | NextNeedInput
  | NextLocal: ev:local_event -> next_action local_event external_action
  | NextExternal: action:external_action -> next_action local_event external_action
  | NextDone
  | NextFailed

let next_action_correct
  (#impl:Type0)
  (#state:Type0)
  (#local_event:Type0)
  (#external_action:Type0)
  (#query:Type0)
  (network_enabled:impl -> query -> state -> prop)
  (local_enabled:impl -> query -> state -> local_event -> prop)
  (external_enabled:impl -> query -> state -> external_action -> prop)
  (done_enabled:impl -> query -> state -> prop)
  (failed_enabled:impl -> query -> state -> prop)
  (i:impl)
  (q:query)
  (st:state)
  (action:next_action local_event external_action)
  : prop =
  match action with
  | NextNeedInput -> network_enabled i q st
  | NextLocal ev -> local_enabled i q st ev
  | NextExternal ext -> external_enabled i q st ext
  | NextDone -> done_enabled i q st
  | NextFailed -> failed_enabled i q st

noextract
class connection_state_query
  (impl:Type0)
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  (local_output:Type0)
  (query:Type0)
  (external_action:Type0)
  (protocol:CPI.protocol_implementation
    impl
    state
    wire_message
    local_event
    local_output)
  =
{
  csq_frame:
    Type0;

  csq_frame_pre:
    impl ->
    query ->
    csq_frame ->
    state ->
    slprop;

  csq_frame_post:
    impl ->
    query ->
    csq_frame ->
    state ->
    next_action local_event external_action ->
    slprop;

  csq_network_enabled:
    impl ->
    query ->
    state ->
    prop;

  csq_local_enabled:
    impl ->
    query ->
    state ->
    local_event ->
    prop;

  csq_external_enabled:
    impl ->
    query ->
    state ->
    external_action ->
    prop;

  csq_done_enabled:
    impl ->
    query ->
    state ->
    prop;

  csq_failed_enabled:
    impl ->
    query ->
    state ->
    prop;

  csq_network_frame_pre:
    impl ->
    query ->
    protocol.CPI.pi_network_frame ->
    array U8.t ->
    SZ.t ->
    array U8.t ->
    SZ.t ->
    TCP.bytes ->
    TCP.bytes ->
    slprop;

  csq_prepare_network:
    i:impl ->
    q:query ->
    frame:protocol.CPI.pi_network_frame ->
    input:array U8.t ->
    input_len:SZ.t ->
    out:array U8.t ->
    out_len:SZ.t ->
    st:Ghost.erased state ->
    input_contents:Ghost.erased TCP.bytes ->
    old_out:Ghost.erased TCP.bytes ->
      stt unit
        (csq_network_frame_pre
          i
          q
          frame
          input
          input_len
          out
          out_len
          (Ghost.reveal input_contents)
          (Ghost.reveal old_out) **
         pure (csq_network_enabled i q (Ghost.reveal st)))
        (fun _ ->
          protocol.CPI.pi_network_frame_pre
            frame
            input
            input_len
            out
            out_len
            (Ghost.reveal input_contents)
            (Ghost.reveal old_out));

  csq_local_frame_pre:
    impl ->
    query ->
    local_event ->
    protocol.CPI.pi_local_frame ->
    state ->
    array U8.t ->
    SZ.t ->
    TCP.bytes ->
    slprop;

  csq_prepare_local:
    i:impl ->
    q:query ->
    ev:local_event ->
    frame:protocol.CPI.pi_local_frame ->
    out:array U8.t ->
    out_len:SZ.t ->
    st:Ghost.erased state ->
    old_out:Ghost.erased TCP.bytes ->
      stt unit
        (csq_local_frame_pre
          i
          q
          ev
          frame
          (Ghost.reveal st)
          out
          out_len
          (Ghost.reveal old_out) **
         pure (csq_local_enabled i q (Ghost.reveal st) ev))
        (fun _ ->
          protocol.CPI.pi_local_frame_pre
            ev
            frame
            (Ghost.reveal st)
            out
            out_len
            (Ghost.reveal old_out));

  csq_next_action:
    i:impl ->
    q:query ->
    frame:csq_frame ->
    received:Ghost.erased TCP.bytes ->
    sent:Ghost.erased TCP.bytes ->
    st:Ghost.erased state ->
      stt (next_action local_event external_action)
        (protocol.CPI.pi_invariant
          i
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st) **
         csq_frame_pre
          i
          q
          frame
          (Ghost.reveal st))
        (fun action ->
          protocol.CPI.pi_invariant
            i
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st) **
          csq_frame_post
            i
            q
            frame
            (Ghost.reveal st)
            action **
          pure (next_action_correct
            csq_network_enabled
            csq_local_enabled
            csq_external_enabled
            csq_done_enabled
            csq_failed_enabled
            i
            q
            (Ghost.reveal st)
            action));
}
