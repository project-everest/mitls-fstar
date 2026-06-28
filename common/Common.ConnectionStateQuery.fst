module Common.ConnectionStateQuery

#lang-pulse

open Pulse.Lib.Pervasives

module CPI = Common.ProtocolImplementation
module TCP = Common.TCP

noextract
class connection_state_query
  (impl:Type0)
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  (local_output:Type0)
  (query:Type0)
  (action:Type0)
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
    action ->
    slprop;

  csq_action_sound:
    impl ->
    query ->
    state ->
    action ->
    prop;

  csq_next_action:
    i:impl ->
    q:query ->
    frame:csq_frame ->
    received:Ghost.erased TCP.bytes ->
    sent:Ghost.erased TCP.bytes ->
    st:Ghost.erased state ->
      stt action
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
          pure (csq_action_sound i q (Ghost.reveal st) action));
}
