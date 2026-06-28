module Common.ConnectionStateQuery

#lang-pulse

open Pulse.Lib.Pervasives

module TCP = Common.TCP

noextract
class connection_state_query
  (impl:Type0)
  (state:Type0)
  (query:Type0)
  (result:Type0)
  =
{
  csq_invariant:
    impl ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    slprop;

  csq_frame:
    Type0;

  csq_frame_pre:
    query ->
    csq_frame ->
    state ->
    slprop;

  csq_frame_post:
    query ->
    csq_frame ->
    state ->
    result ->
    slprop;

  csq_sound:
    query ->
    state ->
    result ->
    prop;

  csq_run:
    i:impl ->
    q:query ->
    frame:csq_frame ->
    received:Ghost.erased TCP.bytes ->
    sent:Ghost.erased TCP.bytes ->
    st:Ghost.erased state ->
      stt result
        (csq_invariant
          i
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st) **
         csq_frame_pre
          q
          frame
          (Ghost.reveal st))
        (fun result ->
          csq_invariant
            i
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st) **
          csq_frame_post
            q
            frame
            (Ghost.reveal st)
            result **
          pure (csq_sound q (Ghost.reveal st) result));
}
