module TLS13.Impl.Server.CanonicalQueries

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CQ = Common.ConnectionStateQuery
module CS = TLS13.Spec.ConnectionState
module S = TLS13.Impl.Server
module SP = TLS13.Impl.Server.CanonicalProtocol
module ST = TLS13.Impl.Server.Types

type server_next_local_action_query = unit
type server_next_local_action_frame = unit

let server_next_local_action_sound
  (_q:server_next_local_action_query)
  (st:CS.connection_state)
  (action:ST.next_local_action)
  : prop =
  ST.next_local_action_sound st action

[@@pulse_unfold]
let server_next_local_action_frame_pre
  (_q:server_next_local_action_query)
  (_frame:server_next_local_action_frame)
  (_st:CS.connection_state)
  : slprop =
  emp

[@@pulse_unfold]
let server_next_local_action_frame_post
  (_q:server_next_local_action_query)
  (_frame:server_next_local_action_frame)
  (_st:CS.connection_state)
  (_action:ST.next_local_action)
  : slprop =
  emp

fn run_server_next_local_action
  (srv:SP.canonical_server)
  (q:server_next_local_action_query)
  (frame:server_next_local_action_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  server_next_local_action_frame_pre
    q
    frame
    (Ghost.reveal st)
returns action:ST.next_local_action
ensures
  SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  server_next_local_action_frame_post
    q
    frame
    (Ghost.reveal st)
    action **
  pure (server_next_local_action_sound q (Ghost.reveal st) action)
{
  unfold (SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  unfold (server_next_local_action_frame_pre
    q
    frame
    (Ghost.reveal st));
  assert (pure (SP.server_invariant_pure
    (Ghost.reveal srv.SP.canonical_server_initial)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)));
  assert (pure (ST.server_state_correct (Ghost.reveal st)));
  let action =
    S.next_local_action
      srv.SP.canonical_server_state;
  fold (SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  fold (server_next_local_action_frame_post
    q
    frame
    (Ghost.reveal st)
    action);
  action
}

noextract
let server_next_local_action_query_implementation
  : CQ.connection_state_query
      SP.canonical_server
      CS.connection_state
      server_next_local_action_query
      ST.next_local_action
  =
  {
    CQ.csq_invariant = SP.server_invariant;
    CQ.csq_frame = server_next_local_action_frame;
    CQ.csq_frame_pre = server_next_local_action_frame_pre;
    CQ.csq_frame_post = server_next_local_action_frame_post;
    CQ.csq_sound = server_next_local_action_sound;
    CQ.csq_run = run_server_next_local_action;
  }
