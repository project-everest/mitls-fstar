module TLS13.Impl.Client.CanonicalQueries

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Impl.Client
module CP = TLS13.Impl.Client.CanonicalProtocol
module CQ = Common.ConnectionStateQuery
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.ConnectionState
module CT = TLS13.Impl.Client.Types
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Impl.CanonicalWire
module SZ = FStar.SizeT

noeq
type client_next_local_action_query = {
  client_query_network_out_len: SZ.t;
  client_query_certificate_public_key_len: SZ.t;
  client_query_server_finished_payload_len: SZ.t;
}

let client_next_local_action_sound
  (_cc:CP.canonical_client)
  (q:client_next_local_action_query)
  (st:CS.connection_state)
  (action:CT.next_local_action)
  : prop =
  C.next_local_action_sound
    st
    q.client_query_network_out_len
    q.client_query_certificate_public_key_len
    q.client_query_server_finished_payload_len
    action

type client_next_local_action_frame = unit

[@@pulse_unfold]
let client_next_local_action_frame_pre
  (_cc:CP.canonical_client)
  (_q:client_next_local_action_query)
  (_frame:client_next_local_action_frame)
  (_st:CS.connection_state)
  : slprop =
  emp

[@@pulse_unfold]
let client_next_local_action_frame_post
  (_cc:CP.canonical_client)
  (_q:client_next_local_action_query)
  (_frame:client_next_local_action_frame)
  (_st:CS.connection_state)
  (_action:CT.next_local_action)
  : slprop =
  emp

fn run_client_next_local_action
  (cc:CP.canonical_client)
  (q:client_next_local_action_query)
  (frame:client_next_local_action_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  client_next_local_action_frame_pre
    cc
    q
    frame
    (Ghost.reveal st)
returns action:CT.next_local_action
ensures
  CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  client_next_local_action_frame_post
    cc
    q
    frame
    (Ghost.reveal st)
    action **
  pure (client_next_local_action_sound cc q (Ghost.reveal st) action)
{
  unfold (CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  unfold (client_next_local_action_frame_pre
    cc
    q
    frame
    (Ghost.reveal st));
  rewrite
    (C.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st))
    as
    (CR.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st));
  let action =
    C.next_local_action
      cc.CP.canonical_client_state
      q.client_query_network_out_len
      q.client_query_certificate_public_key_len
      q.client_query_server_finished_payload_len;
  rewrite
    (CR.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st))
    as
    (C.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st));
  fold (CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  fold (client_next_local_action_frame_post
    cc
    q
    frame
    (Ghost.reveal st)
    action);
  action
}

noextract
let client_next_local_action_query_implementation
  : CQ.connection_state_query
      CP.canonical_client
      CS.connection_state
      CW.wire_message
      CTypes.client_local_event
      CTypes.local_output
      client_next_local_action_query
      CT.next_local_action
      CP.client_protocol_implementation
  =
  {
    CQ.csq_frame = client_next_local_action_frame;
    CQ.csq_frame_pre = client_next_local_action_frame_pre;
    CQ.csq_frame_post = client_next_local_action_frame_post;
    CQ.csq_action_sound = client_next_local_action_sound;
    CQ.csq_next_action = run_client_next_local_action;
  }
