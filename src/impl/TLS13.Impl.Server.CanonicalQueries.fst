module TLS13.Impl.Server.CanonicalQueries

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CQ = Common.ConnectionStateQuery
module CS = TLS13.Spec.ConnectionState
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Impl.CanonicalWire
module S = TLS13.Impl.Server
module SP = TLS13.Impl.Server.CanonicalProtocol
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

type server_next_local_action_query = unit
type server_next_local_action_frame = unit

type server_external_action =
  | ServerExternalSelectServerParameters
  | ServerExternalDeriveSharedSecret
  | ServerExternalSendServerHello
  | ServerExternalSendCertificate
  | ServerExternalSignCertificateVerify

let server_local_event_of_kind
  (kind:ST.local_event_kind)
  : CTypes.server_local_event =
  CTypes.ServerAPI {
    CTypes.server_local_kind = kind;
    CTypes.server_local_payload = B.empty;
  }

let server_next_action_of_tls
  (action:ST.next_local_action)
  : CQ.next_action CTypes.server_local_event server_external_action =
  if action.ST.next_local_ready then
    match action.ST.next_local_kind with
    | ST.LocalSelectServerParameters ->
      CQ.NextExternal ServerExternalSelectServerParameters
    | ST.LocalDeriveSharedSecret ->
      CQ.NextExternal ServerExternalDeriveSharedSecret
    | ST.LocalSendServerHello ->
      CQ.NextExternal ServerExternalSendServerHello
    | ST.LocalSendCertificate ->
      CQ.NextExternal ServerExternalSendCertificate
    | ST.LocalSignCertificateVerify ->
      CQ.NextExternal ServerExternalSignCertificateVerify
    | _ ->
      CQ.NextLocal (server_local_event_of_kind action.ST.next_local_kind)
  else
    CQ.NextNeedInput

let server_network_enabled
  (_srv:SP.canonical_server)
  (_q:server_next_local_action_query)
  (_st:CS.connection_state)
  : prop =
  True

let server_local_enabled
  (_srv:SP.canonical_server)
  (_q:server_next_local_action_query)
  (st:CS.connection_state)
  (ev:CTypes.server_local_event)
  : prop =
  match ev with
  | CTypes.ServerAPI api ->
    Seq.equal api.CTypes.server_local_payload B.empty /\
    ST.server_local_event_input_ready
      st
      api.CTypes.server_local_kind
      api.CTypes.server_local_payload
  | CTypes.ServerGhostStep ->
    False

let server_external_action_witness
  (ext:server_external_action)
  : ST.next_local_action =
  match ext with
  | ServerExternalSelectServerParameters ->
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSelectServerParameters;
      ST.next_local_payload = ST.LocalPayloadServerRandomAndPrivateKey;
    }
  | ServerExternalDeriveSharedSecret ->
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalDeriveSharedSecret;
      ST.next_local_payload = ST.LocalPayloadServerPrivateKey;
    }
  | ServerExternalSendServerHello ->
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSendServerHello;
      ST.next_local_payload = ST.LocalPayloadServerRandomAndPrivateKey;
    }
  | ServerExternalSendCertificate ->
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSendCertificate;
      ST.next_local_payload = ST.LocalPayloadNone;
    }
  | ServerExternalSignCertificateVerify ->
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSignCertificateVerify;
      ST.next_local_payload = ST.LocalPayloadNone;
    }

let server_external_enabled
  (_srv:SP.canonical_server)
  (_q:server_next_local_action_query)
  (st:CS.connection_state)
  (ext:server_external_action)
  : prop =
  ST.next_local_action_sound st (server_external_action_witness ext)

let server_done_enabled
  (_srv:SP.canonical_server)
  (_q:server_next_local_action_query)
  (_st:CS.connection_state)
  : prop =
  True

let server_failed_enabled
  (_srv:SP.canonical_server)
  (_q:server_next_local_action_query)
  (_st:CS.connection_state)
  : prop =
  True

let server_next_action_correct
  (srv:SP.canonical_server)
  (q:server_next_local_action_query)
  (st:CS.connection_state)
  (tls_action:ST.next_local_action)
  : Lemma
      (requires ST.next_local_action_sound st tls_action)
      (ensures
        CQ.next_action_correct
          server_network_enabled
          server_local_enabled
          server_external_enabled
          server_done_enabled
          server_failed_enabled
          srv
          q
          st
          (server_next_action_of_tls tls_action))
=
  if tls_action.ST.next_local_ready then (
    match tls_action.ST.next_local_kind with
    | ST.LocalSelectServerParameters -> ()
    | ST.LocalDeriveSharedSecret -> ()
    | ST.LocalSendServerHello -> ()
    | ST.LocalSendCertificate -> ()
    | ST.LocalSignCertificateVerify -> ()
    | _ ->
      assert (ST.server_local_event_input_ready
        st
        tls_action.ST.next_local_kind
        B.empty);
      assert (Seq.equal B.empty B.empty)
  ) else (
    ()
  )

[@@pulse_unfold]
let server_next_local_action_frame_pre
  (_srv:SP.canonical_server)
  (_q:server_next_local_action_query)
  (_frame:server_next_local_action_frame)
  (_st:CS.connection_state)
  : slprop =
  emp

[@@pulse_unfold]
let server_next_local_action_frame_post
  (_srv:SP.canonical_server)
  (_q:server_next_local_action_query)
  (_frame:server_next_local_action_frame)
  (_st:CS.connection_state)
  (_action:CQ.next_action CTypes.server_local_event server_external_action)
  : slprop =
  emp

[@@pulse_unfold]
let server_next_action_network_frame_pre
  (_srv:SP.canonical_server)
  (_q:server_next_local_action_query)
  (frame:SP.tls_server_network_bridge_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (input_contents:B.bytes)
  (old_out:B.bytes)
  : slprop =
  SP.server_network_bridge_frame_pre
    frame
    input
    input_len
    out
    out_len
    input_contents
    old_out

fn prepare_server_next_action_network
  (srv:SP.canonical_server)
  (q:server_next_local_action_query)
  (frame:SP.tls_server_network_bridge_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (st:Ghost.erased CS.connection_state)
  (input_contents:Ghost.erased B.bytes)
  (old_out:Ghost.erased B.bytes)
requires
  server_next_action_network_frame_pre
    srv
    q
    frame
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out) **
  pure (server_network_enabled srv q (Ghost.reveal st))
ensures
  SP.server_network_bridge_frame_pre
    frame
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out)
{
  unfold (server_next_action_network_frame_pre
    srv
    q
    frame
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out))
}

[@@pulse_unfold]
let server_next_action_local_frame_pre
  (_srv:SP.canonical_server)
  (_q:server_next_local_action_query)
  (ev:CTypes.server_local_event)
  (frame:SP.tls_server_local_bridge_frame)
  (st:CS.connection_state)
  (out:array U8.t)
  (out_len:SZ.t)
  (old_out:B.bytes)
  : slprop =
  SP.server_local_bridge_frame_pre ev frame st out out_len old_out

fn prepare_server_next_action_local
  (srv:SP.canonical_server)
  (q:server_next_local_action_query)
  (ev:CTypes.server_local_event)
  (frame:SP.tls_server_local_bridge_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (st:Ghost.erased CS.connection_state)
  (old_out:Ghost.erased B.bytes)
requires
  server_next_action_local_frame_pre
    srv
    q
    ev
    frame
    (Ghost.reveal st)
    out
    out_len
    (Ghost.reveal old_out) **
  pure (server_local_enabled srv q (Ghost.reveal st) ev)
ensures
  SP.server_local_bridge_frame_pre
    ev
    frame
    (Ghost.reveal st)
    out
    out_len
    (Ghost.reveal old_out)
{
  unfold (server_next_action_local_frame_pre
    srv
    q
    ev
    frame
    (Ghost.reveal st)
    out
    out_len
    (Ghost.reveal old_out))
}

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
    srv
    q
    frame
    (Ghost.reveal st)
returns action:CQ.next_action CTypes.server_local_event server_external_action
ensures
  SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  server_next_local_action_frame_post
    srv
    q
    frame
    (Ghost.reveal st)
    action **
  pure (CQ.next_action_correct
    server_network_enabled
    server_local_enabled
    server_external_enabled
    server_done_enabled
    server_failed_enabled
    srv
    q
    (Ghost.reveal st)
    action)
{
  unfold (SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  unfold (server_next_local_action_frame_pre
    srv
    q
    frame
    (Ghost.reveal st));
  assert (pure (SP.server_invariant_pure
    (Ghost.reveal srv.SP.canonical_server_initial)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)));
  assert (pure (ST.server_state_correct (Ghost.reveal st)));
  let tls_action =
    S.next_local_action
      srv.SP.canonical_server_state;
  let action = server_next_action_of_tls tls_action;
  server_next_action_correct srv q (Ghost.reveal st) tls_action;
  fold (SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  fold (server_next_local_action_frame_post
    srv
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
      CW.wire_message
      CTypes.server_local_event
      CTypes.local_output
      server_next_local_action_query
      server_external_action
      SP.server_protocol_implementation
  =
  {
    CQ.csq_frame = server_next_local_action_frame;
    CQ.csq_frame_pre = server_next_local_action_frame_pre;
    CQ.csq_frame_post = server_next_local_action_frame_post;
    CQ.csq_network_enabled = server_network_enabled;
    CQ.csq_local_enabled = server_local_enabled;
    CQ.csq_external_enabled = server_external_enabled;
    CQ.csq_done_enabled = server_done_enabled;
    CQ.csq_failed_enabled = server_failed_enabled;
    CQ.csq_network_frame_pre = server_next_action_network_frame_pre;
    CQ.csq_prepare_network = prepare_server_next_action_network;
    CQ.csq_local_frame_pre = server_next_action_local_frame_pre;
    CQ.csq_prepare_local = prepare_server_next_action_local;
    CQ.csq_next_action = run_server_next_local_action;
  }
