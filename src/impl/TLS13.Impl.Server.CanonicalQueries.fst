module TLS13.Impl.Server.CanonicalQueries

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CPI = Common.ProtocolImplementation
module CQ = TLS13.Impl.ConnectionStateQuery
module CS = TLS13.Spec.ConnectionState
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Impl.CanonicalWire
module S = TLS13.Impl.Server
module SP = TLS13.Impl.Server.CanonicalProtocol
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

type server_next_local_action_config = unit

type server_deferred_action =
  | ServerDeferredSelectServerParameters
  | ServerDeferredDeriveSharedSecret
  | ServerDeferredSendServerHello
  | ServerDeferredSignCertificateVerify

noeq
type server_next_local_action_frame = {
  server_query_network_app_out: array U8.t;
  server_query_network_app_out_len: SZ.t;
  server_query_network_bridge_proof:
    old:Ghost.erased B.bytes ->
      Ghost.erased
        (SP.server_network_bridge_obligation {
          SP.tls_server_network_app_out = server_query_network_app_out;
          SP.tls_server_network_app_out_len = server_query_network_app_out_len;
          SP.tls_server_network_old_app_out = old;
        });
  server_query_local_payload: array U8.t;
  server_query_local_payload_len: SZ.t;
  server_query_local_app_out: array U8.t;
  server_query_local_app_out_len: SZ.t;
  server_query_local_bridge_proof:
    old:Ghost.erased B.bytes ->
      Ghost.erased
        (SP.server_local_bridge_obligation {
          SP.tls_server_local_payload = server_query_local_payload;
          SP.tls_server_local_payload_len = server_query_local_payload_len;
          SP.tls_server_local_app_out = server_query_local_app_out;
          SP.tls_server_local_app_out_len = server_query_local_app_out_len;
          SP.tls_server_local_old_app_out = old;
        });
}

let server_network_frame_of_current
  (frame:server_next_local_action_frame)
  (old:Ghost.erased B.bytes)
  : SP.tls_server_network_bridge_frame =
  let base = {
    SP.tls_server_network_app_out = frame.server_query_network_app_out;
    SP.tls_server_network_app_out_len =
      frame.server_query_network_app_out_len;
    SP.tls_server_network_old_app_out = old;
  } in
  {
    SP.tls_server_network_bridge_base = base;
    SP.tls_server_network_bridge_proof =
      frame.server_query_network_bridge_proof old;
  }

let server_local_frame_of_current
  (frame:server_next_local_action_frame)
  (old:Ghost.erased B.bytes)
  : SP.tls_server_local_bridge_frame =
  let base = {
    SP.tls_server_local_payload = frame.server_query_local_payload;
    SP.tls_server_local_payload_len = frame.server_query_local_payload_len;
    SP.tls_server_local_app_out = frame.server_query_local_app_out;
    SP.tls_server_local_app_out_len = frame.server_query_local_app_out_len;
    SP.tls_server_local_old_app_out = old;
  } in
  {
    SP.tls_server_local_bridge_base = base;
    SP.tls_server_local_bridge_proof =
      frame.server_query_local_bridge_proof old;
  }

let server_network_frame_matches
  (frame:server_next_local_action_frame)
  (network_frame:SP.tls_server_network_bridge_frame)
  : prop =
  network_frame.SP.tls_server_network_bridge_base.SP.tls_server_network_app_out
    == frame.server_query_network_app_out /\
  network_frame.SP.tls_server_network_bridge_base.SP.tls_server_network_app_out_len
    == frame.server_query_network_app_out_len

let server_local_frame_matches
  (frame:server_next_local_action_frame)
  (local_frame:SP.tls_server_local_bridge_frame)
  : prop =
  local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
    == frame.server_query_local_payload /\
  local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload_len
    == frame.server_query_local_payload_len /\
  local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
    == frame.server_query_local_app_out /\
  local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out_len
    == frame.server_query_local_app_out_len

let server_local_event_of_kind
  (kind:ST.local_event_kind)
  : CTypes.server_local_event =
  CTypes.ServerAPI {
    CTypes.server_local_kind = kind;
    CTypes.server_local_payload = B.empty;
  }

let server_next_action_of_tls
  (network_frame:SP.tls_server_network_bridge_frame)
  (local_frame:SP.tls_server_local_bridge_frame)
  (action:ST.next_local_action)
  : CQ.next_action
      SP.tls_server_network_bridge_frame
      CTypes.server_local_event
      SP.tls_server_local_bridge_frame
      server_deferred_action =
  if action.ST.next_local_ready then
    match action.ST.next_local_kind with
    | ST.LocalSelectServerParameters ->
      CQ.NextDeferredLocal ServerDeferredSelectServerParameters
    | ST.LocalDeriveSharedSecret ->
      CQ.NextDeferredLocal ServerDeferredDeriveSharedSecret
    | ST.LocalSendServerHello ->
      CQ.NextDeferredLocal ServerDeferredSendServerHello
    | ST.LocalSendCertificate ->
      CQ.NextLocal
        (server_local_event_of_kind action.ST.next_local_kind)
        local_frame
    | ST.LocalSignCertificateVerify ->
      CQ.NextDeferredLocal ServerDeferredSignCertificateVerify
    | _ ->
      CQ.NextLocal
        (server_local_event_of_kind action.ST.next_local_kind)
        local_frame
  else
    CQ.NextNeedInput network_frame

let server_local_event_ready
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
  | CTypes.ServerPayload kind payload ->
    Seq.equal (Ghost.reveal payload) B.empty /\
    ST.server_local_event_input_ready
      st
      kind
      (Ghost.reveal payload)

let server_local_event_from_query
  (ev:CTypes.server_local_event)
  : prop =
  match ev with
  | CTypes.ServerAPI _ -> True
  | CTypes.ServerPayload _ _ -> False

let server_local_event_ready_payload_empty
  (st:CS.connection_state)
  (ev:CTypes.server_local_event)
  : Lemma
      (requires server_local_event_ready st ev)
      (ensures Seq.equal
        (CTypes.server_local_event_api ev).CTypes.server_local_payload
        B.empty)
=
  match ev with
  | CTypes.ServerAPI _ -> ()
  | CTypes.ServerPayload _ _ -> ()

let server_local_event_ready_input_wf
  (st:CS.connection_state)
  (ev:CTypes.server_local_event)
  : Lemma
      (requires server_local_event_ready st ev)
      (ensures ST.server_local_event_input_ready
        st
        (CTypes.server_local_event_api ev).CTypes.server_local_kind
        (CTypes.server_local_event_api ev).CTypes.server_local_payload)
=
  match ev with
  | CTypes.ServerAPI _ -> ()
  | CTypes.ServerPayload _ _ -> ()

let server_deferred_action_witness
  (ext:server_deferred_action)
  : ST.next_local_action =
  match ext with
  | ServerDeferredSelectServerParameters ->
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSelectServerParameters;
      ST.next_local_payload = ST.LocalPayloadServerRandomAndPrivateKey;
    }
  | ServerDeferredDeriveSharedSecret ->
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalDeriveSharedSecret;
      ST.next_local_payload = ST.LocalPayloadServerPrivateKey;
    }
  | ServerDeferredSendServerHello ->
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSendServerHello;
      ST.next_local_payload = ST.LocalPayloadServerRandomAndPrivateKey;
    }
  | ServerDeferredSignCertificateVerify ->
    {
      ST.next_local_ready = true;
      ST.next_local_kind = ST.LocalSignCertificateVerify;
      ST.next_local_payload = ST.LocalPayloadNone;
    }

let server_deferred_action_ready
  (st:CS.connection_state)
  (ext:server_deferred_action)
  : prop =
  ST.next_local_action_sound st (server_deferred_action_witness ext)

let server_internal_ready_implies_kind_ready
  (st:CS.connection_state)
  (tls_action:ST.next_local_action)
  : Lemma
      (requires
        ST.next_local_action_sound st tls_action /\
        tls_action.ST.next_local_ready == true)
      (ensures
        (match tls_action.ST.next_local_kind with
        | ST.LocalSelectServerParameters
        | ST.LocalDeriveSharedSecret
        | ST.LocalSendServerHello
        | ST.LocalSignCertificateVerify ->
          True
        | _ ->
          ST.server_local_event_input_ready
            st
            tls_action.ST.next_local_kind
            B.empty))
 =
  ()

let server_next_action_correct
  (st:CS.connection_state)
  (network_frame:SP.tls_server_network_bridge_frame)
  (local_frame:SP.tls_server_local_bridge_frame)
  (tls_action:ST.next_local_action)
  : Lemma
      (requires ST.next_local_action_sound st tls_action)
      (ensures
        (match server_next_action_of_tls network_frame local_frame tls_action with
        | CQ.NextNeedInput _ -> True
        | CQ.NextLocal ev _ -> server_local_event_ready st ev
        | CQ.NextDeferredLocal ext -> server_deferred_action_ready st ext
        | CQ.NextDone -> True
        | CQ.NextFailed -> True))
=
  if tls_action.ST.next_local_ready then (
    match tls_action.ST.next_local_kind with
    | ST.LocalSelectServerParameters -> ()
    | ST.LocalDeriveSharedSecret -> ()
    | ST.LocalSendServerHello -> ()
    | ST.LocalSignCertificateVerify -> ()
    | _ ->
      server_internal_ready_implies_kind_ready st tls_action;
      assert (ST.server_local_event_input_ready
        st
        tls_action.ST.next_local_kind
        B.empty);
      assert (Seq.equal B.empty B.empty)
  ) else (
    ()
  )

[@@pulse_unfold]
let server_network_persistent_resource
  (frame:server_next_local_action_frame)
  : slprop =
  exists* (current:B.bytes).
    pts_to frame.server_query_network_app_out current **
    pure (B.length current == SZ.v frame.server_query_network_app_out_len)

[@@pulse_unfold]
let server_local_persistent_resource
  (frame:server_next_local_action_frame)
  : slprop =
  exists* (current:B.bytes).
    pts_to frame.server_query_local_payload B.empty **
    pts_to frame.server_query_local_app_out current **
    pure (
      SZ.v frame.server_query_local_payload_len == 0 /\
      B.length current == SZ.v frame.server_query_local_app_out_len)

[@@pulse_unfold]
let server_network_frame_resource
  (frame:SP.tls_server_network_bridge_frame)
  : slprop =
  pts_to
    frame.SP.tls_server_network_bridge_base.SP.tls_server_network_app_out
    (Ghost.reveal
      frame.SP.tls_server_network_bridge_base.SP.tls_server_network_old_app_out) **
  pure (
    B.length
      (Ghost.reveal
        frame.SP.tls_server_network_bridge_base.SP.tls_server_network_old_app_out) ==
      SZ.v frame.SP.tls_server_network_bridge_base.SP.tls_server_network_app_out_len)

[@@pulse_unfold]
let server_local_frame_resource
  (frame:SP.tls_server_local_bridge_frame)
  : slprop =
  pts_to
    frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
    B.empty **
  pts_to
    frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
    (Ghost.reveal
      frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out) **
  pure (
    SZ.v
      frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload_len
      == 0 /\
    B.length
      (Ghost.reveal
        frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out) ==
      SZ.v frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out_len)

[@@pulse_unfold]
let server_next_local_action_frame_ready
  (_srv:SP.canonical_server)
  (_cfg:server_next_local_action_config)
  (frame:server_next_local_action_frame)
  (_st:CS.connection_state)
  : slprop =
  server_network_persistent_resource frame **
  server_local_persistent_resource frame

[@@pulse_unfold]
let server_next_local_action_frame_post
  (srv:SP.canonical_server)
  (cfg:server_next_local_action_config)
  (frame:server_next_local_action_frame)
  (st:CS.connection_state)
  (action:CQ.next_action
    SP.tls_server_network_bridge_frame
    CTypes.server_local_event
    SP.tls_server_local_bridge_frame
    server_deferred_action)
  : slprop =
  match action with
  | CQ.NextNeedInput network_frame ->
    server_network_frame_resource network_frame **
    server_local_persistent_resource frame **
    pure (server_network_frame_matches frame network_frame)
  | CQ.NextLocal ev local_frame ->
    server_local_frame_resource local_frame **
    server_network_persistent_resource frame **
    pure (
      server_local_event_ready st ev /\
      server_local_frame_matches frame local_frame /\
      SZ.v frame.server_query_local_payload_len == 0 /\
      server_local_event_from_query ev)
  | CQ.NextDeferredLocal ext ->
    server_next_local_action_frame_ready srv cfg frame st **
    pure (server_deferred_action_ready st ext)
  | CQ.NextDone
  | CQ.NextFailed ->
    server_next_local_action_frame_ready srv cfg frame st

[@@pulse_unfold]
let server_next_local_action_network_continuation
  (_srv:SP.canonical_server)
  (_cfg:server_next_local_action_config)
  (frame:server_next_local_action_frame)
  (_st:CS.connection_state)
  (network_frame:SP.tls_server_network_bridge_frame)
  : slprop =
  server_local_persistent_resource frame **
  pure (server_network_frame_matches frame network_frame)

[@@pulse_unfold]
let server_next_local_action_local_continuation
  (srv:SP.canonical_server)
  (cfg:server_next_local_action_config)
  (frame:server_next_local_action_frame)
  (st:CS.connection_state)
  (ev:CTypes.server_local_event)
  (local_frame:SP.tls_server_local_bridge_frame)
  : slprop =
  server_network_persistent_resource frame **
  pure (
    server_local_event_ready st ev /\
    server_local_frame_matches frame local_frame /\
    SZ.v frame.server_query_local_payload_len == 0)

fn cancel_server_next_action
  (srv:SP.canonical_server)
  (cfg:server_next_local_action_config)
  (frame:server_next_local_action_frame)
  (st:Ghost.erased CS.connection_state)
  (action:CQ.next_action
    SP.tls_server_network_bridge_frame
    CTypes.server_local_event
    SP.tls_server_local_bridge_frame
    server_deferred_action)
requires
  server_next_local_action_frame_post
    srv
    cfg
    frame
    (Ghost.reveal st)
    action
ensures
  server_next_local_action_frame_ready
    srv
    cfg
    frame
    (Ghost.reveal st)
{
  unfold (server_next_local_action_frame_post
    srv
    cfg
    frame
    (Ghost.reveal st)
    action);
  match action {
    CQ.NextNeedInput network_frame -> {
      unfold (server_network_frame_resource network_frame);
      rewrite
        (pts_to
          network_frame.SP.tls_server_network_bridge_base.SP.tls_server_network_app_out
          (Ghost.reveal
            network_frame.SP.tls_server_network_bridge_base.SP.tls_server_network_old_app_out))
        as
        (pts_to
          frame.server_query_network_app_out
          (Ghost.reveal
            network_frame.SP.tls_server_network_bridge_base.SP.tls_server_network_old_app_out));
      let old_network: Ghost.erased B.bytes =
        network_frame.SP.tls_server_network_bridge_base.SP.tls_server_network_old_app_out;
      with old_network.
      fold (server_network_persistent_resource frame);
      fold (server_next_local_action_frame_ready
        srv
        cfg
        frame
        (Ghost.reveal st))
    }
    CQ.NextLocal ev local_frame -> {
      unfold (server_local_frame_resource local_frame);
      server_local_event_ready_payload_empty (Ghost.reveal st) ev;
      Seq.lemma_eq_elim
        (CTypes.server_local_event_api ev).CTypes.server_local_payload
        B.empty;
      rewrite
        (pts_to
          local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
          B.empty)
        as
        (pts_to frame.server_query_local_payload B.empty);
      rewrite
        (pts_to
          local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
          (Ghost.reveal
            local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out))
        as
        (pts_to
          frame.server_query_local_app_out
          (Ghost.reveal
            local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out));
      let old_local: Ghost.erased B.bytes =
        local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out;
      with old_local.
      fold (server_local_persistent_resource frame);
      fold (server_next_local_action_frame_ready
        srv
        cfg
        frame
        (Ghost.reveal st))
    }
    CQ.NextDeferredLocal _ -> {
      fold (server_next_local_action_frame_ready
        srv
        cfg
        frame
        (Ghost.reveal st))
    }
    CQ.NextDone -> {
      fold (server_next_local_action_frame_ready
        srv
        cfg
        frame
        (Ghost.reveal st))
    }
    CQ.NextFailed -> {
      fold (server_next_local_action_frame_ready
        srv
        cfg
        frame
        (Ghost.reveal st))
    }
  }
}

fn prepare_server_next_action_network
  (srv:SP.canonical_server)
  (cfg:server_next_local_action_config)
  (frame:server_next_local_action_frame)
  (network_frame:SP.tls_server_network_bridge_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (st:Ghost.erased CS.connection_state)
  (input_contents:Ghost.erased B.bytes)
  (old_out:Ghost.erased B.bytes)
requires
  server_next_local_action_frame_post
    srv
    cfg
    frame
    (Ghost.reveal st)
    (CQ.NextNeedInput network_frame) **
  CQ.network_buffers
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out)
ensures
  SP.server_network_bridge_frame_pre
    network_frame
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out) **
  server_next_local_action_network_continuation
    srv
    cfg
    frame
    (Ghost.reveal st)
    network_frame **
  CQ.network_buffers
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
      out_len)
{
  unfold (server_next_local_action_frame_post
    srv
    cfg
    frame
    (Ghost.reveal st)
    (CQ.NextNeedInput network_frame));
  unfold (server_network_frame_resource network_frame);
  unfold (CQ.network_buffers
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out));
  fold (SP.server_network_bridge_frame_pre
    network_frame
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out));
  fold (server_next_local_action_network_continuation
    srv
    cfg
    frame
    (Ghost.reveal st)
    network_frame);
  fold (CQ.network_buffers
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out));
  assert (pure (CPI.buffers_wf
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    out_len))
}

fn finish_server_next_action_network
  (srv:SP.canonical_server)
  (cfg:server_next_local_action_config)
  (frame:server_next_local_action_frame)
  (network_frame:SP.tls_server_network_bridge_frame)
  (result:CPI.process_result)
  (input_contents:Ghost.erased B.bytes)
  (input_len:SZ.t)
  (old_out:Ghost.erased B.bytes)
  (out_contents:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  (st1:Ghost.erased CS.connection_state)
  (consumed:Ghost.erased B.bytes)
  (wire_outputs:Ghost.erased (list CW.wire_message))
  (local_outputs:Ghost.erased (list CTypes.local_output))
requires
  server_next_local_action_network_continuation
    srv
    cfg
    frame
    (Ghost.reveal st0)
    network_frame **
  SP.server_network_bridge_frame_post
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
    (Ghost.reveal local_outputs)
ensures
  server_next_local_action_frame_ready
    srv
    cfg
    frame
    (Ghost.reveal st1)
{
  unfold (server_next_local_action_network_continuation
    srv
    cfg
    frame
    (Ghost.reveal st0)
    network_frame);
  unfold (SP.server_network_bridge_frame_post
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
    (Ghost.reveal local_outputs));
  with app_out. _;
  rewrite
    (pts_to
      network_frame.SP.tls_server_network_bridge_base.SP.tls_server_network_app_out
      app_out)
    as
    (pts_to frame.server_query_network_app_out app_out);
  with app_out.
  fold (server_network_persistent_resource frame);
  fold (server_next_local_action_frame_ready
    srv
    cfg
    frame
    (Ghost.reveal st1))
}

fn prepare_server_next_action_local
  (srv:SP.canonical_server)
  (cfg:server_next_local_action_config)
  (frame:server_next_local_action_frame)
  (ev:CTypes.server_local_event)
  (local_frame:SP.tls_server_local_bridge_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (st:Ghost.erased CS.connection_state)
  (old_out:Ghost.erased B.bytes)
requires
  server_next_local_action_frame_post
    srv
    cfg
    frame
    (Ghost.reveal st)
    (CQ.NextLocal ev local_frame) **
  CQ.local_output_buffer
    out
    out_len
    (Ghost.reveal old_out)
ensures
  SP.server_local_bridge_frame_pre
    ev
    local_frame
    (Ghost.reveal st)
    out
    out_len
    (Ghost.reveal old_out) **
  server_next_local_action_local_continuation
    srv
    cfg
    frame
    (Ghost.reveal st)
    ev
    local_frame **
  CQ.local_output_buffer
    out
    out_len
    (Ghost.reveal old_out)
{
  unfold (server_next_local_action_frame_post
    srv
    cfg
    frame
    (Ghost.reveal st)
    (CQ.NextLocal ev local_frame));
  unfold (CQ.local_output_buffer
    out
    out_len
    (Ghost.reveal old_out));
  unfold (server_local_frame_resource local_frame);
  server_local_event_ready_payload_empty (Ghost.reveal st) ev;
  server_local_event_ready_input_wf (Ghost.reveal st) ev;
  Seq.lemma_eq_elim
    (CTypes.server_local_event_api ev).CTypes.server_local_payload
    B.empty;
  assert (pure (B.length
    (CTypes.server_local_event_api ev).CTypes.server_local_payload ==
    SZ.v local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload_len));
  assert (pure (B.length (Ghost.reveal old_out) == SZ.v out_len));
  assert (pure (B.length
    (Ghost.reveal
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out) ==
    SZ.v local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out_len));
  assert (pure (ST.server_local_event_input_ready
    (Ghost.reveal st)
    (CTypes.server_local_event_api ev).CTypes.server_local_kind
    (CTypes.server_local_event_api ev).CTypes.server_local_payload));
  assert (pure (server_local_frame_matches frame local_frame));
  assert (pure (SZ.v frame.server_query_local_payload_len == 0));
  rewrite
    (pts_to
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
      B.empty)
    as
    (pts_to
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
      (CTypes.server_local_event_api ev).CTypes.server_local_payload);
  fold (SP.server_local_bridge_frame_pre
    ev
    local_frame
    (Ghost.reveal st)
    out
    out_len
    (Ghost.reveal old_out));
  fold (server_next_local_action_local_continuation
    srv
    cfg
    frame
    (Ghost.reveal st)
    ev
    local_frame);
  fold (CQ.local_output_buffer
    out
    out_len
    (Ghost.reveal old_out))
}

fn finish_server_next_action_local
  (srv:SP.canonical_server)
  (cfg:server_next_local_action_config)
  (frame:server_next_local_action_frame)
  (ev:CTypes.server_local_event)
  (local_frame:SP.tls_server_local_bridge_frame)
  (result:CPI.process_result)
  (old_out:Ghost.erased B.bytes)
  (out_contents:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  (st1:Ghost.erased CS.connection_state)
  (wire_outputs:Ghost.erased (list CW.wire_message))
  (local_outputs:Ghost.erased (list CTypes.local_output))
requires
  server_next_local_action_local_continuation
    srv
    cfg
    frame
    (Ghost.reveal st0)
    ev
    local_frame **
  SP.server_local_bridge_frame_post
    ev
    local_frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs)
ensures
  server_next_local_action_frame_ready
    srv
    cfg
    frame
    (Ghost.reveal st1)
{
  unfold (server_next_local_action_local_continuation
    srv
    cfg
    frame
    (Ghost.reveal st0)
    ev
    local_frame);
  unfold (SP.server_local_bridge_frame_post
    ev
    local_frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs));
  with app_out. _;
  unfold (server_network_persistent_resource frame);
  with network_current. _;
  server_local_event_ready_payload_empty (Ghost.reveal st0) ev;
  Seq.lemma_eq_elim
    (CTypes.server_local_event_api ev).CTypes.server_local_payload
    B.empty;
  assert (pure (server_local_frame_matches frame local_frame));
  assert (pure (SZ.v frame.server_query_local_payload_len == 0));
  assert (pure (B.length (Ghost.reveal app_out) ==
    SZ.v frame.server_query_local_app_out_len));
  rewrite
    (pts_to
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
      (CTypes.server_local_event_api ev).CTypes.server_local_payload)
    as
    (pts_to frame.server_query_local_payload B.empty);
  rewrite
    (pts_to
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
      app_out)
    as
    (pts_to frame.server_query_local_app_out app_out);
  with app_out.
  fold (server_local_persistent_resource frame);
  with network_current.
  fold (server_network_persistent_resource frame);
  fold (server_next_local_action_frame_ready
    srv
    cfg
    frame
    (Ghost.reveal st1))
}

fn return_server_payload_free_action
  (srv:SP.canonical_server)
  (cfg:server_next_local_action_config)
  (frame:server_next_local_action_frame)
  (kind:ST.local_event_kind)
  (local_frame:SP.tls_server_local_bridge_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
  (network_current:Ghost.erased B.bytes)
  (local_current:Ghost.erased B.bytes)
requires
  SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  pts_to frame.server_query_network_app_out (Ghost.reveal network_current) **
  pts_to frame.server_query_local_payload B.empty **
  pts_to frame.server_query_local_app_out (Ghost.reveal local_current) **
  pure (
    B.length (Ghost.reveal network_current) ==
      SZ.v frame.server_query_network_app_out_len /\
    B.length (Ghost.reveal local_current) ==
      SZ.v frame.server_query_local_app_out_len /\
    SZ.v frame.server_query_local_payload_len == 0 /\
    server_local_frame_matches frame local_frame /\
    (Ghost.reveal
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out) ==
      (Ghost.reveal local_current) /\
    ST.server_local_event_input_ready (Ghost.reveal st) kind B.empty)
returns action:CQ.next_action
  SP.tls_server_network_bridge_frame
  CTypes.server_local_event
  SP.tls_server_local_bridge_frame
  server_deferred_action
ensures
  SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  server_next_local_action_frame_post
    srv
    cfg
    frame
    (Ghost.reveal st)
    action
{
  let api = {
    CTypes.server_local_kind = kind;
    CTypes.server_local_payload = B.empty;
  };
  rewrite
    (pts_to frame.server_query_local_payload B.empty)
    as
    (pts_to
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
      B.empty);
  rewrite
    (pts_to frame.server_query_local_app_out (Ghost.reveal local_current))
    as
    (pts_to
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
      (Ghost.reveal
        local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out));
  fold (server_local_frame_resource local_frame);
  with network_current.
  fold (server_network_persistent_resource frame);
  assert (pure (server_local_event_ready
    (Ghost.reveal st)
    (CTypes.ServerAPI api)));
  fold (server_next_local_action_frame_post
    srv
    cfg
    frame
    (Ghost.reveal st)
    (CQ.NextLocal (CTypes.ServerAPI api) local_frame));
  CQ.NextLocal (CTypes.ServerAPI api) local_frame
}

fn run_server_next_local_action
  (srv:SP.canonical_server)
  (cfg:server_next_local_action_config)
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
  server_next_local_action_frame_ready
    srv
    cfg
    frame
    (Ghost.reveal st)
returns action:CQ.next_action
  SP.tls_server_network_bridge_frame
  CTypes.server_local_event
  SP.tls_server_local_bridge_frame
  server_deferred_action
ensures
  SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  server_next_local_action_frame_post
    srv
    cfg
    frame
    (Ghost.reveal st)
    action
{
  unfold (SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  unfold (server_next_local_action_frame_ready
    srv
    cfg
    frame
    (Ghost.reveal st));
  unfold (server_network_persistent_resource frame);
  with network_current. _;
  unfold (server_local_persistent_resource frame);
  with local_current. _;
  let network_frame =
    server_network_frame_of_current frame (Ghost.hide network_current);
  let local_frame =
    server_local_frame_of_current frame (Ghost.hide local_current);
  assert (pure (SP.server_invariant_pure
    (Ghost.reveal srv.SP.canonical_server_initial)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)));
  assert (pure (ST.server_state_correct (Ghost.reveal st)));
  let tls_action =
    S.next_local_action
      srv.SP.canonical_server_state;
  let action = server_next_action_of_tls network_frame local_frame tls_action;
  server_next_action_correct
    (Ghost.reveal st)
    network_frame
    local_frame
    tls_action;
  fold (SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  if tls_action.ST.next_local_ready {
    match tls_action.ST.next_local_kind {
      ST.LocalStartServer -> {
        server_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_server_payload_free_action srv cfg frame ST.LocalStartServer local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      ST.LocalSelectServerParameters -> {
        with network_current.
        fold (server_network_persistent_resource frame);
        with local_current.
        fold (server_local_persistent_resource frame);
        fold (server_next_local_action_frame_ready
          srv
          cfg
          frame
          (Ghost.reveal st));
        assert (pure (server_deferred_action_ready
          (Ghost.reveal st)
          ServerDeferredSelectServerParameters));
        fold (server_next_local_action_frame_post
          srv
          cfg
          frame
          (Ghost.reveal st)
          (CQ.NextDeferredLocal ServerDeferredSelectServerParameters));
        CQ.NextDeferredLocal ServerDeferredSelectServerParameters
      }
      ST.LocalDeriveSharedSecret -> {
        with network_current.
        fold (server_network_persistent_resource frame);
        with local_current.
        fold (server_local_persistent_resource frame);
        fold (server_next_local_action_frame_ready
          srv
          cfg
          frame
          (Ghost.reveal st));
        assert (pure (server_deferred_action_ready
          (Ghost.reveal st)
          ServerDeferredDeriveSharedSecret));
        fold (server_next_local_action_frame_post
          srv
          cfg
          frame
          (Ghost.reveal st)
          (CQ.NextDeferredLocal ServerDeferredDeriveSharedSecret));
        CQ.NextDeferredLocal ServerDeferredDeriveSharedSecret
      }
      ST.LocalInstallClientHandshakeTrafficKeys -> {
        server_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_server_payload_free_action srv cfg frame ST.LocalInstallClientHandshakeTrafficKeys local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      ST.LocalInstallServerHandshakeTrafficKeys -> {
        server_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_server_payload_free_action srv cfg frame ST.LocalInstallServerHandshakeTrafficKeys local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      ST.LocalInstallClientApplicationTrafficKeys -> {
        server_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_server_payload_free_action srv cfg frame ST.LocalInstallClientApplicationTrafficKeys local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      ST.LocalInstallServerApplicationTrafficKeys -> {
        server_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_server_payload_free_action srv cfg frame ST.LocalInstallServerApplicationTrafficKeys local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      ST.LocalSignCertificateVerify -> {
        with network_current.
        fold (server_network_persistent_resource frame);
        with local_current.
        fold (server_local_persistent_resource frame);
        fold (server_next_local_action_frame_ready
          srv
          cfg
          frame
          (Ghost.reveal st));
        assert (pure (server_deferred_action_ready
          (Ghost.reveal st)
          ServerDeferredSignCertificateVerify));
        fold (server_next_local_action_frame_post
          srv
          cfg
          frame
          (Ghost.reveal st)
          (CQ.NextDeferredLocal ServerDeferredSignCertificateVerify));
        CQ.NextDeferredLocal ServerDeferredSignCertificateVerify
      }
      ST.LocalVerifyClientFinished -> {
        server_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_server_payload_free_action srv cfg frame ST.LocalVerifyClientFinished local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      ST.LocalDeliverApplicationData -> {
        server_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_server_payload_free_action srv cfg frame ST.LocalDeliverApplicationData local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      ST.LocalSendServerHello -> {
        with network_current.
        fold (server_network_persistent_resource frame);
        with local_current.
        fold (server_local_persistent_resource frame);
        fold (server_next_local_action_frame_ready
          srv
          cfg
          frame
          (Ghost.reveal st));
        assert (pure (server_deferred_action_ready
          (Ghost.reveal st)
          ServerDeferredSendServerHello));
        fold (server_next_local_action_frame_post
          srv
          cfg
          frame
          (Ghost.reveal st)
          (CQ.NextDeferredLocal ServerDeferredSendServerHello));
        CQ.NextDeferredLocal ServerDeferredSendServerHello
      }
      ST.LocalSendEncryptedExtensions -> {
        server_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_server_payload_free_action srv cfg frame ST.LocalSendEncryptedExtensions local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      ST.LocalSendCertificate -> {
        server_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_server_payload_free_action srv cfg frame ST.LocalSendCertificate local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      ST.LocalSendCertificateVerify -> {
        server_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_server_payload_free_action srv cfg frame ST.LocalSendCertificateVerify local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      ST.LocalSendServerFinished -> {
        server_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_server_payload_free_action srv cfg frame ST.LocalSendServerFinished local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      ST.LocalSendApplicationData -> {
        server_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_server_payload_free_action srv cfg frame ST.LocalSendApplicationData local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      ST.LocalSendCloseNotify -> {
        server_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_server_payload_free_action srv cfg frame ST.LocalSendCloseNotify local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      ST.LocalFail -> {
        server_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_server_payload_free_action srv cfg frame ST.LocalFail local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
    }
  } else {
    assert (pure ((Ghost.reveal
      network_frame.SP.tls_server_network_bridge_base.SP.tls_server_network_old_app_out) ==
      network_current));
    rewrite
      (pts_to frame.server_query_network_app_out network_current)
      as
      (pts_to
        network_frame.SP.tls_server_network_bridge_base.SP.tls_server_network_app_out
        (Ghost.reveal
          network_frame.SP.tls_server_network_bridge_base.SP.tls_server_network_old_app_out));
    fold (server_network_frame_resource network_frame);
    with local_current.
    fold (server_local_persistent_resource frame);
    assert (pure (server_network_frame_matches frame network_frame));
    fold (server_next_local_action_frame_post
      srv
      cfg
      frame
      (Ghost.reveal st)
      (CQ.NextNeedInput network_frame));
    CQ.NextNeedInput network_frame
  }
}
