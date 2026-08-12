module TLS13.Impl.Client.CanonicalQueries

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module C = TLS13.Impl.Client
module CP = TLS13.Impl.Client.CanonicalProtocol
module CQ = TLS13.Impl.ConnectionStateQuery
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Spec.Endpoint.Wire
module EAPI = TLS13.Spec.Endpoint.API
module L = TLS13.Impl.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

noeq
type client_next_local_action_config = {
  client_query_network_out_len: SZ.t;
  client_query_certificate_public_key_len: SZ.t;
  client_query_server_finished_payload_len: SZ.t;
}

type client_deferred_action =
  | ClientDeferredValidateCertificate
  | ClientDeferredVerifyCertificateSignature

noeq
type client_next_local_action_frame = {
  client_query_network_app_out: array U8.t;
  client_query_network_app_out_len: SZ.t;
  client_query_local_payload: array U8.t;
  client_query_local_payload_len: SZ.t;
  client_query_local_app_out: array U8.t;
  client_query_local_app_out_len: SZ.t;
}

let client_network_frame_of_current
  (frame:client_next_local_action_frame)
  (old:Ghost.erased B.bytes)
  : CP.tls_client_network_bridge_frame =
  let base = {
    CP.tls_client_network_app_out = frame.client_query_network_app_out;
    CP.tls_client_network_app_out_len = frame.client_query_network_app_out_len;
    CP.tls_client_network_old_app_out = old;
  } in
  {
    CP.tls_client_network_bridge_base = base;
  }

let client_local_frame_of_current
  (frame:client_next_local_action_frame)
  (old:Ghost.erased B.bytes)
  : CP.tls_client_local_frame =
  {
    CP.tls_client_local_payload = frame.client_query_local_payload;
    CP.tls_client_local_payload_len = frame.client_query_local_payload_len;
    CP.tls_client_local_app_out = frame.client_query_local_app_out;
    CP.tls_client_local_app_out_len = frame.client_query_local_app_out_len;
    CP.tls_client_local_old_app_out = old;
  }

let client_network_frame_matches
  (frame:client_next_local_action_frame)
  (network_frame:CP.tls_client_network_bridge_frame)
  : prop =
  network_frame.CP.tls_client_network_bridge_base.CP.tls_client_network_app_out ==
    frame.client_query_network_app_out /\
  network_frame.CP.tls_client_network_bridge_base.CP.tls_client_network_app_out_len ==
    frame.client_query_network_app_out_len /\
  L.max_record_fragment_len <= SZ.v frame.client_query_network_app_out_len

let client_local_frame_matches
  (frame:client_next_local_action_frame)
  (local_frame:CP.tls_client_local_frame)
  : prop =
  local_frame.CP.tls_client_local_payload == frame.client_query_local_payload /\
  local_frame.CP.tls_client_local_payload_len == frame.client_query_local_payload_len /\
  local_frame.CP.tls_client_local_app_out == frame.client_query_local_app_out /\
  local_frame.CP.tls_client_local_app_out_len == frame.client_query_local_app_out_len

let client_local_event_of_kind
  (kind:CT.local_event_kind)
  : CTypes.client_local_event =
  CTypes.ClientAPI {
    CTypes.client_local_kind = kind;
    CTypes.client_local_payload = B.empty;
  }

let client_next_action_of_tls
  (network_frame:CP.tls_client_network_bridge_frame)
  (local_frame:CP.tls_client_local_frame)
  (action:CT.next_local_action)
  : CQ.next_action
      CP.tls_client_network_bridge_frame
      CTypes.client_local_event
      CP.tls_client_local_frame
      client_deferred_action =
  if action.CT.next_local_ready then
    match action.CT.next_local_kind with
    | CT.LocalValidateCertificate ->
      CQ.NextDeferredLocal ClientDeferredValidateCertificate
    | CT.LocalVerifyCertificateSignature ->
      CQ.NextDeferredLocal ClientDeferredVerifyCertificateSignature
    | _ ->
      CQ.NextLocal
        (client_local_event_of_kind action.CT.next_local_kind)
        local_frame
  else
    CQ.NextNeedInput network_frame

let client_local_event_ready
  (st:CS.connection_state)
  (ev:CTypes.client_local_event)
  : prop =
  match ev with
  | CTypes.ClientAPI api ->
    Seq.equal api.CTypes.client_local_payload B.empty /\
    CT.local_input_wf
      st
      api.CTypes.client_local_kind
      api.CTypes.client_local_payload
  | CTypes.ClientValidateCertificate payload ->
    Seq.equal (Ghost.reveal payload) B.empty /\
    CT.local_input_wf st CT.LocalValidateCertificate (Ghost.reveal payload)

let client_local_event_from_query
  (ev:CTypes.client_local_event)
  : prop =
  match ev with
  | CTypes.ClientAPI _ -> True
  | CTypes.ClientValidateCertificate _ -> False

let client_local_event_ready_payload_empty
  (st:CS.connection_state)
  (ev:CTypes.client_local_event)
  : Lemma
      (requires client_local_event_ready st ev)
      (ensures Seq.equal
        (CTypes.client_local_event_api ev).CTypes.client_local_payload
        B.empty)
=
  match ev with
  | CTypes.ClientAPI _ -> ()
  | CTypes.ClientValidateCertificate _ -> ()

let client_local_event_ready_input_wf
  (st:CS.connection_state)
  (ev:CTypes.client_local_event)
  : Lemma
      (requires client_local_event_ready st ev)
      (ensures CT.local_input_wf
        st
        (CTypes.client_local_event_api ev).CTypes.client_local_kind
        (CTypes.client_local_event_api ev).CTypes.client_local_payload)
=
  match ev with
  | CTypes.ClientAPI _ -> ()
  | CTypes.ClientValidateCertificate _ -> ()

let client_deferred_action_ready
  (cfg:client_next_local_action_config)
  (st:CS.connection_state)
  (ext:client_deferred_action)
  : prop =
  match ext with
  | ClientDeferredValidateCertificate ->
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsCertificateReceived /\
    st.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der /\
    SZ.v cfg.client_query_certificate_public_key_len <= Bounds.max_public_key_len
  | ClientDeferredVerifyCertificateSignature ->
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
    st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false

let client_next_action_correct
  (cfg:client_next_local_action_config)
  (st:CS.connection_state)
  (network_frame:CP.tls_client_network_bridge_frame)
  (local_frame:CP.tls_client_local_frame)
  (tls_action:CT.next_local_action)
  : Lemma
      (requires
        C.next_local_action_sound
          st
          cfg.client_query_network_out_len
          cfg.client_query_certificate_public_key_len
          cfg.client_query_server_finished_payload_len
          tls_action)
      (ensures
        (match client_next_action_of_tls network_frame local_frame tls_action with
        | CQ.NextNeedInput _ -> True
        | CQ.NextLocal ev _ -> client_local_event_ready st ev
        | CQ.NextDeferredLocal ext -> client_deferred_action_ready cfg st ext
        | CQ.NextDone -> True
        | CQ.NextFailed -> True))
=
  if tls_action.CT.next_local_ready then (
    match tls_action.CT.next_local_kind with
    | CT.LocalValidateCertificate -> ()
    | CT.LocalVerifyCertificateSignature -> ()
    | _ ->
      assert (C.next_local_action_internal_input_ready st tls_action);
      assert (CT.local_input_wf st tls_action.CT.next_local_kind B.empty);
      assert (Seq.equal B.empty B.empty)
  ) else (
    ()
  )

let client_payload_free_action_ready
  (cfg:client_next_local_action_config)
  (st:CS.connection_state)
  (tls_action:CT.next_local_action)
  : Lemma
      (requires
        C.next_local_action_sound
          st
          cfg.client_query_network_out_len
          cfg.client_query_certificate_public_key_len
          cfg.client_query_server_finished_payload_len
          tls_action /\
        tls_action.CT.next_local_ready == true /\
        tls_action.CT.next_local_kind <> CT.LocalValidateCertificate /\
        tls_action.CT.next_local_kind <> CT.LocalVerifyCertificateSignature)
      (ensures
        client_local_event_ready
          st
          (client_local_event_of_kind tls_action.CT.next_local_kind))
=
  assert (C.next_local_action_internal_input_ready st tls_action);
  assert (CT.local_input_wf st tls_action.CT.next_local_kind B.empty);
  assert (Seq.equal B.empty B.empty)

let client_internal_ready_implies_kind_ready
  (st:CS.connection_state)
  (tls_action:CT.next_local_action)
  : Lemma
      (requires
        C.next_local_action_internal_input_ready st tls_action /\
        tls_action.CT.next_local_ready == true)
      (ensures
        (match tls_action.CT.next_local_kind with
        | CT.LocalValidateCertificate
        | CT.LocalVerifyCertificateSignature ->
          True
        | _ ->
          CT.local_input_wf st tls_action.CT.next_local_kind B.empty))
=
  ()

[@@pulse_unfold]
let client_network_persistent_resource
  (frame:client_next_local_action_frame)
  : slprop =
  exists* (current:B.bytes).
    pts_to frame.client_query_network_app_out current **
    pure (
      B.length current == SZ.v frame.client_query_network_app_out_len /\
      L.max_record_fragment_len <= SZ.v frame.client_query_network_app_out_len)

[@@pulse_unfold]
let client_local_persistent_resource
  (frame:client_next_local_action_frame)
  : slprop =
  exists* (current:B.bytes).
    pts_to frame.client_query_local_payload B.empty **
    pts_to frame.client_query_local_app_out current **
    pure (
      SZ.v frame.client_query_local_payload_len == 0 /\
      B.length current == SZ.v frame.client_query_local_app_out_len)

[@@pulse_unfold]
let client_network_frame_resource
  (frame:CP.tls_client_network_bridge_frame)
  : slprop =
  pts_to
    frame.CP.tls_client_network_bridge_base.CP.tls_client_network_app_out
    (Ghost.reveal
      frame.CP.tls_client_network_bridge_base.CP.tls_client_network_old_app_out) **
  pure (
    B.length
      (Ghost.reveal
        frame.CP.tls_client_network_bridge_base.CP.tls_client_network_old_app_out) ==
      SZ.v frame.CP.tls_client_network_bridge_base.CP.tls_client_network_app_out_len /\
    L.max_record_fragment_len <=
      SZ.v frame.CP.tls_client_network_bridge_base.CP.tls_client_network_app_out_len)

[@@pulse_unfold]
let client_local_frame_resource
  (frame:CP.tls_client_local_frame)
  : slprop =
  pts_to frame.CP.tls_client_local_payload B.empty **
  pts_to
    frame.CP.tls_client_local_app_out
    (Ghost.reveal frame.CP.tls_client_local_old_app_out) **
  pure (
    SZ.v frame.CP.tls_client_local_payload_len == 0 /\
    B.length (Ghost.reveal frame.CP.tls_client_local_old_app_out) ==
      SZ.v frame.CP.tls_client_local_app_out_len)

[@@pulse_unfold]
let client_next_local_action_frame_ready
  (_cc:CP.canonical_client)
  (_cfg:client_next_local_action_config)
  (frame:client_next_local_action_frame)
  (_st:CS.connection_state)
  : slprop =
  client_network_persistent_resource frame **
  client_local_persistent_resource frame

[@@pulse_unfold]
let client_next_local_action_frame_post
  (cc:CP.canonical_client)
  (cfg:client_next_local_action_config)
  (frame:client_next_local_action_frame)
  (st:CS.connection_state)
  (action:CQ.next_action
    CP.tls_client_network_bridge_frame
    CTypes.client_local_event
    CP.tls_client_local_frame
    client_deferred_action)
  : slprop =
  match action with
  | CQ.NextNeedInput network_frame ->
    client_network_frame_resource network_frame **
    client_local_persistent_resource frame **
    pure (client_network_frame_matches frame network_frame)
  | CQ.NextLocal ev local_frame ->
    client_local_frame_resource local_frame **
    client_network_persistent_resource frame **
    pure (
      client_local_event_ready st ev /\
      client_local_frame_matches frame local_frame /\
      SZ.v frame.client_query_local_payload_len == 0 /\
      client_local_event_from_query ev)
  | CQ.NextDeferredLocal ext ->
    client_next_local_action_frame_ready cc cfg frame st **
    pure (client_deferred_action_ready cfg st ext)
  | CQ.NextDone
  | CQ.NextFailed ->
    client_next_local_action_frame_ready cc cfg frame st

[@@pulse_unfold]
let client_next_local_action_network_continuation
  (_cc:CP.canonical_client)
  (_cfg:client_next_local_action_config)
  (frame:client_next_local_action_frame)
  (_st:CS.connection_state)
  (network_frame:CP.tls_client_network_bridge_frame)
  : slprop =
  client_local_persistent_resource frame **
  pure (client_network_frame_matches frame network_frame)

[@@pulse_unfold]
let client_next_local_action_local_continuation
  (cc:CP.canonical_client)
  (cfg:client_next_local_action_config)
  (frame:client_next_local_action_frame)
  (st:CS.connection_state)
  (ev:CTypes.client_local_event)
  (local_frame:CP.tls_client_local_frame)
  : slprop =
  client_network_persistent_resource frame **
  pure (
    client_local_event_ready st ev /\
    client_local_frame_matches frame local_frame /\
    SZ.v frame.client_query_local_payload_len == 0)

fn cancel_client_next_action
  (cc:CP.canonical_client)
  (cfg:client_next_local_action_config)
  (frame:client_next_local_action_frame)
  (st:Ghost.erased CS.connection_state)
  (action:CQ.next_action
    CP.tls_client_network_bridge_frame
    CTypes.client_local_event
    CP.tls_client_local_frame
    client_deferred_action)
requires
  client_next_local_action_frame_post
    cc
    cfg
    frame
    (Ghost.reveal st)
    action
ensures
  client_next_local_action_frame_ready
    cc
    cfg
    frame
    (Ghost.reveal st)
{
  unfold (client_next_local_action_frame_post
    cc
    cfg
    frame
    (Ghost.reveal st)
    action);
  match action {
    CQ.NextNeedInput network_frame -> {
      unfold (client_network_frame_resource network_frame);
      unfold (client_next_local_action_network_continuation
        cc
        cfg
        frame
        (Ghost.reveal st)
        network_frame);
      rewrite
        (pts_to
          network_frame.CP.tls_client_network_bridge_base.CP.tls_client_network_app_out
          (Ghost.reveal
            network_frame.CP.tls_client_network_bridge_base.CP.tls_client_network_old_app_out))
        as
        (pts_to
          frame.client_query_network_app_out
          (Ghost.reveal
            network_frame.CP.tls_client_network_bridge_base.CP.tls_client_network_old_app_out));
      let old_network: Ghost.erased B.bytes =
        network_frame.CP.tls_client_network_bridge_base.CP.tls_client_network_old_app_out;
      with old_network.
      fold (client_network_persistent_resource frame);
      fold (client_next_local_action_frame_ready
        cc
        cfg
        frame
        (Ghost.reveal st))
    }
    CQ.NextLocal ev local_frame -> {
      unfold (client_local_frame_resource local_frame);
      rewrite
        (pts_to local_frame.CP.tls_client_local_payload B.empty)
        as
        (pts_to frame.client_query_local_payload B.empty);
      rewrite
        (pts_to
          local_frame.CP.tls_client_local_app_out
          (Ghost.reveal local_frame.CP.tls_client_local_old_app_out))
        as
        (pts_to
          frame.client_query_local_app_out
          (Ghost.reveal local_frame.CP.tls_client_local_old_app_out));
      let old_local: Ghost.erased B.bytes =
        local_frame.CP.tls_client_local_old_app_out;
      with old_local.
      fold (client_local_persistent_resource frame);
      fold (client_next_local_action_frame_ready
        cc
        cfg
        frame
        (Ghost.reveal st))
    }
    CQ.NextDeferredLocal ext -> {
      fold (client_next_local_action_frame_ready
        cc
        cfg
        frame
        (Ghost.reveal st))
    }
    CQ.NextDone -> {
      fold (client_next_local_action_frame_ready
        cc
        cfg
        frame
        (Ghost.reveal st))
    }
    CQ.NextFailed -> {
      fold (client_next_local_action_frame_ready
        cc
        cfg
        frame
        (Ghost.reveal st))
    }
  }
}

fn prepare_client_next_action_network
  (cc:CP.canonical_client)
  (cfg:client_next_local_action_config)
  (frame:client_next_local_action_frame)
  (network_frame:CP.tls_client_network_bridge_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (st:Ghost.erased CS.connection_state)
  (input_contents:Ghost.erased B.bytes)
  (old_out:Ghost.erased B.bytes)
requires
  client_next_local_action_frame_post
    cc
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
  CP.client_network_bridge_frame_pre
    network_frame
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out) **
  client_next_local_action_network_continuation
    cc
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
    Common.ProtocolImplementation.buffers_wf
      (Ghost.reveal input_contents)
      input_len
      (Ghost.reveal old_out)
      out_len)
{
  unfold (client_next_local_action_frame_post
    cc
    cfg
    frame
    (Ghost.reveal st)
    (CQ.NextNeedInput network_frame));
  unfold (client_network_frame_resource network_frame);
  unfold (CQ.network_buffers
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out));
  fold (CP.client_network_bridge_frame_pre
    network_frame
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out));
  fold (client_next_local_action_network_continuation
    cc
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
  assert (pure (Common.ProtocolImplementation.buffers_wf
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    out_len))
}

fn finish_client_next_action_network
  (cc:CP.canonical_client)
  (cfg:client_next_local_action_config)
  (frame:client_next_local_action_frame)
  (network_frame:CP.tls_client_network_bridge_frame)
  (result:Common.ProtocolImplementation.process_result)
  (input_contents:Ghost.erased B.bytes)
  (input_len:SZ.t)
  (old_out:Ghost.erased B.bytes)
  (out_contents:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  (st1:Ghost.erased CS.connection_state)
  (consumed:Ghost.erased B.bytes)
  (wire_outputs:Ghost.erased (list CW.wire_message))
  (local_outputs:Ghost.erased (list EAPI.local_output))
requires
  client_next_local_action_network_continuation
    cc
    cfg
    frame
    (Ghost.reveal st0)
    network_frame **
  CP.client_network_bridge_frame_post
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
  client_next_local_action_frame_ready
    cc
    cfg
    frame
    (Ghost.reveal st1)
{
  unfold (client_next_local_action_network_continuation
    cc
    cfg
    frame
    (Ghost.reveal st0)
    network_frame);
  unfold (CP.client_network_bridge_frame_post
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
      network_frame.CP.tls_client_network_bridge_base.CP.tls_client_network_app_out
      app_out)
    as
    (pts_to frame.client_query_network_app_out app_out);
  with app_out.
  fold (client_network_persistent_resource frame);
  fold (client_next_local_action_frame_ready
    cc
    cfg
    frame
    (Ghost.reveal st1))
}

fn prepare_client_next_action_local
  (cc:CP.canonical_client)
  (cfg:client_next_local_action_config)
  (frame:client_next_local_action_frame)
  (ev:CTypes.client_local_event)
  (local_frame:CP.tls_client_local_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (st:Ghost.erased CS.connection_state)
  (old_out:Ghost.erased B.bytes)
requires
  client_next_local_action_frame_post
    cc
    cfg
    frame
    (Ghost.reveal st)
    (CQ.NextLocal ev local_frame) **
  CQ.local_output_buffer
    out
    out_len
    (Ghost.reveal old_out)
ensures
  CP.client_local_frame_pre
    ev
    local_frame
    (Ghost.reveal st)
    out
    out_len
    (Ghost.reveal old_out) **
  client_next_local_action_local_continuation
    cc
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
  unfold (CQ.local_output_buffer
    out
    out_len
    (Ghost.reveal old_out));
  unfold (client_local_frame_resource local_frame);
  client_local_event_ready_payload_empty (Ghost.reveal st) ev;
  client_local_event_ready_input_wf (Ghost.reveal st) ev;
  Seq.lemma_eq_elim
    (CTypes.client_local_event_api ev).CTypes.client_local_payload
    B.empty;
  assert (pure (B.length
    (CTypes.client_local_event_api ev).CTypes.client_local_payload ==
    SZ.v local_frame.CP.tls_client_local_payload_len));
  assert (pure (B.length (Ghost.reveal old_out) == SZ.v out_len));
  assert (pure (B.length (Ghost.reveal local_frame.CP.tls_client_local_old_app_out) ==
    SZ.v local_frame.CP.tls_client_local_app_out_len));
  assert (pure (CT.local_input_wf
    (Ghost.reveal st)
    (CTypes.client_local_event_api ev).CTypes.client_local_kind
    (CTypes.client_local_event_api ev).CTypes.client_local_payload));
  assert (pure (client_local_frame_matches frame local_frame));
  assert (pure (SZ.v frame.client_query_local_payload_len == 0));
  rewrite
    (pts_to local_frame.CP.tls_client_local_payload B.empty)
    as
    (pts_to
      local_frame.CP.tls_client_local_payload
      (CTypes.client_local_event_api ev).CTypes.client_local_payload);
  fold (CP.client_local_frame_pre
    ev
    local_frame
    (Ghost.reveal st)
    out
    out_len
    (Ghost.reveal old_out));
  fold (client_next_local_action_local_continuation
    cc
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

fn finish_client_next_action_local
  (cc:CP.canonical_client)
  (cfg:client_next_local_action_config)
  (frame:client_next_local_action_frame)
  (ev:CTypes.client_local_event)
  (local_frame:CP.tls_client_local_frame)
  (result:Common.ProtocolImplementation.process_result)
  (old_out:Ghost.erased B.bytes)
  (out_contents:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  (st1:Ghost.erased CS.connection_state)
  (wire_outputs:Ghost.erased (list CW.wire_message))
  (local_outputs:Ghost.erased (list EAPI.local_output))
requires
  client_next_local_action_local_continuation
    cc
    cfg
    frame
    (Ghost.reveal st0)
    ev
    local_frame **
  CP.client_local_frame_post
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
  client_next_local_action_frame_ready
    cc
    cfg
    frame
    (Ghost.reveal st1)
{
  unfold (client_next_local_action_local_continuation
    cc
    cfg
    frame
    (Ghost.reveal st0)
    ev
    local_frame);
  unfold (CP.client_local_frame_post
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
  unfold (client_network_persistent_resource frame);
  with network_current. _;
  client_local_event_ready_payload_empty (Ghost.reveal st0) ev;
  Seq.lemma_eq_elim
    (CTypes.client_local_event_api ev).CTypes.client_local_payload
    B.empty;
  assert (pure (client_local_frame_matches frame local_frame));
  assert (pure (SZ.v frame.client_query_local_payload_len == 0));
  assert (pure (B.length (Ghost.reveal app_out) ==
    SZ.v frame.client_query_local_app_out_len));
  rewrite
    (pts_to
      local_frame.CP.tls_client_local_payload
      (CTypes.client_local_event_api ev).CTypes.client_local_payload)
    as
    (pts_to frame.client_query_local_payload B.empty);
  rewrite
    (pts_to local_frame.CP.tls_client_local_app_out app_out)
    as
    (pts_to frame.client_query_local_app_out app_out);
  with app_out.
  fold (client_local_persistent_resource frame);
  with network_current.
  fold (client_network_persistent_resource frame);
  fold (client_next_local_action_frame_ready
    cc
    cfg
    frame
    (Ghost.reveal st1))
}

fn return_client_payload_free_action
  (cc:CP.canonical_client)
  (cfg:client_next_local_action_config)
  (frame:client_next_local_action_frame)
  (kind:CT.local_event_kind)
  (local_frame:CP.tls_client_local_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
  (network_current:Ghost.erased B.bytes)
  (local_current:Ghost.erased B.bytes)
requires
  CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  pts_to frame.client_query_network_app_out (Ghost.reveal network_current) **
  pts_to frame.client_query_local_payload B.empty **
  pts_to frame.client_query_local_app_out (Ghost.reveal local_current) **
  pure (
    B.length (Ghost.reveal network_current) ==
      SZ.v frame.client_query_network_app_out_len /\
    L.max_record_fragment_len <= SZ.v frame.client_query_network_app_out_len /\
    B.length (Ghost.reveal local_current) ==
      SZ.v frame.client_query_local_app_out_len /\
    SZ.v frame.client_query_local_payload_len == 0 /\
    client_local_frame_matches frame local_frame /\
    (Ghost.reveal local_frame.CP.tls_client_local_old_app_out) ==
      (Ghost.reveal local_current) /\
    CT.local_input_wf (Ghost.reveal st) kind B.empty)
returns action:CQ.next_action
  CP.tls_client_network_bridge_frame
  CTypes.client_local_event
  CP.tls_client_local_frame
  client_deferred_action
ensures
  CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  client_next_local_action_frame_post
    cc
    cfg
    frame
    (Ghost.reveal st)
    action
{
  let api = {
    CTypes.client_local_kind = kind;
    CTypes.client_local_payload = B.empty;
  };
  rewrite
    (pts_to frame.client_query_local_payload B.empty)
    as
    (pts_to local_frame.CP.tls_client_local_payload B.empty);
  rewrite
    (pts_to frame.client_query_local_app_out (Ghost.reveal local_current))
    as
    (pts_to
      local_frame.CP.tls_client_local_app_out
      (Ghost.reveal local_frame.CP.tls_client_local_old_app_out));
  fold (client_local_frame_resource local_frame);
  with network_current.
  fold (client_network_persistent_resource frame);
  assert (pure (client_local_event_ready
    (Ghost.reveal st)
    (CTypes.ClientAPI api)));
  fold (client_next_local_action_frame_post
    cc
    cfg
    frame
    (Ghost.reveal st)
    (CQ.NextLocal (CTypes.ClientAPI api) local_frame));
  CQ.NextLocal (CTypes.ClientAPI api) local_frame
}

fn run_client_next_local_action
  (cc:CP.canonical_client)
  (cfg:client_next_local_action_config)
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
  client_next_local_action_frame_ready
    cc
    cfg
    frame
    (Ghost.reveal st)
returns action:CQ.next_action
  CP.tls_client_network_bridge_frame
  CTypes.client_local_event
  CP.tls_client_local_frame
  client_deferred_action
ensures
  CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  client_next_local_action_frame_post
    cc
    cfg
    frame
    (Ghost.reveal st)
    action
{
  unfold (CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  unfold (client_next_local_action_frame_ready
    cc
    cfg
    frame
    (Ghost.reveal st));
  unfold (client_network_persistent_resource frame);
  with network_current. _;
  unfold (client_local_persistent_resource frame);
  with local_current. _;
  let network_frame =
    client_network_frame_of_current frame (Ghost.hide network_current);
  let local_frame =
    client_local_frame_of_current frame (Ghost.hide local_current);
  rewrite
    (C.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st))
    as
    (CR.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st));
  let tls_action =
    C.next_local_action
      cc.CP.canonical_client_state
      cfg.client_query_network_out_len
      cfg.client_query_certificate_public_key_len
      cfg.client_query_server_finished_payload_len;
  let action = client_next_action_of_tls network_frame local_frame tls_action;
  client_next_action_correct cfg (Ghost.reveal st) network_frame local_frame tls_action;
  rewrite
    (CR.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st))
    as
    (C.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st));
  fold (CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  if tls_action.CT.next_local_ready {
    match tls_action.CT.next_local_kind {
      CT.LocalValidateCertificate -> {
        with network_current.
        fold (client_network_persistent_resource frame);
        with local_current.
        fold (client_local_persistent_resource frame);
        fold (client_next_local_action_frame_ready
          cc
          cfg
          frame
          (Ghost.reveal st));
        fold (client_next_local_action_frame_post
          cc
          cfg
          frame
          (Ghost.reveal st)
          (CQ.NextDeferredLocal ClientDeferredValidateCertificate));
        CQ.NextDeferredLocal ClientDeferredValidateCertificate
      }
      CT.LocalVerifyCertificateSignature -> {
        with network_current.
        fold (client_network_persistent_resource frame);
        with local_current.
        fold (client_local_persistent_resource frame);
        fold (client_next_local_action_frame_ready
          cc
          cfg
          frame
          (Ghost.reveal st));
        fold (client_next_local_action_frame_post
          cc
          cfg
          frame
          (Ghost.reveal st)
          (CQ.NextDeferredLocal ClientDeferredVerifyCertificateSignature));
        CQ.NextDeferredLocal ClientDeferredVerifyCertificateSignature
      }
      CT.LocalStartHandshake -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalStartHandshake local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      CT.LocalDeriveSharedSecret -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalDeriveSharedSecret local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      CT.LocalInstallClientHandshakeTrafficKeys -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalInstallClientHandshakeTrafficKeys local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      CT.LocalInstallServerHandshakeTrafficKeys -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalInstallServerHandshakeTrafficKeys local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      CT.LocalInstallClientApplicationTrafficKeys -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalInstallClientApplicationTrafficKeys local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      CT.LocalInstallServerApplicationTrafficKeys -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalInstallServerApplicationTrafficKeys local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      CT.LocalVerifyFinished -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalVerifyFinished local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      CT.LocalDeliverApplicationData -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalDeliverApplicationData local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      CT.LocalSendClientHello -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalSendClientHello local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      CT.LocalSendClientFinished -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalSendClientFinished local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      CT.LocalSendApplicationData -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalSendApplicationData local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      CT.LocalSendKeyUpdate -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalSendKeyUpdate local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      CT.LocalSendKeyUpdateRequested -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalSendKeyUpdateRequested local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      CT.LocalSendCloseNotify -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalSendCloseNotify local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
      CT.LocalFail -> {
        client_internal_ready_implies_kind_ready (Ghost.reveal st) tls_action;
        return_client_payload_free_action cc cfg frame CT.LocalFail local_frame received sent st (Ghost.hide network_current) (Ghost.hide local_current)
      }
    }
  } else {
    assert (pure ((Ghost.reveal
      network_frame.CP.tls_client_network_bridge_base.CP.tls_client_network_old_app_out) ==
      network_current));
    rewrite
      (pts_to frame.client_query_network_app_out network_current)
      as
      (pts_to
        network_frame.CP.tls_client_network_bridge_base.CP.tls_client_network_app_out
        (Ghost.reveal
          network_frame.CP.tls_client_network_bridge_base.CP.tls_client_network_old_app_out));
    fold (client_network_frame_resource network_frame);
    with local_current.
    fold (client_local_persistent_resource frame);
    assert (pure (client_network_frame_matches frame network_frame));
    fold (client_next_local_action_frame_post
      cc
      cfg
      frame
      (Ghost.reveal st)
      (CQ.NextNeedInput network_frame));
    CQ.NextNeedInput network_frame
  }
}
