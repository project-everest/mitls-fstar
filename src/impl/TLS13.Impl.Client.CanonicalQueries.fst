module TLS13.Impl.Client.CanonicalQueries

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module C = TLS13.Impl.Client
module CP = TLS13.Impl.Client.CanonicalProtocol
module CQ = Common.ConnectionStateQuery
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.ConnectionState
module CT = TLS13.Impl.Client.Types
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Impl.CanonicalWire
module CPI = Common.ProtocolImplementation
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

noeq
type client_next_local_action_query = {
  client_query_network_out_len: SZ.t;
  client_query_certificate_public_key_len: SZ.t;
  client_query_server_finished_payload_len: SZ.t;
}

type client_external_action =
  | ClientExternalValidateCertificate
  | ClientExternalVerifyCertificateSignature

let client_local_event_of_kind
  (kind:CT.local_event_kind)
  : CTypes.client_local_event =
  CTypes.ClientAPI {
    CTypes.client_local_kind = kind;
    CTypes.client_local_payload = B.empty;
  }

let client_next_action_of_tls
  (action:CT.next_local_action)
  : CQ.next_action CTypes.client_local_event client_external_action =
  if action.CT.next_local_ready then
    match action.CT.next_local_kind with
    | CT.LocalValidateCertificate ->
      CQ.NextExternal ClientExternalValidateCertificate
    | CT.LocalVerifyCertificateSignature ->
      CQ.NextExternal ClientExternalVerifyCertificateSignature
    | _ ->
      CQ.NextLocal (client_local_event_of_kind action.CT.next_local_kind)
  else
    CQ.NextNeedInput

let client_network_enabled
  (_cc:CP.canonical_client)
  (_q:client_next_local_action_query)
  (_st:CS.connection_state)
  : prop =
  True

let client_local_enabled
  (_cc:CP.canonical_client)
  (_q:client_next_local_action_query)
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
  | CTypes.ClientGhostStep ->
    False

let client_external_enabled
  (_cc:CP.canonical_client)
  (q:client_next_local_action_query)
  (st:CS.connection_state)
  (ext:client_external_action)
  : prop =
  match ext with
  | ClientExternalValidateCertificate ->
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsCertificateReceived /\
    st.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der /\
    SZ.v q.client_query_certificate_public_key_len <=
      Bounds.max_public_key_len
  | ClientExternalVerifyCertificateSignature ->
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
    st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false

let client_done_enabled
  (_cc:CP.canonical_client)
  (_q:client_next_local_action_query)
  (_st:CS.connection_state)
  : prop =
  True

let client_failed_enabled
  (_cc:CP.canonical_client)
  (_q:client_next_local_action_query)
  (_st:CS.connection_state)
  : prop =
  True

let client_next_action_correct
  (cc:CP.canonical_client)
  (q:client_next_local_action_query)
  (st:CS.connection_state)
  (tls_action:CT.next_local_action)
  : Lemma
      (requires
        C.next_local_action_sound
          st
          q.client_query_network_out_len
          q.client_query_certificate_public_key_len
          q.client_query_server_finished_payload_len
          tls_action)
      (ensures
        CQ.next_action_correct
          client_network_enabled
          client_local_enabled
          client_external_enabled
          client_done_enabled
          client_failed_enabled
          cc
          q
          st
          (client_next_action_of_tls tls_action))
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
  (_action:CQ.next_action CTypes.client_local_event client_external_action)
  : slprop =
  emp

[@@pulse_unfold]
let client_next_action_network_frame_pre
  (_cc:CP.canonical_client)
  (_q:client_next_local_action_query)
  (frame:CP.tls_client_network_bridge_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (input_contents:B.bytes)
  (old_out:B.bytes)
  : slprop =
  CP.client_network_bridge_frame_pre
    frame
    input
    input_len
    out
    out_len
    input_contents
    old_out

fn prepare_client_next_action_network
  (cc:CP.canonical_client)
  (q:client_next_local_action_query)
  (frame:CP.tls_client_network_bridge_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (st:Ghost.erased CS.connection_state)
  (input_contents:Ghost.erased B.bytes)
  (old_out:Ghost.erased B.bytes)
requires
  client_next_action_network_frame_pre
    cc
    q
    frame
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out) **
  pure (client_network_enabled cc q (Ghost.reveal st))
ensures
  CP.client_network_bridge_frame_pre
    frame
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out)
{
  unfold (client_next_action_network_frame_pre
    cc
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
let client_next_action_local_frame_pre
  (_cc:CP.canonical_client)
  (_q:client_next_local_action_query)
  (ev:CTypes.client_local_event)
  (frame:CP.tls_client_local_frame)
  (st:CS.connection_state)
  (out:array U8.t)
  (out_len:SZ.t)
  (old_out:B.bytes)
  : slprop =
  CP.client_local_frame_pre ev frame st out out_len old_out

fn prepare_client_next_action_local
  (cc:CP.canonical_client)
  (q:client_next_local_action_query)
  (ev:CTypes.client_local_event)
  (frame:CP.tls_client_local_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (st:Ghost.erased CS.connection_state)
  (old_out:Ghost.erased B.bytes)
requires
  client_next_action_local_frame_pre
    cc
    q
    ev
    frame
    (Ghost.reveal st)
    out
    out_len
    (Ghost.reveal old_out) **
  pure (client_local_enabled cc q (Ghost.reveal st) ev)
ensures
  CP.client_local_frame_pre
    ev
    frame
    (Ghost.reveal st)
    out
    out_len
    (Ghost.reveal old_out)
{
  unfold (client_next_action_local_frame_pre
    cc
    q
    ev
    frame
    (Ghost.reveal st)
    out
    out_len
    (Ghost.reveal old_out))
}

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
returns action:CQ.next_action CTypes.client_local_event client_external_action
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
  pure (CQ.next_action_correct
    client_network_enabled
    client_local_enabled
    client_external_enabled
    client_done_enabled
    client_failed_enabled
    cc
    q
    (Ghost.reveal st)
    action)
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
  let tls_action =
    C.next_local_action
      cc.CP.canonical_client_state
      q.client_query_network_out_len
      q.client_query_certificate_public_key_len
      q.client_query_server_finished_payload_len;
  let action = client_next_action_of_tls tls_action;
  client_next_action_correct cc q (Ghost.reveal st) tls_action;
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
      client_external_action
      CP.client_protocol_implementation
  =
  {
    CQ.csq_frame = client_next_local_action_frame;
    CQ.csq_frame_pre = client_next_local_action_frame_pre;
    CQ.csq_frame_post = client_next_local_action_frame_post;
    CQ.csq_network_enabled = client_network_enabled;
    CQ.csq_local_enabled = client_local_enabled;
    CQ.csq_external_enabled = client_external_enabled;
    CQ.csq_done_enabled = client_done_enabled;
    CQ.csq_failed_enabled = client_failed_enabled;
    CQ.csq_network_frame_pre = client_next_action_network_frame_pre;
    CQ.csq_prepare_network = prepare_client_next_action_network;
    CQ.csq_local_frame_pre = client_next_action_local_frame_pre;
    CQ.csq_prepare_local = prepare_client_next_action_local;
    CQ.csq_next_action = run_client_next_local_action;
  }
