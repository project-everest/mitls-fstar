module TLS13.Impl.Client.Engine

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module C = TLS13.Impl.Client
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module L = TLS13.Impl.Messages
module Sem = TLS13.Wire.Semantics
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Trace = TLS13.Trace
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec

noeq
type client_engine = {
  engine_client: C.client;
  engine_empty_payload: V.vec U8.t;
}

inline_for_extraction
let engine_action_tag (action:engine_action) : FStar.UInt64.t =
  match action with
  | EngineProgress -> 0UL
  | EngineNeedNetworkInput -> 1UL
  | EngineNeedCertificateVerification -> 2UL
  | EngineNeedCertificateSignatureVerification -> 3UL
  | EngineNetworkOutput -> 4UL
  | EngineApplicationData -> 5UL
  | EngineReady -> 6UL
  | EngineClosing -> 7UL
  | EngineClosed -> 8UL
  | EngineFailed -> 9UL

inline_for_extraction
let engine_status_tag (status:CT.client_status) : FStar.UInt64.t =
  match status with
  | CT.StepOk -> 0UL
  | CT.NeedMoreInput -> 1UL
  | CT.DecodeError -> 2UL
  | CT.IllegalTransition -> 3UL
  | CT.OutputBufferTooSmall -> 4UL
  | CT.ConnectionFailed -> 5UL

fn trace_engine_result
  (event:FStar.UInt32.t)
  (result:engine_step_result)
  requires emp
  ensures emp
{
  Trace.emit
    event
    (engine_action_tag result.engine_step_action)
    (engine_status_tag result.engine_step_status)
    (SZ.sizet_to_uint64 result.engine_step_consumed_len);
}

let engine_live
  (e:client_engine)
  (st:CS.connection_state)
  : slprop =
  CR.connection_exactly e.engine_client st **
  (exists* empty_payload.
    V.pts_to e.engine_empty_payload #1.0R empty_payload **
    pure (V.is_full_vec e.engine_empty_payload /\
          B.length empty_payload == 0 /\
          CT.client_end_to_end_invariant st))

let engine_released
  (e:client_engine)
  (st:CS.connection_state)
  : slprop =
  CR.connection_released e.engine_client st

inline_for_extraction
let local_action_from_response
  (resp:CT.client_response)
  : engine_action =
  match resp.CT.status with
  | CT.StepOk ->
    if resp.CT.app_out_len <> 0sz
    then EngineApplicationData
    else if resp.CT.network_out_len <> 0sz
    then EngineNetworkOutput
    else EngineProgress
  | _ -> EngineFailed

inline_for_extraction
let network_action_from_response
  (buffer_resp:CT.client_buffer_response)
  : engine_action =
  match buffer_resp.CT.response.CT.status with
  | CT.NeedMoreInput -> EngineNeedNetworkInput
  | CT.StepOk ->
    if buffer_resp.CT.response.CT.app_out_len <> 0sz
    then EngineApplicationData
    else if buffer_resp.CT.response.CT.network_out_len <> 0sz
    then EngineNetworkOutput
    else EngineProgress
  | _ -> EngineFailed

inline_for_extraction
let local_result
  (resp:CT.client_response)
  : engine_step_result =
  {
    engine_step_action = local_action_from_response resp;
    engine_step_status = resp.CT.status;
    engine_step_consumed_len = 0sz;
    engine_step_network_out_len = resp.CT.network_out_len;
    engine_step_app_out_len = resp.CT.app_out_len;
  }

inline_for_extraction
let network_result
  (buffer_resp:CT.client_buffer_response)
  : engine_step_result =
  {
    engine_step_action = network_action_from_response buffer_resp;
    engine_step_status = buffer_resp.CT.response.CT.status;
    engine_step_consumed_len = buffer_resp.CT.consumed_len;
    engine_step_network_out_len =
      buffer_resp.CT.response.CT.network_out_len;
    engine_step_app_out_len = buffer_resp.CT.response.CT.app_out_len;
  }

inline_for_extraction
let observation_result
  (action:engine_action)
  : engine_step_result =
  {
    engine_step_action = action;
    engine_step_status = CT.StepOk;
    engine_step_consumed_len = 0sz;
    engine_step_network_out_len = 0sz;
    engine_step_app_out_len = 0sz;
  }

inline_for_extraction
let action_from_control_snapshot
  (snapshot:CR.control_snapshot)
  : engine_action =
  if U8.eq snapshot.CR.snapshot_control_tag 2uy
  then EngineReady
  else if U8.eq snapshot.CR.snapshot_control_tag 3uy
  then EngineClosing
  else if U8.eq snapshot.CR.snapshot_control_tag 4uy
  then EngineClosed
  else if U8.eq snapshot.CR.snapshot_control_tag 5uy
  then EngineFailed
  else EngineNeedNetworkInput

noextract
let lemma_local_action_is_not_observation
  (resp:CT.client_response)
  : Lemma
      (ensures
        local_action_from_response resp <>
          EngineNeedCertificateVerification /\
        local_action_from_response resp <>
          EngineNeedCertificateSignatureVerification /\
        local_action_from_response resp <> EngineReady)
=
  match resp.CT.status with
  | CT.StepOk ->
    if resp.CT.app_out_len <> 0sz
    then ()
    else if resp.CT.network_out_len <> 0sz
    then ()
    else ()
  | _ -> ()

fn new_engine
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_context:array U8.t)
  (trust_context_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to server_name 'server_name_bytes **
           pts_to trust_context 'trust_context_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_context_bytes == SZ.v trust_context_len /\
                 SZ.v server_name_len <= Bounds.max_hostname_len /\
                 SZ.v trust_context_len <= Bounds.max_trust_anchors_len)
  returns e:client_engine
  ensures pts_to server_name 'server_name_bytes **
          pts_to trust_context 'trust_context_bytes **
          engine_live
            e
            (CR.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_context_bytes)
              validation_time_seconds)
{
  let c =
    C.new_client
      server_name
      server_name_len
      trust_context
      trust_context_len
      validation_time_seconds;
  let empty_payload = V.alloc 0uy 0sz;
  let e = {
    engine_client = c;
    engine_empty_payload = empty_payload;
  };
  rewrite
    (CR.connection_exactly
      c
      (CR.configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_context_bytes)
        validation_time_seconds))
    as
    (CR.connection_exactly
      e.engine_client
      (CR.configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_context_bytes)
        validation_time_seconds));
  rewrite
    (V.pts_to empty_payload #1.0R (Seq.create 0 0uy))
    as
    (V.pts_to e.engine_empty_payload #1.0R (Seq.create 0 0uy));
  fold (engine_live
    e
    (CR.configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_context_bytes)
      validation_time_seconds));
  Trace.emit Trace.engine_new
    (SZ.sizet_to_uint64 server_name_len)
    (SZ.sizet_to_uint64 trust_context_len)
    (SZ.sizet_to_uint64 validation_time_seconds);
  e
}

fn poll
  (e:client_engine)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v engine_network_out_capacity <= SZ.v network_out_len /\
                 SZ.v engine_app_out_capacity <= SZ.v app_out_len)
  returns result:engine_step_result
  ensures exists* st1 network_out_bytes app_out_bytes.
          engine_live e st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                engine_result_buffers_wf result network_out_bytes app_out_bytes /\
                (result.engine_step_action ==
                   EngineNeedCertificateVerification ==>
                 engine_waiting_for_certificate st1) /\
                (result.engine_step_action ==
                   EngineNeedCertificateSignatureVerification ==>
                 engine_waiting_for_certificate_signature st1) /\
                (result.engine_step_action == EngineReady ==>
                 st1.CS.cs_model.CS.model_control ==
                   CS.ControlApplicationData))
{
  Trace.emit Trace.engine_poll_begin 0UL 0UL 0UL;
  unfold (engine_live e 'st0);
  with empty_payload.
    assert (V.pts_to e.engine_empty_payload #1.0R empty_payload);
  assert (pure (forall (i:nat{i < B.length empty_payload}).
    Seq.index empty_payload i == Seq.index B.empty i));
  Seq.lemma_eq_intro empty_payload B.empty;
  let action =
    C.next_local_action
      e.engine_client
      network_out_len
      engine_public_key_capacity
      36sz;
  assert (pure (C.next_local_action_sound
    'st0
    network_out_len
    engine_public_key_capacity
    36sz
    action));
  if action.CT.next_local_ready {
    assert (pure (C.next_local_action_internal_input_ready 'st0 action));
    let needs_certificate =
      action.CT.next_local_kind = CT.LocalValidateCertificate;
    if needs_certificate {
      let result =
        observation_result EngineNeedCertificateVerification;
      assert (pure (engine_waiting_for_certificate 'st0));
      fold (engine_live e 'st0);
      trace_engine_result Trace.engine_poll_end result;
      result
    } else {
      let needs_signature =
        action.CT.next_local_kind = CT.LocalVerifyCertificateSignature;
      if needs_signature {
        let result =
          observation_result EngineNeedCertificateSignatureVerification;
        assert (pure (engine_waiting_for_certificate_signature 'st0));
        fold (engine_live e 'st0);
        trace_engine_result Trace.engine_poll_end result;
        result
      } else {
        assert (pure (CT.local_input_wf
          'st0
          action.CT.next_local_kind
          B.empty));
        V.to_array_pts_to e.engine_empty_payload;
        let resp =
          C.process_local_event
            e.engine_client
            action.CT.next_local_kind
            (V.vec_to_array e.engine_empty_payload)
            0sz
            network_out
            network_out_len
            app_out
            app_out_len;
        with st1 network_out_bytes app_out_bytes.
          assert (
            CR.connection_exactly e.engine_client st1 **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
        V.to_vec_pts_to e.engine_empty_payload;
        let result = local_result resp;
        assert (pure (CT.client_end_to_end_invariant st1));
        assert (pure (
          engine_result_buffers_wf result network_out_bytes app_out_bytes));
        lemma_local_action_is_not_observation resp;
        fold (engine_live e st1);
        trace_engine_result Trace.engine_poll_end result;
        result
      }
    }
  } else {
    V.to_array_pts_to e.engine_empty_payload;
    let pending =
      C.process_pending_protected_handshake
        e.engine_client
        (V.vec_to_array e.engine_empty_payload);
    with st_pending. assert (
      CR.connection_exactly e.engine_client st_pending);
    V.to_vec_pts_to e.engine_empty_payload;
    match pending {
      None -> {
        assert (pure (st_pending == 'st0));
        rewrite
          (CR.connection_exactly e.engine_client st_pending)
          as
          (CR.connection_exactly e.engine_client 'st0);
        let snapshot = C.control_snapshot e.engine_client;
        let result =
          observation_result (action_from_control_snapshot snapshot);
        assert (pure (
          result.engine_step_action == EngineReady ==>
          'st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
        fold (engine_live e 'st0);
        trace_engine_result Trace.engine_poll_end result;
        result
      }
      Some resp -> {
        let result = local_result resp;
        assert (pure (
          engine_result_buffers_wf
            result
            (Ghost.reveal 'old_network_out)
            (Ghost.reveal 'old_app_out)));
        lemma_local_action_is_not_observation resp;
        fold (engine_live e st_pending);
        trace_engine_result Trace.engine_poll_end result;
        result
      }
    }
  }
}

fn feed_network
  (e:client_engine)
  (network_input:array U8.t)
  (network_input_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to network_input 'network_input_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'network_input_bytes == SZ.v network_input_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v engine_network_out_capacity <= SZ.v network_out_len /\
                 SZ.v engine_app_out_capacity <= SZ.v app_out_len)
  returns result:engine_step_result
  ensures exists* st1 network_out_bytes app_out_bytes.
          engine_live e st1 **
          pts_to network_input 'network_input_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                engine_network_step_correct
                  'st0
                  st1
                  result
                  (Ghost.reveal 'network_input_bytes)
                  'old_network_out
                  network_out_bytes
                  'old_app_out
                  app_out_bytes)
{
  Trace.emit Trace.engine_feed_begin
    (SZ.sizet_to_uint64 network_input_len)
    0UL
    0UL;
  unfold (engine_live e 'st0);
  with empty_payload.
    assert (V.pts_to e.engine_empty_payload #1.0R empty_payload);
  let buffer_resp =
    C.process_coalesced_network_bytes
      e.engine_client
      network_input
      network_input_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (
      CR.connection_exactly e.engine_client st1 **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes);
  let result = network_result buffer_resp;
  assert (pure (CT.client_end_to_end_invariant st1));
  assert (pure (engine_network_result_matches result buffer_resp));
  assert (pure (
    engine_network_step_correct
      'st0
      st1
      result
      (Ghost.reveal 'network_input_bytes)
      'old_network_out
      network_out_bytes
      'old_app_out
      app_out_bytes));
  fold (engine_live e st1);
  trace_engine_result Trace.engine_feed_end result;
  result
}

fn copy_certificate_chain
  (e:client_engine)
  (chain_out:array U8.t)
  (chain_out_len:SZ.t)
  (offsets_out:array SZ.t)
  (offsets_out_len:SZ.t)
  (lens_out:array SZ.t)
  (lens_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to chain_out 'old_chain_out **
           pts_to offsets_out 'old_offsets_out **
           pts_to lens_out 'old_lens_out **
           pure (B.length 'old_chain_out == SZ.v chain_out_len /\
                 Seq.length 'old_offsets_out == SZ.v offsets_out_len /\
                 Seq.length 'old_lens_out == SZ.v lens_out_len /\
                 chain_out_len == engine_certificate_chain_capacity /\
                 offsets_out_len == engine_certificate_chain_entries /\
                 lens_out_len == engine_certificate_chain_entries /\
                 engine_waiting_for_certificate 'st0)
  returns snapshot:CR.certificate_chain_snapshot
  ensures exists* chain_bytes offsets lens.
          engine_live e 'st0 **
          pts_to chain_out chain_bytes **
          pts_to offsets_out offsets **
          pts_to lens_out lens **
          pure (B.length chain_bytes == SZ.v chain_out_len /\
                Seq.length offsets == SZ.v offsets_out_len /\
                Seq.length lens == SZ.v lens_out_len /\
                SZ.v snapshot.CR.certificate_chain_bytes_len <=
                  B.length chain_bytes /\
                SZ.v snapshot.CR.certificate_chain_cert_count <=
                  Seq.length offsets /\
                SZ.v snapshot.CR.certificate_chain_cert_count <=
                  Seq.length lens /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate with
                 | Some cert ->
                   L.certificate_chain_matches
                     chain_bytes
                     (SZ.v snapshot.CR.certificate_chain_bytes_len)
                     offsets
                     lens
                     (SZ.v snapshot.CR.certificate_chain_cert_count)
                     (Sem.certificate_entries cert)
                 | None -> False))
{
  unfold (engine_live e 'st0);
  with empty_payload.
    assert (V.pts_to e.engine_empty_payload #1.0R empty_payload);
  let snapshot =
    C.copy_certificate_chain
      e.engine_client
      chain_out
      chain_out_len
      offsets_out
      offsets_out_len
      lens_out
      lens_out_len;
  fold (engine_live e 'st0);
  Trace.emit Trace.engine_certificate_chain
    (SZ.sizet_to_uint64 snapshot.CR.certificate_chain_bytes_len)
    (SZ.sizet_to_uint64 snapshot.CR.certificate_chain_cert_count)
    0UL;
  snapshot
}

fn copy_certificate_verify_request
  (e:client_engine)
  (input_out:array U8.t)
  (input_out_len:SZ.t)
  (signature_out:array U8.t)
  (signature_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to input_out 'old_input_out **
           pts_to signature_out 'old_signature_out **
           pure (B.length 'old_input_out == SZ.v input_out_len /\
                 B.length 'old_signature_out == SZ.v signature_out_len /\
                 input_out_len == engine_certificate_verify_input_capacity /\
                 signature_out_len == engine_signature_capacity /\
                 engine_waiting_for_certificate_signature 'st0)
  returns request:certificate_verify_request
  ensures exists* input_bytes signature_bytes.
          engine_live e 'st0 **
          pts_to input_out input_bytes **
          pts_to signature_out signature_bytes **
          pure (B.length input_bytes == SZ.v input_out_len /\
                B.length signature_bytes == SZ.v signature_out_len /\
                SZ.v request.certificate_verify_input_len <=
                  B.length input_bytes /\
                SZ.v request.certificate_verify_signature_len <=
                  B.length signature_bytes /\
                (match
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input,
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify
                 with
                 | Some input, Some cv ->
                   B.length input <= B.length input_bytes /\
                   Seq.equal
                     (Seq.slice input_bytes 0 (B.length input))
                     input /\
                   L.signature_scheme_matches
                     request.certificate_verify_signature_scheme
                     (Sem.certificateVerify_scheme cv) /\
                   SZ.v request.certificate_verify_input_len ==
                     B.length input /\
                   SZ.v request.certificate_verify_signature_len ==
                     B.length (Sem.certificateVerify_signature_bytes cv) /\
                   Seq.equal
                     (Seq.slice
                       signature_bytes
                       0
                       (SZ.v request.certificate_verify_signature_len))
                     (Sem.certificateVerify_signature_bytes cv)
                 | _, _ -> False))
{
  unfold (engine_live e 'st0);
  with empty_payload.
    assert (V.pts_to e.engine_empty_payload #1.0R empty_payload);
  let input_len =
    C.copy_certificate_verify_input
      e.engine_client
      input_out
      input_out_len;
  with input_bytes.
    assert (pts_to input_out input_bytes);
  let signature_snapshot =
    C.copy_certificate_verify_signature
      e.engine_client
      signature_out
      signature_out_len;
  with signature_bytes.
    assert (pts_to signature_out signature_bytes);
  assert (pure (
    match
      'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input
    with
    | Some input -> SZ.v input_len == B.length input
    | None -> False));
  let request = {
    certificate_verify_input_len = input_len;
    certificate_verify_signature_scheme =
      signature_snapshot.CR.cv_signature_scheme;
    certificate_verify_signature_len =
      signature_snapshot.CR.cv_signature_len;
  };
  fold (engine_live e 'st0);
  request
}

fn process_external_local_event
  (e:client_engine)
  (kind:CT.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes))
  returns result:engine_step_result
  ensures exists* st1 network_out_bytes app_out_bytes.
          engine_live e st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                engine_local_step_correct
                  'st0
                  st1
                  result
                  kind
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  unfold (engine_live e 'st0);
  with empty_payload.
    assert (V.pts_to e.engine_empty_payload #1.0R empty_payload);
  let resp =
    C.process_local_event
      e.engine_client
      kind
      payload
      payload_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (
      CR.connection_exactly e.engine_client st1 **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes);
  let result = local_result resp;
  assert (pure (CT.client_end_to_end_invariant st1));
  assert (pure (engine_local_result_matches result resp));
  assert (pure (
    engine_local_step_correct
      'st0
      st1
      result
      kind
      (Ghost.reveal 'payload_bytes)
      network_out_bytes
      app_out_bytes));
  fold (engine_live e st1);
  result
}

fn process_empty_local_event
  (e:client_engine)
  (kind:CT.local_event_kind)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf 'st0 kind B.empty)
  returns result:engine_step_result
  ensures exists* st1 network_out_bytes app_out_bytes.
          engine_live e st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                engine_local_step_correct
                  'st0
                  st1
                  result
                  kind
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  unfold (engine_live e 'st0);
  with empty_payload.
    assert (V.pts_to e.engine_empty_payload #1.0R empty_payload);
  assert (pure (forall (i:nat{i < B.length empty_payload}).
    Seq.index empty_payload i == Seq.index B.empty i));
  Seq.lemma_eq_intro empty_payload B.empty;
  V.to_array_pts_to e.engine_empty_payload;
  let resp =
    C.process_local_event
      e.engine_client
      kind
      (V.vec_to_array e.engine_empty_payload)
      0sz
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (
      CR.connection_exactly e.engine_client st1 **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes);
  V.to_vec_pts_to e.engine_empty_payload;
  let result = local_result resp;
  assert (pure (CT.client_end_to_end_invariant st1));
  assert (pure (engine_local_result_matches result resp));
  assert (pure (
    engine_local_step_correct
      'st0
      st1
      result
      kind
      B.empty
      network_out_bytes
      app_out_bytes));
  fold (engine_live e st1);
  result
}

fn complete_certificate_verification
  (e:client_engine)
  (public_key:array U8.t)
  (public_key_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to public_key 'public_key_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'public_key_bytes == SZ.v public_key_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v public_key_len <= Bounds.max_public_key_len /\
                 SZ.v engine_network_out_capacity <= SZ.v network_out_len /\
                 SZ.v engine_app_out_capacity <= SZ.v app_out_len /\
                 engine_external_certificate_validation
                   'st0
                   (Ghost.reveal 'public_key_bytes))
  returns result:engine_step_result
  ensures exists* st1 network_out_bytes app_out_bytes.
          engine_live e st1 **
          pts_to public_key 'public_key_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                engine_local_step_correct
                  'st0
                  st1
                  result
                  CT.LocalValidateCertificate
                  (Ghost.reveal 'public_key_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  Trace.emit Trace.engine_certificate_verified
    (SZ.sizet_to_uint64 public_key_len)
    0UL
    0UL;
  let result = process_external_local_event
    e
    CT.LocalValidateCertificate
    public_key
    public_key_len
    network_out
    network_out_len
    app_out
    app_out_len;
  trace_engine_result Trace.engine_certificate_verified result;
  result
}

fn complete_certificate_signature_verification
  (e:client_engine)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v engine_network_out_capacity <= SZ.v network_out_len /\
                 SZ.v engine_app_out_capacity <= SZ.v app_out_len /\
                 engine_external_signature_validation 'st0)
  returns result:engine_step_result
  ensures exists* st1 network_out_bytes app_out_bytes.
          engine_live e st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                engine_local_step_correct
                  'st0
                  st1
                  result
                  CT.LocalVerifyCertificateSignature
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  Trace.emit Trace.engine_certificate_signature_verified 0UL 0UL 0UL;
  let result = process_empty_local_event
    e
    CT.LocalVerifyCertificateSignature
    network_out
    network_out_len
    app_out
    app_out_len;
  trace_engine_result Trace.engine_certificate_signature_verified result;
  result
}

fn send_application_data
  (e:client_engine)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v payload_len <= 16384 /\
                 SZ.v engine_network_out_capacity <= SZ.v network_out_len /\
                 SZ.v engine_app_out_capacity <= SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns result:engine_step_result
  ensures exists* st1 network_out_bytes app_out_bytes.
          engine_live e st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                engine_local_step_correct
                  'st0
                  st1
                  result
                  CT.LocalSendApplicationData
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  Trace.emit Trace.engine_send_application
    (SZ.sizet_to_uint64 payload_len)
    0UL
    0UL;
  let result = process_external_local_event
    e
    CT.LocalSendApplicationData
    payload
    payload_len
    network_out
    network_out_len
    app_out
    app_out_len;
  trace_engine_result Trace.engine_send_application result;
  result
}

fn send_close_notify
  (e:client_engine)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v engine_network_out_capacity <= SZ.v network_out_len /\
                 SZ.v engine_app_out_capacity <= SZ.v app_out_len /\
                 CT.local_input_wf 'st0 CT.LocalSendCloseNotify B.empty)
  returns result:engine_step_result
  ensures exists* st1 network_out_bytes app_out_bytes.
          engine_live e st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                engine_local_step_correct
                  'st0
                  st1
                  result
                  CT.LocalSendCloseNotify
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  Trace.emit Trace.engine_send_close 0UL 0UL 0UL;
  let result = process_empty_local_event
    e
    CT.LocalSendCloseNotify
    network_out
    network_out_len
    app_out
    app_out_len;
  trace_engine_result Trace.engine_send_close result;
  result
}

fn free_engine
  (e:client_engine)
  requires engine_live e 'st0
  ensures engine_released e 'st0
{
  Trace.emit Trace.engine_free 0UL 0UL 0UL;
  unfold (engine_live e 'st0);
  with empty_payload.
    assert (V.pts_to e.engine_empty_payload #1.0R empty_payload);
  fold (CR.connection_exactly e.engine_client 'st0);
  rewrite (CR.connection_exactly e.engine_client 'st0)
    as (C.connection_exactly e.engine_client 'st0);
  V.free e.engine_empty_payload;
  C.free_client e.engine_client;
  rewrite (C.connection_released e.engine_client 'st0)
    as (CR.connection_released e.engine_client 'st0);
  fold (engine_released e 'st0);
}
