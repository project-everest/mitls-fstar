module TLS13.Impl.Client.Endpoint

#lang-pulse

open Pulse.Lib.Pervasives
module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module C = TLS13.Impl.Client
module CL = TLS13.ConnectionLog
module CP = TLS13.Impl.Client.CanonicalProtocol
module CQ = TLS13.Impl.ConnectionStateQuery
module CPI = Common.ProtocolImplementation
module CQueries = TLS13.Impl.Client.CanonicalQueries
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.ConnectionState
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Impl.CanonicalWire
module CT = TLS13.Impl.Client.Types
module L = TLS13.Impl.Messages
module O = TLS13.OpenSSL
module PE = Common.ProtocolEndpoint
module Box = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module SC = TLS13.Impl.Serializer.Common
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TCP = Common.TCP
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec

noeq
type client_endpoint_frame = {
  client_ep_query: CQueries.client_next_local_action_frame;
  client_ep_raw_len: SZ.t;
  client_ep_raw: V.vec U8.t;
  client_ep_network_out_len: SZ.t;
  client_ep_network_out: V.vec U8.t;
  client_ep_auth: O.auth_context;
  client_ep_auth_leaf_der_len: SZ.t;
  client_ep_auth_leaf_der: V.vec U8.t;
  client_ep_auth_payload_len: SZ.t;
  client_ep_auth_payload: V.vec U8.t;
  client_ep_auth_cv_input_len: SZ.t;
  client_ep_auth_cv_input: V.vec U8.t;
  client_ep_auth_signature_len: SZ.t;
  client_ep_auth_signature: V.vec U8.t;
}

let client_endpoint_config_wf
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  : prop =
  frame.client_ep_network_out_len == cfg.CQueries.client_query_network_out_len /\
  frame.client_ep_auth_payload_len == cfg.CQueries.client_query_certificate_public_key_len

let client_endpoint_auth_static_ready
  (frame:client_endpoint_frame)
  : slprop =
  exists* leaf_der_bytes cv_input_bytes signature_bytes.
    O.is_auth_context frame.client_ep_auth **
    V.pts_to frame.client_ep_auth_leaf_der #1.0R leaf_der_bytes **
    V.pts_to frame.client_ep_auth_cv_input #1.0R cv_input_bytes **
    V.pts_to frame.client_ep_auth_signature #1.0R signature_bytes **
    pure (
      B.length leaf_der_bytes == SZ.v frame.client_ep_auth_leaf_der_len /\
      Bounds.max_handshake_flight_len <= SZ.v frame.client_ep_auth_leaf_der_len /\
      B.length cv_input_bytes == SZ.v frame.client_ep_auth_cv_input_len /\
      Bounds.max_certificate_verify_input_len <= SZ.v frame.client_ep_auth_cv_input_len /\
      B.length signature_bytes == SZ.v frame.client_ep_auth_signature_len /\
      L.max_signature_len <= SZ.v frame.client_ep_auth_signature_len)

let client_endpoint_auth_payload_ready
  (frame:client_endpoint_frame)
  : slprop =
  exists* payload_bytes.
    V.pts_to frame.client_ep_auth_payload #1.0R payload_bytes **
    pure (
      B.length payload_bytes == SZ.v frame.client_ep_auth_payload_len /\
      SZ.v frame.client_ep_auth_payload_len <= Bounds.max_public_key_len)

let client_endpoint_auth_ready
  (frame:client_endpoint_frame)
  : slprop =
  client_endpoint_auth_static_ready frame **
  client_endpoint_auth_payload_ready frame

let client_endpoint_frame_ready
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (st:CS.connection_state)
  : slprop =
  CQueries.client_next_local_action_frame_ready
    cc
    cfg
    frame.client_ep_query
    st **
  client_endpoint_auth_ready frame **
  pure (client_endpoint_config_wf cfg frame)

let client_endpoint_io_ready
  (_cc:CP.canonical_client)
  (ch:TCP.channel)
  (frame:client_endpoint_frame)
  (_received:B.bytes)
  (sent:B.bytes)
  (_st:CS.connection_state)
  : slprop =
  exists* raw_received raw_bytes network_out_bytes.
    TCP.is_channel ch raw_received sent **
    V.pts_to frame.client_ep_raw #1.0R raw_bytes **
    V.pts_to frame.client_ep_network_out #1.0R network_out_bytes **
    pure (
      B.length raw_bytes == SZ.v frame.client_ep_raw_len /\
      B.length network_out_bytes == SZ.v frame.client_ep_network_out_len)

let client_validate_local_frame_matches
  (frame:client_endpoint_frame)
  (local_frame:CP.tls_client_local_frame)
  : prop =
  local_frame.CP.tls_client_local_payload ==
    V.vec_to_array frame.client_ep_auth_payload /\
  local_frame.CP.tls_client_local_payload_len ==
    frame.client_ep_auth_payload_len /\
  local_frame.CP.tls_client_local_app_out ==
    frame.client_ep_query.CQueries.client_query_local_app_out /\
  local_frame.CP.tls_client_local_app_out_len ==
    frame.client_ep_query.CQueries.client_query_local_app_out_len

let client_validate_local_action_frame
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (st:CS.connection_state)
  (payload:B.bytes)
  (local_frame:CP.tls_client_local_frame)
  : slprop =
  CQueries.client_network_persistent_resource frame.client_ep_query **
  client_endpoint_auth_static_ready frame **
  pts_to local_frame.CP.tls_client_local_payload payload **
  pts_to frame.client_ep_query.CQueries.client_query_local_payload B.empty **
  pts_to
    local_frame.CP.tls_client_local_app_out
    (Ghost.reveal local_frame.CP.tls_client_local_old_app_out) **
  pure (
    B.length payload == SZ.v frame.client_ep_auth_payload_len /\
    SZ.v frame.client_ep_auth_payload_len <= Bounds.max_public_key_len /\
    B.length (Ghost.reveal local_frame.CP.tls_client_local_old_app_out) ==
      SZ.v local_frame.CP.tls_client_local_app_out_len /\
    SZ.v frame.client_ep_query.CQueries.client_query_local_payload_len == 0 /\
    client_validate_local_frame_matches frame local_frame /\
    CT.local_input_wf
      st
      CT.LocalValidateCertificate
      payload /\
    client_endpoint_config_wf cfg frame)

let client_validate_local_continuation
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (st:CS.connection_state)
  (payload:B.bytes)
  (local_frame:CP.tls_client_local_frame)
  : slprop =
  CQueries.client_network_persistent_resource frame.client_ep_query **
  client_endpoint_auth_static_ready frame **
  pts_to frame.client_ep_query.CQueries.client_query_local_payload B.empty **
  pure (
    B.length payload == SZ.v frame.client_ep_auth_payload_len /\
    SZ.v frame.client_ep_auth_payload_len <= Bounds.max_public_key_len /\
    SZ.v frame.client_ep_query.CQueries.client_query_local_payload_len == 0 /\
    client_validate_local_frame_matches frame local_frame /\
    CT.local_input_wf
      st
      CT.LocalValidateCertificate
      payload /\
    client_endpoint_config_wf cfg frame)

let client_endpoint_local_action_frame
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (st:CS.connection_state)
  (ev:CTypes.client_local_event)
  (local_frame:CP.tls_client_local_frame)
  : slprop =
  match ev with
  | CTypes.ClientValidateCertificate payload ->
    client_validate_local_action_frame cfg frame st (Ghost.reveal payload) local_frame
  | CTypes.ClientAPI _ ->
    CQueries.client_next_local_action_frame_post
      cc
      cfg
      frame.client_ep_query
      st
      (CQ.NextLocal ev local_frame) **
    client_endpoint_auth_ready frame **
    pure (client_endpoint_config_wf cfg frame)

let client_endpoint_action_frame
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (st:CS.connection_state)
  (action:PE.endpoint_action
    CP.tls_client_network_bridge_frame
    CTypes.client_local_event
    CP.tls_client_local_frame)
  : slprop =
  (match action with
  | PE.EndpointNeedInput network_frame ->
    CQueries.client_next_local_action_frame_post
      cc
      cfg
      frame.client_ep_query
      st
      (CQ.NextNeedInput network_frame)
  | PE.EndpointLocal ev local_frame ->
    client_endpoint_local_action_frame cc cfg frame st ev local_frame
  | PE.EndpointDone
  | PE.EndpointFailed ->
    CQueries.client_next_local_action_frame_ready cc cfg frame.client_ep_query st) **
  (match action with
  | PE.EndpointLocal _ _ -> emp
  | _ ->
    client_endpoint_auth_ready frame **
    pure (client_endpoint_config_wf cfg frame))

let client_endpoint_network_continuation
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (st:CS.connection_state)
  (network_frame:CP.tls_client_network_bridge_frame)
  : slprop =
  CQueries.client_next_local_action_network_continuation
    cc
    cfg
    frame.client_ep_query
    st
    network_frame **
  client_endpoint_auth_ready frame **
  pure (client_endpoint_config_wf cfg frame)

let client_endpoint_local_continuation
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (st:CS.connection_state)
  (ev:CTypes.client_local_event)
  (local_frame:CP.tls_client_local_frame)
  : slprop =
  match ev with
  | CTypes.ClientValidateCertificate payload ->
    client_validate_local_continuation cfg frame st (Ghost.reveal payload) local_frame
  | CTypes.ClientAPI _ ->
    CQueries.client_next_local_action_local_continuation
      cc
      cfg
      frame.client_ep_query
      st
      ev
      local_frame **
    client_endpoint_auth_ready frame **
    pure (client_endpoint_config_wf cfg frame)

fn client_endpoint_next_action
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  CP.client_invariant cc (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) **
  client_endpoint_frame_ready cc cfg frame (Ghost.reveal st)
returns action:PE.endpoint_action
  CP.tls_client_network_bridge_frame
  CTypes.client_local_event
  CP.tls_client_local_frame
ensures
  CP.client_invariant cc (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) **
  client_endpoint_action_frame cc cfg frame (Ghost.reveal st) action
{
  unfold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st));
  let cq_action =
    CQueries.run_client_next_local_action
      cc
      cfg
      frame.client_ep_query
      received
      sent
      st;
  match cq_action {
    CQ.NextNeedInput network_frame -> {
      fold (client_endpoint_action_frame
        cc
        cfg
        frame
        (Ghost.reveal st)
        (PE.EndpointNeedInput network_frame));
      PE.EndpointNeedInput network_frame
    }
    CQ.NextLocal ev local_frame -> {
      match ev {
        CTypes.ClientAPI api -> {
          fold (CQueries.client_next_local_action_frame_post
            cc
            cfg
            frame.client_ep_query
            (Ghost.reveal st)
            (CQ.NextLocal (CTypes.ClientAPI api) local_frame));
          fold (client_endpoint_local_action_frame
            cc
            cfg
            frame
            (Ghost.reveal st)
            (CTypes.ClientAPI api)
            local_frame);
          fold (client_endpoint_action_frame
            cc
            cfg
            frame
            (Ghost.reveal st)
            (PE.EndpointLocal (CTypes.ClientAPI api) local_frame));
          PE.EndpointLocal (CTypes.ClientAPI api) local_frame
        }
        CTypes.ClientValidateCertificate _ -> {
          CQueries.cancel_client_next_action
            cc
            cfg
            frame.client_ep_query
            st
            (CQ.NextLocal ev local_frame);
          fold (client_endpoint_action_frame
            cc
            cfg
            frame
            (Ghost.reveal st)
            PE.EndpointFailed);
          PE.EndpointFailed
        }
      }
    }
    CQ.NextDeferredLocal ext -> {
      match ext {
        CQueries.ClientDeferredValidateCertificate -> {
          unfold (CQueries.client_next_local_action_frame_post
            cc
            cfg
            frame.client_ep_query
            (Ghost.reveal st)
            (CQ.NextDeferredLocal ext));
          unfold (CQueries.client_next_local_action_frame_ready
            cc
            cfg
            frame.client_ep_query
            (Ghost.reveal st));
          unfold (CQueries.client_network_persistent_resource frame.client_ep_query);
          with network_current. _;
          unfold (CQueries.client_local_persistent_resource frame.client_ep_query);
          with local_current. _;
          unfold (client_endpoint_auth_ready frame);
          unfold (client_endpoint_auth_static_ready frame);
          with leaf_der_bytes cv_input_bytes signature_bytes. _;
          unfold (client_endpoint_auth_payload_ready frame);
          with payload_bytes. _;
          unfold (CP.client_invariant
            cc
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st));
          rewrite
            (C.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st))
            as
            (CR.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st));
          V.to_array_pts_to frame.client_ep_auth_leaf_der;
          let leaf_der_len =
            C.copy_certificate_leaf_der
              cc.CP.canonical_client_state
              (V.vec_to_array frame.client_ep_auth_leaf_der)
              frame.client_ep_auth_leaf_der_len;
          with leaf_der_after.
            assert (CR.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st) **
                    pts_to (V.vec_to_array frame.client_ep_auth_leaf_der) leaf_der_after);
          V.to_array_pts_to frame.client_ep_auth_payload;
          let ok =
            O.validate_certificate_for_local_event
              frame.client_ep_auth
              #st
              (V.vec_to_array frame.client_ep_auth_leaf_der)
              frame.client_ep_auth_leaf_der_len
              leaf_der_len
              (V.vec_to_array frame.client_ep_auth_payload)
              frame.client_ep_auth_payload_len;
          rewrite
            (CR.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st))
            as
            (C.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st));
          fold (CP.client_invariant
            cc
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st));
          if ok {
            with payload_after.
              assert (O.is_auth_context frame.client_ep_auth **
                      pts_to (V.vec_to_array frame.client_ep_auth_leaf_der) leaf_der_after **
                      pts_to (V.vec_to_array frame.client_ep_auth_payload) payload_after);
            assert (pure (CT.local_input_wf
              (Ghost.reveal st)
              CT.LocalValidateCertificate
              payload_after));
            V.to_vec_pts_to frame.client_ep_auth_leaf_der;
            fold (client_endpoint_auth_static_ready frame);
            let local_frame = {
              CP.tls_client_local_payload = V.vec_to_array frame.client_ep_auth_payload;
              CP.tls_client_local_payload_len = frame.client_ep_auth_payload_len;
              CP.tls_client_local_app_out =
                frame.client_ep_query.CQueries.client_query_local_app_out;
              CP.tls_client_local_app_out_len =
                frame.client_ep_query.CQueries.client_query_local_app_out_len;
              CP.tls_client_local_old_app_out = Ghost.hide local_current;
            };
            let ev = CTypes.ClientValidateCertificate (Ghost.hide payload_after);
            rewrite
              (pts_to (V.vec_to_array frame.client_ep_auth_payload) payload_after)
              as
              (pts_to local_frame.CP.tls_client_local_payload payload_after);
            rewrite
              (pts_to frame.client_ep_query.CQueries.client_query_local_app_out (Ghost.reveal local_current))
              as
              (pts_to
                local_frame.CP.tls_client_local_app_out
                (Ghost.reveal local_frame.CP.tls_client_local_old_app_out));
            with network_current.
            fold (CQueries.client_network_persistent_resource frame.client_ep_query);
            fold (client_validate_local_action_frame
              cfg
              frame
              (Ghost.reveal st)
              payload_after
              local_frame);
            fold (client_endpoint_local_action_frame
              cc
              cfg
              frame
              (Ghost.reveal st)
              (CTypes.ClientValidateCertificate (Ghost.hide payload_after))
              local_frame);
            fold (client_endpoint_action_frame
              cc
              cfg
              frame
              (Ghost.reveal st)
              (PE.EndpointLocal
                (CTypes.ClientValidateCertificate (Ghost.hide payload_after))
                local_frame));
            PE.EndpointLocal
              (CTypes.ClientValidateCertificate (Ghost.hide payload_after))
              local_frame
          } else {
            V.to_vec_pts_to frame.client_ep_auth_leaf_der;
            fold (client_endpoint_auth_static_ready frame);
            with payload_after.
              assert (pts_to (V.vec_to_array frame.client_ep_auth_payload) payload_after);
            V.to_vec_pts_to frame.client_ep_auth_payload;
            fold (client_endpoint_auth_payload_ready frame);
            fold (client_endpoint_auth_ready frame);
            with local_current.
            fold (CQueries.client_local_persistent_resource frame.client_ep_query);
            with network_current.
            fold (CQueries.client_network_persistent_resource frame.client_ep_query);
            fold (CQueries.client_next_local_action_frame_ready
              cc
              cfg
              frame.client_ep_query
              (Ghost.reveal st));
            fold (client_endpoint_action_frame
              cc
              cfg
              frame
              (Ghost.reveal st)
              PE.EndpointFailed);
            PE.EndpointFailed
          }
        }
        CQueries.ClientDeferredVerifyCertificateSignature -> {
          unfold (CQueries.client_next_local_action_frame_post
            cc
            cfg
            frame.client_ep_query
            (Ghost.reveal st)
            (CQ.NextDeferredLocal ext));
          unfold (CQueries.client_next_local_action_frame_ready
            cc
            cfg
            frame.client_ep_query
            (Ghost.reveal st));
          unfold (CQueries.client_network_persistent_resource frame.client_ep_query);
          with network_current. _;
          unfold (CQueries.client_local_persistent_resource frame.client_ep_query);
          with local_current. _;
          unfold (client_endpoint_auth_ready frame);
          unfold (client_endpoint_auth_static_ready frame);
          with leaf_der_bytes cv_input_bytes signature_bytes. _;
          unfold (client_endpoint_auth_payload_ready frame);
          with payload_bytes. _;
          unfold (CP.client_invariant
            cc
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st));
          rewrite
            (C.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st))
            as
            (CR.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st));
          V.to_array_pts_to frame.client_ep_auth_cv_input;
          let input_len =
            C.copy_certificate_verify_input
              cc.CP.canonical_client_state
              (V.vec_to_array frame.client_ep_auth_cv_input)
              frame.client_ep_auth_cv_input_len;
          with cv_input_after.
            assert (CR.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st) **
                    pts_to (V.vec_to_array frame.client_ep_auth_cv_input) cv_input_after);
          V.to_array_pts_to frame.client_ep_auth_signature;
          let signature_snapshot =
            C.copy_certificate_verify_signature
              cc.CP.canonical_client_state
              (V.vec_to_array frame.client_ep_auth_signature)
              frame.client_ep_auth_signature_len;
          with signature_after.
            assert (CR.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st) **
                    pts_to (V.vec_to_array frame.client_ep_auth_signature) signature_after);
          let ok =
            O.verify_certificate_signature_for_local_event
              frame.client_ep_auth
              #st
              (V.vec_to_array frame.client_ep_auth_cv_input)
              frame.client_ep_auth_cv_input_len
              input_len
              signature_snapshot.CR.cv_signature_scheme
              (V.vec_to_array frame.client_ep_auth_signature)
              frame.client_ep_auth_signature_len
              signature_snapshot.CR.cv_signature_len;
          rewrite
            (CR.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st))
            as
            (C.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st));
          fold (CP.client_invariant
            cc
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st));
          if ok {
            assert (pure (CT.local_input_wf
              (Ghost.reveal st)
              CT.LocalVerifyCertificateSignature
              B.empty));
            V.to_vec_pts_to frame.client_ep_auth_cv_input;
            V.to_vec_pts_to frame.client_ep_auth_signature;
            fold (client_endpoint_auth_static_ready frame);
            fold (client_endpoint_auth_payload_ready frame);
            fold (client_endpoint_auth_ready frame);
            let local_frame =
              CQueries.client_local_frame_of_current
                frame.client_ep_query
                (Ghost.hide local_current);
            let api = {
              CTypes.client_local_kind = CT.LocalVerifyCertificateSignature;
              CTypes.client_local_payload = B.empty;
            };
            rewrite
              (pts_to frame.client_ep_query.CQueries.client_query_local_payload B.empty)
              as
              (pts_to local_frame.CP.tls_client_local_payload B.empty);
            rewrite
              (pts_to frame.client_ep_query.CQueries.client_query_local_app_out (Ghost.reveal local_current))
              as
              (pts_to
                local_frame.CP.tls_client_local_app_out
                (Ghost.reveal local_frame.CP.tls_client_local_old_app_out));
            fold (CQueries.client_local_frame_resource local_frame);
            with network_current.
            fold (CQueries.client_network_persistent_resource frame.client_ep_query);
            assert (pure (CQueries.client_local_event_ready
              (Ghost.reveal st)
              (CTypes.ClientAPI api)));
            fold (CQueries.client_next_local_action_frame_post
              cc
              cfg
              frame.client_ep_query
              (Ghost.reveal st)
              (CQ.NextLocal (CTypes.ClientAPI api) local_frame));
            fold (client_endpoint_local_action_frame
              cc
              cfg
              frame
              (Ghost.reveal st)
              (CTypes.ClientAPI api)
              local_frame);
            fold (client_endpoint_action_frame
              cc
              cfg
              frame
              (Ghost.reveal st)
              (PE.EndpointLocal (CTypes.ClientAPI api) local_frame));
            PE.EndpointLocal (CTypes.ClientAPI api) local_frame
          } else {
            V.to_vec_pts_to frame.client_ep_auth_cv_input;
            V.to_vec_pts_to frame.client_ep_auth_signature;
            fold (client_endpoint_auth_static_ready frame);
            fold (client_endpoint_auth_payload_ready frame);
            fold (client_endpoint_auth_ready frame);
            with local_current.
            fold (CQueries.client_local_persistent_resource frame.client_ep_query);
            with network_current.
            fold (CQueries.client_network_persistent_resource frame.client_ep_query);
            fold (CQueries.client_next_local_action_frame_ready
              cc
              cfg
              frame.client_ep_query
              (Ghost.reveal st));
            fold (client_endpoint_action_frame
              cc
              cfg
              frame
              (Ghost.reveal st)
              PE.EndpointFailed);
            PE.EndpointFailed
          }
        }
      }
    }
    CQ.NextDone -> {
      CQueries.cancel_client_next_action cc cfg frame.client_ep_query st CQ.NextDone;
      fold (client_endpoint_action_frame
        cc
        cfg
        frame
        (Ghost.reveal st)
        PE.EndpointDone);
      PE.EndpointDone
    }
    CQ.NextFailed -> {
      CQueries.cancel_client_next_action cc cfg frame.client_ep_query st CQ.NextFailed;
      fold (client_endpoint_action_frame
        cc
        cfg
        frame
        (Ghost.reveal st)
        PE.EndpointFailed);
      PE.EndpointFailed
    }
  }
}

fn client_endpoint_cancel_action
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (st:Ghost.erased CS.connection_state)
  (action:PE.endpoint_action
    CP.tls_client_network_bridge_frame
    CTypes.client_local_event
    CP.tls_client_local_frame)
requires client_endpoint_action_frame cc cfg frame (Ghost.reveal st) action
ensures client_endpoint_frame_ready cc cfg frame (Ghost.reveal st)
{
  unfold (client_endpoint_action_frame cc cfg frame (Ghost.reveal st) action);
  match action {
    PE.EndpointNeedInput network_frame -> {
      CQueries.cancel_client_next_action
        cc
        cfg
        frame.client_ep_query
        st
        (CQ.NextNeedInput network_frame);
      fold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st))
    }
    PE.EndpointLocal ev local_frame -> {
      match ev {
        CTypes.ClientValidateCertificate payload -> {
          unfold (client_endpoint_local_action_frame
            cc
            cfg
            frame
            (Ghost.reveal st)
            (CTypes.ClientValidateCertificate payload)
            local_frame);
          unfold (client_validate_local_action_frame
            cfg
            frame
            (Ghost.reveal st)
            (Ghost.reveal payload)
            local_frame);
          rewrite
            (pts_to
              local_frame.CP.tls_client_local_app_out
              (Ghost.reveal local_frame.CP.tls_client_local_old_app_out))
            as
            (pts_to
              frame.client_ep_query.CQueries.client_query_local_app_out
              (Ghost.reveal local_frame.CP.tls_client_local_old_app_out));
          rewrite
            (pts_to
              local_frame.CP.tls_client_local_payload
              (Ghost.reveal payload))
            as
            (pts_to
              (V.vec_to_array frame.client_ep_auth_payload)
              (Ghost.reveal payload));
          V.to_vec_pts_to frame.client_ep_auth_payload;
          fold (client_endpoint_auth_payload_ready frame);
          fold (client_endpoint_auth_ready frame);
          let old_local: Ghost.erased B.bytes =
            local_frame.CP.tls_client_local_old_app_out;
          with old_local.
          fold (CQueries.client_local_persistent_resource frame.client_ep_query);
          fold (CQueries.client_next_local_action_frame_ready
            cc
            cfg
            frame.client_ep_query
            (Ghost.reveal st));
          fold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st))
        }
        CTypes.ClientAPI api -> {
          unfold (client_endpoint_local_action_frame
            cc
            cfg
            frame
            (Ghost.reveal st)
            (CTypes.ClientAPI api)
            local_frame);
          CQueries.cancel_client_next_action
            cc
            cfg
            frame.client_ep_query
            st
            (CQ.NextLocal (CTypes.ClientAPI api) local_frame);
          fold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st))
        }
      }
    }
    PE.EndpointDone -> {
      fold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st))
    }
    PE.EndpointFailed -> {
      fold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st))
    }
  }
}

noeq
type client_network_io = {
  client_nio_input: array U8.t;
  client_nio_input_len: SZ.t;
  client_nio_output: array U8.t;
  client_nio_output_len: SZ.t;
  client_nio_input_contents: Ghost.erased B.bytes;
  client_nio_old_output: Ghost.erased B.bytes;
  client_nio_raw_received: Ghost.erased B.bytes;
}

let client_network_io_continuation
  (_cc:CP.canonical_client)
  (ch:TCP.channel)
  (frame:client_endpoint_frame)
  (_received:B.bytes)
  (sent:B.bytes)
  (_st:CS.connection_state)
  (nio:client_network_io)
  : slprop =
  TCP.is_channel ch (Ghost.reveal nio.client_nio_raw_received) sent **
  pure (
    nio.client_nio_input == V.vec_to_array frame.client_ep_raw /\
    nio.client_nio_output == V.vec_to_array frame.client_ep_network_out /\
    nio.client_nio_output_len == frame.client_ep_network_out_len /\
    B.length (Ghost.reveal nio.client_nio_input_contents) == SZ.v frame.client_ep_raw_len /\
    B.length (Ghost.reveal nio.client_nio_old_output) == SZ.v nio.client_nio_output_len)

let client_network_input (nio:client_network_io) : array U8.t =
  nio.client_nio_input

let client_network_input_len (nio:client_network_io) : SZ.t =
  nio.client_nio_input_len

let client_network_output (nio:client_network_io) : array U8.t =
  nio.client_nio_output

let client_network_output_len (nio:client_network_io) : SZ.t =
  nio.client_nio_output_len

let client_network_input_contents (nio:client_network_io) : Ghost.erased B.bytes =
  nio.client_nio_input_contents

let client_network_old_output (nio:client_network_io) : Ghost.erased B.bytes =
  nio.client_nio_old_output

fn client_prepare_network
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (ch:TCP.channel)
  (network_frame:CP.tls_client_network_bridge_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  client_endpoint_action_frame cc cfg frame (Ghost.reveal st) (PE.EndpointNeedInput network_frame) **
  client_endpoint_io_ready cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
returns nio:client_network_io
ensures
  client_network_io_continuation cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio **
  PE.network_buffers
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    (Ghost.reveal (client_network_input_contents nio))
    (Ghost.reveal (client_network_old_output nio)) **
  CP.client_network_bridge_frame_pre
    network_frame
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    (Ghost.reveal (client_network_input_contents nio))
    (Ghost.reveal (client_network_old_output nio)) **
  client_endpoint_network_continuation cc cfg frame (Ghost.reveal st) network_frame **
  pure (
    CPI.buffers_wf
      (Ghost.reveal (client_network_input_contents nio))
      (client_network_input_len nio)
      (Ghost.reveal (client_network_old_output nio))
      (client_network_output_len nio))
{
  unfold (client_endpoint_io_ready cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw_received raw_bytes network_out_bytes. _;
  V.to_array_pts_to frame.client_ep_raw;
  let nread = TCP.read_full ch (V.vec_to_array frame.client_ep_raw) frame.client_ep_raw_len;
  with raw_after chunk. _;
  let rawe = Ghost.hide (Seq.append raw_received chunk);
  assert (pure (Ghost.reveal rawe == Seq.append raw_received chunk));
  rewrite
    (TCP.is_channel ch (Seq.append raw_received chunk) (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal rawe) (Ghost.reveal sent));
  V.to_array_pts_to frame.client_ep_network_out;
  let inpute = Ghost.hide raw_after;
  let old_oute = Ghost.hide network_out_bytes;
  let nio = {
    client_nio_input = V.vec_to_array frame.client_ep_raw;
    client_nio_input_len = nread;
    client_nio_output = V.vec_to_array frame.client_ep_network_out;
    client_nio_output_len = frame.client_ep_network_out_len;
    client_nio_input_contents = inpute;
    client_nio_old_output = old_oute;
    client_nio_raw_received = rawe;
  };
  rewrite
    (TCP.is_channel ch (Ghost.reveal rawe) (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal nio.client_nio_raw_received) (Ghost.reveal sent));
  fold (client_network_io_continuation cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio);
  unfold (client_endpoint_action_frame cc cfg frame (Ghost.reveal st) (PE.EndpointNeedInput network_frame));
  rewrite
    (pts_to (V.vec_to_array frame.client_ep_raw) raw_after)
    as
    (pts_to (client_network_input nio) (Ghost.reveal (client_network_input_contents nio)));
  rewrite
    (pts_to (V.vec_to_array frame.client_ep_network_out) network_out_bytes)
    as
    (pts_to (client_network_output nio) (Ghost.reveal (client_network_old_output nio)));
  fold (CQ.network_buffers
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    (Ghost.reveal (client_network_input_contents nio))
    (Ghost.reveal (client_network_old_output nio)));
  CQueries.prepare_client_next_action_network
    cc
    cfg
    frame.client_ep_query
    network_frame
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    st
    (client_network_input_contents nio)
    (client_network_old_output nio);
  unfold (CQ.network_buffers
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    (Ghost.reveal (client_network_input_contents nio))
    (Ghost.reveal (client_network_old_output nio)));
  fold (PE.network_buffers
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    (Ghost.reveal (client_network_input_contents nio))
    (Ghost.reveal (client_network_old_output nio)));
  fold (client_endpoint_network_continuation cc cfg frame (Ghost.reveal st) network_frame);
  nio
}

fn client_finish_network_action
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (network_frame:CP.tls_client_network_bridge_frame)
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
  client_endpoint_network_continuation cc cfg frame (Ghost.reveal st0) network_frame **
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
ensures client_endpoint_frame_ready cc cfg frame (Ghost.reveal st1)
{
  unfold (client_endpoint_network_continuation cc cfg frame (Ghost.reveal st0) network_frame);
  CQueries.finish_client_next_action_network
    cc
    cfg
    frame.client_ep_query
    network_frame
    result
    input_contents
    input_len
    old_out
    out_contents
    st0
    st1
    consumed
    wire_outputs
    local_outputs;
  fold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st1))
}

fn client_finish_network_io
  (cc:CP.canonical_client)
  (ch:TCP.channel)
  (frame:client_endpoint_frame)
  (nio:client_network_io)
  (result:CPI.process_result)
  (received0:Ghost.erased B.bytes)
  (sent0:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  (received1:Ghost.erased B.bytes)
  (sent1:Ghost.erased B.bytes)
  (st1:Ghost.erased CS.connection_state)
  (out_contents:Ghost.erased B.bytes)
  (consumed:Ghost.erased B.bytes)
  (wire_outputs:Ghost.erased (list CW.wire_message))
  (local_outputs:Ghost.erased (list CTypes.local_output))
requires
  client_network_io_continuation cc ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) nio **
  pts_to (client_network_input nio) (Ghost.reveal (client_network_input_contents nio)) **
  pts_to (client_network_output nio) (Ghost.reveal out_contents) **
  pure (
    CPI.network_process_correct
      (CP.client_protocol_implementation.CPI.pi_system cc)
      (Ghost.reveal (client_network_input_contents nio))
      (client_network_input_len nio)
      (Ghost.reveal (client_network_old_output nio))
      (Ghost.reveal out_contents)
      (client_network_output_len nio)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      (Ghost.reveal consumed)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs))
ensures client_endpoint_io_ready cc ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
{
  unfold (client_network_io_continuation cc ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) nio);
  CPI.lemma_network_process_sent_output_prefix
    (CP.client_protocol_implementation.CPI.pi_system cc)
    (Ghost.reveal (client_network_input_contents nio))
    (client_network_input_len nio)
    (Ghost.reveal (client_network_old_output nio))
    (Ghost.reveal out_contents)
    (client_network_output_len nio)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal consumed)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs);
  let nwritten = TCP.write ch (client_network_output nio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal nio.client_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel
      ch
      (Ghost.reveal nio.client_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  assert (pure (Seq.equal
    (Ghost.reveal sent1)
    (Seq.append
      (Ghost.reveal sent0)
      (CPI.output_prefix (Ghost.reveal out_contents) result.CPI.process_produced_len))));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal nio.client_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal nio.client_nio_raw_received) (Ghost.reveal sent1));
  rewrite
    (pts_to (client_network_input nio) (Ghost.reveal (client_network_input_contents nio)))
    as
    (pts_to (V.vec_to_array frame.client_ep_raw) (Ghost.reveal (client_network_input_contents nio)));
  rewrite
    (pts_to (client_network_output nio) (Ghost.reveal out_contents))
    as
    (pts_to (V.vec_to_array frame.client_ep_network_out) (Ghost.reveal out_contents));
  V.to_vec_pts_to frame.client_ep_raw;
  V.to_vec_pts_to frame.client_ep_network_out;
  fold (client_endpoint_io_ready cc ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
}

noeq
type client_local_io = {
  client_lio_output: array U8.t;
  client_lio_output_len: SZ.t;
  client_lio_old_output: Ghost.erased B.bytes;
  client_lio_raw_received: Ghost.erased B.bytes;
}

let client_local_io_continuation
  (_cc:CP.canonical_client)
  (ch:TCP.channel)
  (frame:client_endpoint_frame)
  (_received:B.bytes)
  (sent:B.bytes)
  (_st:CS.connection_state)
  (_ev:CTypes.client_local_event)
  (lio:client_local_io)
  : slprop =
  exists* raw_bytes.
    TCP.is_channel ch (Ghost.reveal lio.client_lio_raw_received) sent **
    V.pts_to frame.client_ep_raw #1.0R raw_bytes **
    pure (
      lio.client_lio_output == V.vec_to_array frame.client_ep_network_out /\
      lio.client_lio_output_len == frame.client_ep_network_out_len /\
      B.length (Ghost.reveal lio.client_lio_old_output) == SZ.v lio.client_lio_output_len /\
      B.length raw_bytes == SZ.v frame.client_ep_raw_len)

let client_local_output (lio:client_local_io) : array U8.t =
  lio.client_lio_output

let client_local_output_len (lio:client_local_io) : SZ.t =
  lio.client_lio_output_len

let client_local_old_output (lio:client_local_io) : Ghost.erased B.bytes =
  lio.client_lio_old_output

fn client_prepare_local
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (ch:TCP.channel)
  (ev:CTypes.client_local_event)
  (local_frame:CP.tls_client_local_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  client_endpoint_action_frame cc cfg frame (Ghost.reveal st) (PE.EndpointLocal ev local_frame) **
  client_endpoint_io_ready cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
returns lio:client_local_io
ensures
  client_local_io_continuation cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio **
  PE.local_output_buffer
    (client_local_output lio)
    (client_local_output_len lio)
    (Ghost.reveal (client_local_old_output lio)) **
  CP.client_local_frame_pre
    ev
    local_frame
    (Ghost.reveal st)
    (client_local_output lio)
    (client_local_output_len lio)
    (Ghost.reveal (client_local_old_output lio)) **
  client_endpoint_local_continuation cc cfg frame (Ghost.reveal st) ev local_frame
{
  unfold (client_endpoint_io_ready cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw_received raw_bytes network_out_bytes. _;
  let rawe = Ghost.hide raw_received;
  let old_oute = Ghost.hide network_out_bytes;
  V.to_array_pts_to frame.client_ep_network_out;
  let lio = {
    client_lio_output = V.vec_to_array frame.client_ep_network_out;
    client_lio_output_len = frame.client_ep_network_out_len;
    client_lio_old_output = old_oute;
    client_lio_raw_received = rawe;
  };
  rewrite
    (TCP.is_channel ch raw_received (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal lio.client_lio_raw_received) (Ghost.reveal sent));
  fold (client_local_io_continuation cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio);
  unfold (client_endpoint_action_frame cc cfg frame (Ghost.reveal st) (PE.EndpointLocal ev local_frame));
  rewrite
    (pts_to (V.vec_to_array frame.client_ep_network_out) network_out_bytes)
    as
    (pts_to (client_local_output lio) (Ghost.reveal (client_local_old_output lio)));
  fold (CQ.local_output_buffer
    (client_local_output lio)
    (client_local_output_len lio)
    (Ghost.reveal (client_local_old_output lio)));
  match ev {
    CTypes.ClientValidateCertificate payload -> {
      unfold (client_endpoint_local_action_frame
        cc
        cfg
        frame
        (Ghost.reveal st)
        (CTypes.ClientValidateCertificate payload)
        local_frame);
      unfold (client_validate_local_action_frame
        cfg
        frame
        (Ghost.reveal st)
        (Ghost.reveal payload)
        local_frame);
      unfold (CQ.local_output_buffer
        (client_local_output lio)
        (client_local_output_len lio)
        (Ghost.reveal (client_local_old_output lio)));
      fold (CP.client_local_frame_pre
        (CTypes.ClientValidateCertificate payload)
        local_frame
        (Ghost.reveal st)
        (client_local_output lio)
        (client_local_output_len lio)
        (Ghost.reveal (client_local_old_output lio)));
      fold (client_validate_local_continuation
        cfg
        frame
        (Ghost.reveal st)
        (Ghost.reveal payload)
        local_frame);
      fold (client_endpoint_local_continuation
        cc
        cfg
        frame
        (Ghost.reveal st)
        (CTypes.ClientValidateCertificate payload)
        local_frame);
      fold (PE.local_output_buffer
        (client_local_output lio)
        (client_local_output_len lio)
        (Ghost.reveal (client_local_old_output lio)));
      rewrite
        (client_endpoint_local_continuation
          cc
          cfg
          frame
          (Ghost.reveal st)
          (CTypes.ClientValidateCertificate payload)
          local_frame)
        as
        (client_endpoint_local_continuation
          cc
          cfg
          frame
          (Ghost.reveal st)
          ev
          local_frame);
      rewrite
        (client_local_io_continuation
          cc
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st)
          (CTypes.ClientValidateCertificate payload)
          lio)
        as
        (client_local_io_continuation
          cc
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st)
          ev
          lio);
      lio
    }
    CTypes.ClientAPI api -> {
      unfold (client_endpoint_local_action_frame
        cc
        cfg
        frame
        (Ghost.reveal st)
        (CTypes.ClientAPI api)
        local_frame);
      CQueries.prepare_client_next_action_local
        cc
        cfg
        frame.client_ep_query
        (CTypes.ClientAPI api)
        local_frame
        (client_local_output lio)
        (client_local_output_len lio)
        st
        (client_local_old_output lio);
      unfold (CQ.local_output_buffer
        (client_local_output lio)
        (client_local_output_len lio)
        (Ghost.reveal (client_local_old_output lio)));
      fold (PE.local_output_buffer
        (client_local_output lio)
        (client_local_output_len lio)
        (Ghost.reveal (client_local_old_output lio)));
      fold (client_endpoint_local_continuation
        cc
        cfg
        frame
        (Ghost.reveal st)
        (CTypes.ClientAPI api)
        local_frame);
      rewrite
        (client_endpoint_local_continuation
          cc
          cfg
          frame
          (Ghost.reveal st)
          (CTypes.ClientAPI api)
          local_frame)
        as
        (client_endpoint_local_continuation
          cc
          cfg
          frame
          (Ghost.reveal st)
          ev
          local_frame);
      rewrite
        (client_local_io_continuation
          cc
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st)
          (CTypes.ClientAPI api)
          lio)
        as
        (client_local_io_continuation
          cc
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st)
          ev
          lio);
      lio
    }
  }
}

fn client_finish_local_action
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (ev:CTypes.client_local_event)
  (local_frame:CP.tls_client_local_frame)
  (result:CPI.process_result)
  (old_out:Ghost.erased B.bytes)
  (out_contents:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  (st1:Ghost.erased CS.connection_state)
  (wire_outputs:Ghost.erased (list CW.wire_message))
  (local_outputs:Ghost.erased (list CTypes.local_output))
requires
  client_endpoint_local_continuation cc cfg frame (Ghost.reveal st0) ev local_frame **
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
ensures client_endpoint_frame_ready cc cfg frame (Ghost.reveal st1)
{
  unfold (client_endpoint_local_continuation cc cfg frame (Ghost.reveal st0) ev local_frame);
  match ev {
    CTypes.ClientValidateCertificate payload -> {
      unfold (client_validate_local_continuation
        cfg
        frame
        (Ghost.reveal st0)
        (Ghost.reveal payload)
        local_frame);
      unfold (CP.client_local_frame_post
        (CTypes.ClientValidateCertificate payload)
        local_frame
        result
        (Ghost.reveal old_out)
        (Ghost.reveal out_contents)
        (Ghost.reveal st0)
        (Ghost.reveal st1)
        (Ghost.reveal wire_outputs)
        (Ghost.reveal local_outputs));
      with app_out. _;
      rewrite
        (pts_to
          local_frame.CP.tls_client_local_payload
          (Ghost.reveal payload))
        as
        (pts_to
          (V.vec_to_array frame.client_ep_auth_payload)
          (Ghost.reveal payload));
      V.to_vec_pts_to frame.client_ep_auth_payload;
      fold (client_endpoint_auth_payload_ready frame);
      fold (client_endpoint_auth_ready frame);
      rewrite
        (pts_to local_frame.CP.tls_client_local_app_out app_out)
        as
        (pts_to frame.client_ep_query.CQueries.client_query_local_app_out app_out);
      with app_out.
      fold (CQueries.client_local_persistent_resource frame.client_ep_query);
      fold (CQueries.client_next_local_action_frame_ready
        cc
        cfg
        frame.client_ep_query
        (Ghost.reveal st1));
      fold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st1))
    }
    CTypes.ClientAPI api -> {
      CQueries.finish_client_next_action_local
        cc
        cfg
        frame.client_ep_query
        (CTypes.ClientAPI api)
        local_frame
        result
        old_out
        out_contents
        st0
        st1
        wire_outputs
        local_outputs;
      fold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st1))
    }
  }
}

fn client_finish_local_io
  (cc:CP.canonical_client)
  (ch:TCP.channel)
  (frame:client_endpoint_frame)
  (lio:client_local_io)
  (ev:CTypes.client_local_event)
  (result:CPI.process_result)
  (received0:Ghost.erased B.bytes)
  (sent0:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  (received1:Ghost.erased B.bytes)
  (sent1:Ghost.erased B.bytes)
  (st1:Ghost.erased CS.connection_state)
  (out_contents:Ghost.erased B.bytes)
  (wire_outputs:Ghost.erased (list CW.wire_message))
  (local_outputs:Ghost.erased (list CTypes.local_output))
requires
  client_local_io_continuation cc ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) ev lio **
  pts_to (client_local_output lio) (Ghost.reveal out_contents) **
  pure (
    CPI.local_process_correct
      (CP.client_protocol_implementation.CPI.pi_system cc)
      ev
      (Ghost.reveal (client_local_old_output lio))
      (Ghost.reveal out_contents)
      (client_local_output_len lio)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs))
ensures client_endpoint_io_ready cc ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
{
  unfold (client_local_io_continuation cc ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) ev lio);
  with raw_bytes. _;
  CPI.lemma_local_process_sent_output_prefix
    (CP.client_protocol_implementation.CPI.pi_system cc)
    ev
    (Ghost.reveal (client_local_old_output lio))
    (Ghost.reveal out_contents)
    (client_local_output_len lio)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs);
  let nwritten = TCP.write ch (client_local_output lio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal lio.client_lio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel
      ch
      (Ghost.reveal lio.client_lio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal lio.client_lio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal lio.client_lio_raw_received) (Ghost.reveal sent1));
  rewrite
    (pts_to (client_local_output lio) (Ghost.reveal out_contents))
    as
    (pts_to (V.vec_to_array frame.client_ep_network_out) (Ghost.reveal out_contents));
  V.to_vec_pts_to frame.client_ep_network_out;
  fold (client_endpoint_io_ready cc ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
}

let client_pending_after_consumed (buffered_len consumed_len:SZ.t) : SZ.t =
  if SZ.lte consumed_len buffered_len
  then SZ.sub buffered_len consumed_len
  else 0sz

fn client_compact_buffer_suffix
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (consumed_len:SZ.t)
  requires pts_to raw 'raw_bytes **
           pure (B.length 'raw_bytes == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity)
  returns new_len:SZ.t
  ensures exists* raw_after.
           pts_to raw raw_after **
           pure (B.length raw_after == SZ.v raw_capacity /\
                 B.length (Ghost.reveal 'raw_bytes) == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 new_len == client_pending_after_consumed buffered_len consumed_len /\
                 SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
                 SZ.v new_len <= SZ.v buffered_len /\
                 Seq.equal
                   (Seq.slice raw_after 0 (SZ.v new_len))
                   (Seq.slice (Ghost.reveal 'raw_bytes)
                     (SZ.v consumed_len)
                     (SZ.v buffered_len)))
{
  let new_len = SZ.sub buffered_len consumed_len;
  assert (pure (new_len == client_pending_after_consumed buffered_len consumed_len));
  assert (pure (SZ.v new_len == SZ.v buffered_len - SZ.v consumed_len));
  assert (pure (SZ.v new_len <= SZ.v buffered_len));
  let no_shift = consumed_len = 0sz;
  if no_shift {
    assert (pure (new_len == buffered_len));
    assert (pure (Seq.equal
      (Seq.slice (Ghost.reveal 'raw_bytes) 0 (SZ.v new_len))
      (Seq.slice (Ghost.reveal 'raw_bytes)
        (SZ.v consumed_len)
        (SZ.v buffered_len))));
    new_len
  } else {
    let mut i = 0sz;
    while ((R.read i) `SZ.lt` new_len)
      invariant live i
      invariant exists* raw_loop.
        pts_to raw raw_loop **
        pure (B.length raw_loop == SZ.v raw_capacity /\
              SZ.v (R.read i) <= SZ.v new_len /\
              SZ.v new_len == SZ.v buffered_len - SZ.v consumed_len /\
              SZ.v new_len <= SZ.v buffered_len /\
              SZ.v consumed_len <= SZ.v buffered_len /\
              SZ.v buffered_len <= SZ.v raw_capacity /\
              (forall (k:nat). k < SZ.v (R.read i) ==>
                Seq.index raw_loop k ==
                Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)) /\
              (forall (k:nat). SZ.v (R.read i) <= k /\ k < SZ.v buffered_len ==>
                Seq.index raw_loop k ==
                Seq.index (Ghost.reveal 'raw_bytes) k))
    {
      let vi = R.read i;
      assert (pure (SZ.v vi < SZ.v new_len));
      assert (pure (SZ.v vi + SZ.v consumed_len < SZ.v buffered_len));
      assert (pure (SZ.v vi + SZ.v consumed_len < SZ.v raw_capacity));
      SZ.fits_lte (SZ.v vi + SZ.v consumed_len) (SZ.v raw_capacity);
      let src_idx = vi `SZ.add` consumed_len;
      assert (pure (SZ.v src_idx < SZ.v raw_capacity));
      with raw_before_read.
        assert (pts_to raw raw_before_read);
      assert (pure (B.length raw_before_read == SZ.v raw_capacity));
      let b = raw.(src_idx);
      assert (pure (b == Seq.index (Ghost.reveal 'raw_bytes)
        (SZ.v vi + SZ.v consumed_len)));
      assert (pure (SZ.v vi < SZ.v raw_capacity));
      raw.(vi) <- b;
      with raw_after_write.
        assert (pts_to raw raw_after_write);
      assert (pure (B.length raw_after_write == SZ.v raw_capacity));
      assert (pure (Seq.index raw_after_write (SZ.v vi) == b));
      assert (pure (forall (k:nat). k < SZ.v vi ==>
        Seq.index raw_after_write k == Seq.index raw_before_read k));
      assert (pure (forall (k:nat). SZ.v vi + 1 <= k /\ k < SZ.v buffered_len ==>
        Seq.index raw_after_write k == Seq.index raw_before_read k));
      assert (pure (forall (k:nat). k < SZ.v vi ==>
        Seq.index raw_after_write k ==
        Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)));
      assert (pure (forall (k:nat). SZ.v vi + 1 <= k /\ k < SZ.v buffered_len ==>
        Seq.index raw_after_write k ==
        Seq.index (Ghost.reveal 'raw_bytes) k));
      let next = vi `SZ.add` 1sz;
      R.write i next
    };
    with raw_final.
      assert (pts_to raw raw_final);
    assert (pure (SZ.v (R.read i) == SZ.v new_len));
    assert (pure (forall (k:nat). k < SZ.v new_len ==>
      Seq.index raw_final k ==
      Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)));
    assert (pure (Seq.length (Seq.slice raw_final 0 (SZ.v new_len)) == SZ.v new_len));
    Seq.lemma_len_slice
      (Ghost.reveal 'raw_bytes)
      (SZ.v consumed_len)
      (SZ.v buffered_len);
    assert (pure (Seq.length
      (Seq.slice (Ghost.reveal 'raw_bytes) (SZ.v consumed_len) (SZ.v buffered_len))
      == SZ.v new_len));
    assert (pure (forall (k:nat). k < SZ.v new_len ==>
      Seq.index (Seq.slice raw_final 0 (SZ.v new_len)) k ==
      Seq.index raw_final k));
    assert (pure (forall (k:nat). k < SZ.v new_len ==>
      Seq.index
        (Seq.slice (Ghost.reveal 'raw_bytes) (SZ.v consumed_len) (SZ.v buffered_len))
        k ==
      Seq.index (Ghost.reveal 'raw_bytes) (SZ.v consumed_len + k)));
    assert (pure (forall (k:nat). k < SZ.v new_len ==>
      Seq.index (Seq.slice raw_final 0 (SZ.v new_len)) k ==
      Seq.index
        (Seq.slice (Ghost.reveal 'raw_bytes) (SZ.v consumed_len) (SZ.v buffered_len))
        k));
    Seq.lemma_eq_intro
      (Seq.slice raw_final 0 (SZ.v new_len))
      (Seq.slice (Ghost.reveal 'raw_bytes) (SZ.v consumed_len) (SZ.v buffered_len));
    new_len
  }
}

fn client_compact_buffered_input
  (raw:V.vec U8.t)
  (raw_capacity:SZ.t)
  (buffered_len_ref:Box.box SZ.t)
  (buffered_len:SZ.t)
  (consumed_len:SZ.t)
  requires V.pts_to raw #1.0R 'raw_bytes **
           Box.pts_to buffered_len_ref 'old_buffered_len **
           pure (B.length 'raw_bytes == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity)
  returns new_len:SZ.t
  ensures exists* raw_after.
           V.pts_to raw #1.0R raw_after **
           Box.pts_to buffered_len_ref new_len **
           pure (B.length raw_after == SZ.v raw_capacity /\
                 new_len == client_pending_after_consumed buffered_len consumed_len /\
                 SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
                 SZ.v new_len <= SZ.v buffered_len)
{
  V.to_array_pts_to raw;
  let new_len =
    client_compact_buffer_suffix
      (V.vec_to_array raw)
      raw_capacity
      buffered_len
      consumed_len;
  with raw_after.
    assert (pts_to (V.vec_to_array raw) raw_after);
  assert (pure (B.length raw_after == SZ.v raw_capacity));
  assert (pure (SZ.v new_len <= B.length raw_after));
  assert (pure (SZ.v buffered_len <= B.length (Ghost.reveal 'raw_bytes)));
  Box.(buffered_len_ref := new_len);
  V.to_vec_pts_to raw;
  new_len
}

fn client_compact_endpoint_input
  (cc:CP.canonical_client)
  (ch:TCP.channel)
  (frame:client_endpoint_frame)
  (buffered_len_ref:Box.box SZ.t)
  (buffered_len:SZ.t)
  (consumed_len:SZ.t)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
  requires client_endpoint_io_ready
             cc
             ch
             frame
             (Ghost.reveal received)
             (Ghost.reveal sent)
             (Ghost.reveal st) **
           Box.pts_to buffered_len_ref 'old_buffered_len **
           pure (SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v frame.client_ep_raw_len)
  returns new_len:SZ.t
  ensures client_endpoint_io_ready
            cc
            ch
            frame
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st) **
          Box.pts_to buffered_len_ref new_len **
          pure (new_len == client_pending_after_consumed buffered_len consumed_len /\
                SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
                SZ.v new_len <= SZ.v frame.client_ep_raw_len)
{
  unfold (client_endpoint_io_ready cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw_received raw_bytes network_out_bytes. _;
  let new_len =
    client_compact_buffered_input
      frame.client_ep_raw
      frame.client_ep_raw_len
      buffered_len_ref
      buffered_len
      consumed_len;
  with raw_after.
    assert (V.pts_to frame.client_ep_raw #1.0R raw_after **
            Box.pts_to buffered_len_ref new_len);
  fold (client_endpoint_io_ready cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  assert (pure (SZ.v new_len <= SZ.v buffered_len));
  assert (pure (SZ.v buffered_len <= SZ.v frame.client_ep_raw_len));
  new_len
}

fn client_read_into_raw_suffix
  (ch:TCP.channel)
  (raw:V.vec U8.t)
  (raw_capacity:SZ.t)
  (offset:SZ.t)
  requires TCP.is_channel ch 'received 'sent **
           V.pts_to raw #1.0R 'raw_bytes **
           pure (B.length 'raw_bytes == SZ.v raw_capacity /\
                 SZ.v offset <= SZ.v raw_capacity)
  returns read_len:SZ.t
  ensures exists* received_after raw_after.
            TCP.is_channel ch received_after (Ghost.reveal 'sent) **
            V.pts_to raw #1.0R raw_after **
            pure (B.length raw_after == SZ.v raw_capacity /\
                  SZ.v read_len <= SZ.v raw_capacity - SZ.v offset)
{
  let available = SZ.sub raw_capacity offset;
  assert (pure (SZ.v available == SZ.v raw_capacity - SZ.v offset));
  V.to_array_pts_to raw;
  let tmp = V.alloc 0uy available;
  V.to_array_pts_to tmp;
  let read_len = TCP.read ch (V.vec_to_array tmp) available;
  with tmp_after chunk.
    assert (TCP.is_channel ch (Seq.append (Ghost.reveal 'received) chunk) (Ghost.reveal 'sent) **
            pts_to (V.vec_to_array tmp) tmp_after);
  assert (pure (B.length tmp_after == SZ.v available));
  assert (pure (SZ.v read_len <= SZ.v available));
  assert (pure (SZ.v offset + SZ.v read_len <= SZ.v raw_capacity));
  SC.copy_array_slice_to_array
    (V.vec_to_array tmp)
    available
    0sz
    read_len
    (V.vec_to_array raw)
    raw_capacity
    offset;
  with raw_after.
    assert (pts_to (V.vec_to_array raw) raw_after);
  assert (pure (B.length raw_after == SZ.v raw_capacity));
  let received_after = Ghost.hide (Seq.append (Ghost.reveal 'received) chunk);
  rewrite
    (TCP.is_channel ch (Seq.append (Ghost.reveal 'received) chunk) (Ghost.reveal 'sent))
    as
    (TCP.is_channel ch (Ghost.reveal received_after) (Ghost.reveal 'sent));
  V.to_vec_pts_to tmp;
  V.free tmp;
  V.to_vec_pts_to raw;
  read_len
}

fn client_read_more_endpoint_input
  (cc:CP.canonical_client)
  (ch:TCP.channel)
  (frame:client_endpoint_frame)
  (offset:SZ.t)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
  requires client_endpoint_io_ready
             cc
             ch
             frame
             (Ghost.reveal received)
             (Ghost.reveal sent)
             (Ghost.reveal st) **
           pure (SZ.v offset <= SZ.v frame.client_ep_raw_len)
  returns read_len:SZ.t
  ensures client_endpoint_io_ready
            cc
            ch
            frame
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st) **
          pure (SZ.v read_len <= SZ.v frame.client_ep_raw_len - SZ.v offset)
{
  unfold (client_endpoint_io_ready cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw_received raw_bytes network_out_bytes. _;
  let read_len =
    client_read_into_raw_suffix
      ch
      frame.client_ep_raw
      frame.client_ep_raw_len
      offset;
  with raw_received_after raw_after.
    assert (TCP.is_channel ch raw_received_after (Ghost.reveal sent) **
            V.pts_to frame.client_ep_raw #1.0R raw_after);
  fold (client_endpoint_io_ready cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  read_len
}

let client_api_local_action_ready
  (_cc:CP.canonical_client)
  (ch:TCP.channel)
  (frame:client_endpoint_frame)
  (_received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  (ev:CTypes.client_local_event)
  (local_frame:CP.tls_client_local_frame)
  : slprop =
  exists* raw_received raw_bytes network_out_bytes.
    TCP.is_channel ch raw_received sent **
    V.pts_to frame.client_ep_raw #1.0R raw_bytes **
    V.pts_to frame.client_ep_network_out #1.0R network_out_bytes **
    CP.client_local_frame_pre
      ev
      local_frame
      st
      (V.vec_to_array frame.client_ep_network_out)
      frame.client_ep_network_out_len
      network_out_bytes **
    pure (
      B.length raw_bytes == SZ.v frame.client_ep_raw_len /\
      B.length network_out_bytes == SZ.v frame.client_ep_network_out_len)

fn client_run_api_local_action
  (cc:CP.canonical_client)
  (frame:client_endpoint_frame)
  (ch:TCP.channel)
  (ev:CTypes.client_local_event)
  (local_frame:CP.tls_client_local_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  client_api_local_action_ready
    cc
    ch
    frame
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)
    ev
    local_frame
returns result:CPI.process_result
ensures
  exists* (received1:Ghost.erased B.bytes)
          (sent1:Ghost.erased B.bytes)
          (st1:Ghost.erased CS.connection_state)
          (old_out:Ghost.erased B.bytes)
          (out_contents:Ghost.erased B.bytes)
          (wire_outputs:Ghost.erased (list CW.wire_message))
          (local_outputs:Ghost.erased (list CTypes.local_output)).
    CP.client_invariant
      cc
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    client_endpoint_io_ready
      cc
      ch
      frame
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    CP.client_local_frame_post
      ev
      local_frame
      result
      (Ghost.reveal old_out)
      (Ghost.reveal out_contents)
      (Ghost.reveal st)
      (Ghost.reveal st1)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs)
{
  unfold (client_api_local_action_ready
    cc
    ch
    frame
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)
    ev
    local_frame);
  with raw_received raw_bytes network_out_bytes. _;
  let rawe = Ghost.hide raw_received;
  let old_oute = Ghost.hide network_out_bytes;
  V.to_array_pts_to frame.client_ep_network_out;
  let lio = {
    client_lio_output = V.vec_to_array frame.client_ep_network_out;
    client_lio_output_len = frame.client_ep_network_out_len;
    client_lio_old_output = old_oute;
    client_lio_raw_received = rawe;
  };
  rewrite
    (TCP.is_channel ch raw_received (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal lio.client_lio_raw_received) (Ghost.reveal sent));
  fold (client_local_io_continuation
    cc
    ch
    frame
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)
    ev
    lio);
  rewrite
    (pts_to (V.vec_to_array frame.client_ep_network_out) network_out_bytes)
    as
    (pts_to (client_local_output lio) (Ghost.reveal (client_local_old_output lio)));
  let result =
    CP.client_process_local
      cc
      ev
      local_frame
      (client_local_output lio)
      (client_local_output_len lio)
      received
      sent
      st
      (client_local_old_output lio);
  with received1 sent1 st1 out_contents wire_outputs local_outputs.
  assert (
    CP.client_invariant
      cc
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    CP.client_local_frame_post
      ev
      local_frame
      result
      (Ghost.reveal (client_local_old_output lio))
      out_contents
      (Ghost.reveal st)
      (Ghost.reveal st1)
      wire_outputs
      local_outputs);
  let out_contentse = Ghost.hide out_contents;
  let wire_outputse = Ghost.hide wire_outputs;
  let local_outputse = Ghost.hide local_outputs;
  rewrite
    (CP.client_local_frame_post
      ev
      local_frame
      result
      (Ghost.reveal (client_local_old_output lio))
      out_contents
      (Ghost.reveal st)
      (Ghost.reveal st1)
      wire_outputs
      local_outputs)
    as
    (CP.client_local_frame_post
      ev
      local_frame
      result
      (Ghost.reveal (client_local_old_output lio))
      (Ghost.reveal out_contentse)
      (Ghost.reveal st)
      (Ghost.reveal st1)
      (Ghost.reveal wire_outputse)
      (Ghost.reveal local_outputse));
  client_finish_local_io
    cc
    ch
    frame
    lio
    ev
    result
    received
    sent
    st
    received1
    sent1
    st1
    out_contentse
    wire_outputse
    local_outputse;
  result
}

fn client_run_buffered_network_action
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (ch:TCP.channel)
  (network_frame:CP.tls_client_network_bridge_frame)
  (input_len:SZ.t)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  client_endpoint_action_frame
    cc
    cfg
    frame
    (Ghost.reveal st)
    (PE.EndpointNeedInput network_frame) **
  client_endpoint_io_ready
    cc
    ch
    frame
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  pure (SZ.v input_len <= SZ.v frame.client_ep_raw_len)
returns result:CPI.process_result
ensures
  exists* (received1:Ghost.erased B.bytes)
          (sent1:Ghost.erased B.bytes)
          (st1:Ghost.erased CS.connection_state).
    CP.client_invariant
      cc
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    client_endpoint_frame_ready
      cc
      cfg
      frame
      (Ghost.reveal st1) **
    client_endpoint_io_ready
      cc
      ch
      frame
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
{
  unfold (client_endpoint_io_ready cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw_received raw_bytes network_out_bytes. _;
  V.to_array_pts_to frame.client_ep_raw;
  V.to_array_pts_to frame.client_ep_network_out;
  let input_vec = V.alloc 0uy input_len;
  V.to_array_pts_to input_vec;
  SC.copy_array_slice_to_array
    (V.vec_to_array frame.client_ep_raw)
    frame.client_ep_raw_len
    0sz
    input_len
    (V.vec_to_array input_vec)
    input_len
    0sz;
  let inpute = Ghost.hide (
    Seq.append
      (CL.raw_slice (Seq.create (SZ.v input_len) 0uy) (SZ.v 0sz) (SZ.v 0sz))
      (Seq.append
        (CL.raw_slice raw_bytes (SZ.v 0sz) (SZ.v 0sz + SZ.v input_len))
        (CL.raw_slice
          (Seq.create (SZ.v input_len) 0uy)
          (SZ.v 0sz + SZ.v input_len)
          (SZ.v input_len))));
  assert (pure (B.length (Ghost.reveal inpute) == SZ.v input_len));
  let old_oute = Ghost.hide network_out_bytes;
  let raw_receivede = Ghost.hide raw_received;
  let nio = {
    client_nio_input = V.vec_to_array input_vec;
    client_nio_input_len = input_len;
    client_nio_output = V.vec_to_array frame.client_ep_network_out;
    client_nio_output_len = frame.client_ep_network_out_len;
    client_nio_input_contents = inpute;
    client_nio_old_output = old_oute;
    client_nio_raw_received = raw_receivede;
  };
  rewrite
    (TCP.is_channel ch raw_received (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal nio.client_nio_raw_received) (Ghost.reveal sent));
  unfold (client_endpoint_action_frame cc cfg frame (Ghost.reveal st) (PE.EndpointNeedInput network_frame));
  rewrite
    (pts_to
      (V.vec_to_array input_vec)
      (Seq.append
        (CL.raw_slice (Seq.create (SZ.v input_len) 0uy) (SZ.v 0sz) (SZ.v 0sz))
        (Seq.append
          (CL.raw_slice raw_bytes (SZ.v 0sz) (SZ.v 0sz + SZ.v input_len))
          (CL.raw_slice
            (Seq.create (SZ.v input_len) 0uy)
            (SZ.v 0sz + SZ.v input_len)
            (SZ.v input_len)))))
    as
    (pts_to (client_network_input nio) (Ghost.reveal (client_network_input_contents nio)));
  rewrite
    (pts_to (V.vec_to_array frame.client_ep_network_out) network_out_bytes)
    as
    (pts_to (client_network_output nio) (Ghost.reveal (client_network_old_output nio)));
  fold (CQ.network_buffers
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    (Ghost.reveal (client_network_input_contents nio))
    (Ghost.reveal (client_network_old_output nio)));
  CQueries.prepare_client_next_action_network
    cc
    cfg
    frame.client_ep_query
    network_frame
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    st
    (client_network_input_contents nio)
    (client_network_old_output nio);
  unfold (CQ.network_buffers
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    (Ghost.reveal (client_network_input_contents nio))
    (Ghost.reveal (client_network_old_output nio)));
  fold (PE.network_buffers
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    (Ghost.reveal (client_network_input_contents nio))
    (Ghost.reveal (client_network_old_output nio)));
  fold (client_endpoint_network_continuation cc cfg frame (Ghost.reveal st) network_frame);
  let result =
    CP.client_process_network
      cc
      network_frame
      (client_network_input nio)
      (client_network_input_len nio)
      (client_network_output nio)
      (client_network_output_len nio)
      received
      sent
      st
      (client_network_input_contents nio)
      (client_network_old_output nio);
  with received1 sent1 st1 out_contents consumed wire_outputs local_outputs.
  assert (
    CP.client_invariant
      cc
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    CP.client_network_bridge_frame_post
      network_frame
      result
      (Ghost.reveal (client_network_input_contents nio))
      (client_network_input_len nio)
      (Ghost.reveal (client_network_old_output nio))
      out_contents
      (Ghost.reveal st)
      (Ghost.reveal st1)
      consumed
      wire_outputs
      local_outputs);
  let out_contentse = Ghost.hide out_contents;
  let consumede = Ghost.hide consumed;
  let wire_outputse = Ghost.hide wire_outputs;
  let local_outputse = Ghost.hide local_outputs;
  rewrite
    (CP.client_network_bridge_frame_post
      network_frame
      result
      (Ghost.reveal (client_network_input_contents nio))
      (client_network_input_len nio)
      (Ghost.reveal (client_network_old_output nio))
      out_contents
      (Ghost.reveal st)
      (Ghost.reveal st1)
      consumed
      wire_outputs
      local_outputs)
    as
    (CP.client_network_bridge_frame_post
      network_frame
      result
      (Ghost.reveal (client_network_input_contents nio))
      (client_network_input_len nio)
      (Ghost.reveal (client_network_old_output nio))
      (Ghost.reveal out_contentse)
      (Ghost.reveal st)
      (Ghost.reveal st1)
      (Ghost.reveal consumede)
      (Ghost.reveal wire_outputse)
      (Ghost.reveal local_outputse));
  client_finish_network_action
    cc
    cfg
    frame
    network_frame
    result
    (client_network_input_contents nio)
    (client_network_input_len nio)
    (client_network_old_output nio)
    out_contentse
    st
    st1
    consumede
    wire_outputse
    local_outputse;
  rewrite
    (pts_to (client_network_output nio) out_contents)
    as
    (pts_to (client_network_output nio) (Ghost.reveal out_contentse));
  CPI.lemma_network_process_sent_output_prefix
    (CP.client_protocol_implementation.CPI.pi_system cc)
    (Ghost.reveal (client_network_input_contents nio))
    (client_network_input_len nio)
    (Ghost.reveal (client_network_old_output nio))
    (Ghost.reveal out_contentse)
    (client_network_output_len nio)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal consumede)
    (Ghost.reveal wire_outputse)
    (Ghost.reveal local_outputse);
  let nwritten = TCP.write ch (client_network_output nio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal nio.client_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contentse)
         then Seq.slice (Ghost.reveal out_contentse) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel
      ch
      (Ghost.reveal nio.client_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contentse)
         then Seq.slice (Ghost.reveal out_contentse) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  assert (pure (Seq.equal
    (Ghost.reveal sent1)
    (Seq.append
      (Ghost.reveal sent)
      (CPI.output_prefix (Ghost.reveal out_contentse) result.CPI.process_produced_len))));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal nio.client_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contentse)
         then Seq.slice (Ghost.reveal out_contentse) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal nio.client_nio_raw_received) (Ghost.reveal sent1));
  rewrite
    (pts_to (client_network_output nio) (Ghost.reveal out_contentse))
    as
    (pts_to (V.vec_to_array frame.client_ep_network_out) (Ghost.reveal out_contentse));
  rewrite
    (pts_to (client_network_input nio) (Ghost.reveal (client_network_input_contents nio)))
    as
    (pts_to (V.vec_to_array input_vec) (Ghost.reveal (client_network_input_contents nio)));
  V.to_vec_pts_to input_vec;
  V.free input_vec;
  V.to_vec_pts_to frame.client_ep_raw;
  V.to_vec_pts_to frame.client_ep_network_out;
  fold (client_endpoint_io_ready cc ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
  result
}

fn client_run_scheduled_local_action
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (ch:TCP.channel)
  (ev:CTypes.client_local_event)
  (local_frame:CP.tls_client_local_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  client_endpoint_action_frame
    cc
    cfg
    frame
    (Ghost.reveal st)
    (PE.EndpointLocal ev local_frame) **
  client_endpoint_io_ready
    cc
    ch
    frame
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)
returns result:CPI.process_result
ensures
  exists* (received1:Ghost.erased B.bytes)
          (sent1:Ghost.erased B.bytes)
          (st1:Ghost.erased CS.connection_state).
    CP.client_invariant
      cc
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    client_endpoint_frame_ready
      cc
      cfg
      frame
      (Ghost.reveal st1) **
    client_endpoint_io_ready
      cc
      ch
      frame
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
{
  let lio =
    client_prepare_local
      cc
      cfg
      frame
      ch
      ev
      local_frame
      received
      sent
      st;
  let result =
    CP.client_process_local
      cc
      ev
      local_frame
      (client_local_output lio)
      (client_local_output_len lio)
      received
      sent
      st
      (client_local_old_output lio);
  with received1 sent1 st1 out_contents wire_outputs local_outputs.
  assert (
    CP.client_invariant
      cc
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    CP.client_local_frame_post
      ev
      local_frame
      result
      (Ghost.reveal (client_local_old_output lio))
      out_contents
      (Ghost.reveal st)
      (Ghost.reveal st1)
      wire_outputs
      local_outputs);
  let out_contentse = Ghost.hide out_contents;
  let wire_outputse = Ghost.hide wire_outputs;
  let local_outputse = Ghost.hide local_outputs;
  rewrite
    (CP.client_local_frame_post
      ev
      local_frame
      result
      (Ghost.reveal (client_local_old_output lio))
      out_contents
      (Ghost.reveal st)
      (Ghost.reveal st1)
      wire_outputs
      local_outputs)
    as
    (CP.client_local_frame_post
      ev
      local_frame
      result
      (Ghost.reveal (client_local_old_output lio))
      (Ghost.reveal out_contentse)
      (Ghost.reveal st)
      (Ghost.reveal st1)
      (Ghost.reveal wire_outputse)
      (Ghost.reveal local_outputse));
  client_finish_local_action
    cc
    cfg
    frame
    ev
    local_frame
    result
    (client_local_old_output lio)
    out_contentse
    st
    st1
    wire_outputse
    local_outputse;
  client_finish_local_io
    cc
    ch
    frame
    lio
    ev
    result
    received
    sent
    st
    received1
    sent1
    st1
    out_contentse
    wire_outputse
    local_outputse;
  result
}

type client_endpoint_run_status =
  | ClientEndpointRunOk
  | ClientEndpointRunFailed
  | ClientEndpointRunFuelExhausted

noeq
type client_endpoint_run_result = {
  client_endpoint_run_status: client_endpoint_run_status;
  client_endpoint_run_app_len: SZ.t;
  client_endpoint_run_last_status: CPI.process_status;
}

fn client_decrement_endpoint_fuel
  (remaining:ref SZ.t)
  (fuel:SZ.t)
  requires R.pts_to remaining 'rem **
           pure (not (Ghost.reveal 'rem = 0sz) /\
                 SZ.v (Ghost.reveal 'rem) <= SZ.v fuel)
  ensures exists* rem1.
            R.pts_to remaining rem1 **
            pure (SZ.v rem1 <= SZ.v fuel)
{
  let rem_now = R.read remaining;
  assert (pure (not (rem_now = 0sz)));
  assert (pure (0 < SZ.v rem_now));
  let next = SZ.sub rem_now 1sz;
  assert (pure (SZ.v next < SZ.v rem_now));
  assert (pure (SZ.v next <= SZ.v fuel));
  remaining := next
}

fn client_update_refs_after_network_result
  (result:CPI.process_result)
  (stop_on_application_data:bool)
  (fail_need_more_without_input:bool)
  (running:ref bool)
  (failed:ref bool)
  (app_len:ref SZ.t)
  requires R.pts_to running 'running0 **
           R.pts_to failed 'failed0 **
           R.pts_to app_len 'app_len0
  ensures exists* running1 failed1 app_len1.
            R.pts_to running running1 **
            R.pts_to failed failed1 **
            R.pts_to app_len app_len1
{
  if (result.CPI.process_status = CPI.StepOk) {
    if not (result.CPI.process_app_len = 0sz) {
      app_len := result.CPI.process_app_len;
      if stop_on_application_data {
        running := false
      }
    }
  } else if (result.CPI.process_status = CPI.NeedMoreInput) {
    if fail_need_more_without_input {
      failed := true;
      running := false
    }
  } else {
    failed := true;
    running := false
  }
}

fn client_finish_network_result_iteration
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (ch:TCP.channel)
  (buffered_len_ref:Box.box SZ.t)
  (result:CPI.process_result)
  (total_len:SZ.t)
  (fail_need_more_without_input:bool)
  (stop_on_application_data:bool)
  (running:ref bool)
  (failed:ref bool)
  (app_len:ref SZ.t)
  (last_status:ref CPI.process_status)
  (remaining:ref SZ.t)
  (fuel:SZ.t)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
  requires CP.client_invariant
             cc
             (Ghost.reveal received)
             (Ghost.reveal sent)
             (Ghost.reveal st) **
           client_endpoint_frame_ready
             cc
             cfg
             frame
             (Ghost.reveal st) **
           client_endpoint_io_ready
             cc
             ch
             frame
             (Ghost.reveal received)
             (Ghost.reveal sent)
             (Ghost.reveal st) **
           Box.pts_to buffered_len_ref 'buffered_len **
           R.pts_to running 'running0 **
           R.pts_to failed 'failed0 **
           R.pts_to app_len 'app_len0 **
           R.pts_to last_status 'last_status0 **
           R.pts_to remaining 'rem **
           pure (SZ.v 'buffered_len <= SZ.v frame.client_ep_raw_len /\
                 SZ.v total_len <= SZ.v frame.client_ep_raw_len /\
                 not (Ghost.reveal 'rem = 0sz) /\
                 SZ.v (Ghost.reveal 'rem) <= SZ.v fuel)
  ensures exists* buffered_len1 running1 failed1 app_len1 last_status1 rem1.
            CP.client_invariant
              cc
              (Ghost.reveal received)
              (Ghost.reveal sent)
              (Ghost.reveal st) **
            client_endpoint_frame_ready
              cc
              cfg
              frame
              (Ghost.reveal st) **
            client_endpoint_io_ready
              cc
              ch
              frame
              (Ghost.reveal received)
              (Ghost.reveal sent)
              (Ghost.reveal st) **
            Box.pts_to buffered_len_ref buffered_len1 **
            R.pts_to running running1 **
            R.pts_to failed failed1 **
            R.pts_to app_len app_len1 **
            R.pts_to last_status last_status1 **
            R.pts_to remaining rem1 **
            pure (SZ.v buffered_len1 <= SZ.v frame.client_ep_raw_len /\
                  SZ.v rem1 <= SZ.v fuel)
{
  last_status := result.CPI.process_status;
  if SZ.lte result.CPI.process_consumed_len total_len {
    let _ =
      client_compact_endpoint_input
        cc
        ch
        frame
        buffered_len_ref
        total_len
        result.CPI.process_consumed_len
        received
        sent
        st;
    client_update_refs_after_network_result
      result
      stop_on_application_data
      fail_need_more_without_input
      running
      failed
      app_len;
    client_decrement_endpoint_fuel remaining fuel
  } else {
    failed := true;
    running := false;
    client_decrement_endpoint_fuel remaining fuel
  }
}

fn client_endpoint_control_tag
  (cc:CP.canonical_client)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
  requires CP.client_invariant
             cc
             (Ghost.reveal received)
             (Ghost.reveal sent)
             (Ghost.reveal st)
  returns tag:U8.t
  ensures CP.client_invariant
            cc
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st)
{
  unfold (CP.client_invariant cc (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  rewrite
    (C.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st))
    as
    (CR.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st));
  let snapshot = C.control_snapshot cc.CP.canonical_client_state;
  let tag = snapshot.CR.snapshot_control_tag;
  rewrite
    (CR.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st))
    as
    (C.connection_exactly cc.CP.canonical_client_state (Ghost.reveal st));
  fold (CP.client_invariant cc (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  tag
}

fn client_endpoint_run_workflow
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (ch:TCP.channel)
  (buffered_len_ref:Box.box SZ.t)
  (stop_on_application_data:bool)
  (stop_on_application_ready:bool)
  (stop_on_closed:bool)
  (fuel:SZ.t)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
  requires CP.client_invariant
             cc
             (Ghost.reveal received)
             (Ghost.reveal sent)
             (Ghost.reveal st) **
           client_endpoint_frame_ready
             cc
             cfg
             frame
             (Ghost.reveal st) **
           client_endpoint_io_ready
             cc
             ch
             frame
             (Ghost.reveal received)
             (Ghost.reveal sent)
             (Ghost.reveal st) **
           Box.pts_to buffered_len_ref 'buffered_len **
           pure (SZ.v 'buffered_len <= SZ.v frame.client_ep_raw_len)
  returns run_result:client_endpoint_run_result
  ensures exists* (received1:Ghost.erased B.bytes)
                  (sent1:Ghost.erased B.bytes)
                  (st1:Ghost.erased CS.connection_state)
                  (buffered_len1:SZ.t).
            CP.client_invariant
              cc
              (Ghost.reveal received1)
              (Ghost.reveal sent1)
              (Ghost.reveal st1) **
            client_endpoint_frame_ready
              cc
              cfg
              frame
              (Ghost.reveal st1) **
            client_endpoint_io_ready
              cc
              ch
              frame
              (Ghost.reveal received1)
              (Ghost.reveal sent1)
              (Ghost.reveal st1) **
            Box.pts_to buffered_len_ref buffered_len1 **
            pure (SZ.v buffered_len1 <= SZ.v frame.client_ep_raw_len)
{
  let mut remaining = fuel;
  let mut running = true;
  let mut failed = false;
  let mut app_len = 0sz;
  let mut last_status = CPI.StepOk;
  while (
    let keep = R.read running;
    let rem = R.read remaining;
    keep && not (rem = 0sz)
  )
    invariant live remaining
    invariant live running
    invariant live failed
    invariant live app_len
    invariant live last_status
    invariant exists* (received_loop:Ghost.erased B.bytes)
                      (sent_loop:Ghost.erased B.bytes)
                      (st_loop:Ghost.erased CS.connection_state)
                      (buffered_len_loop:SZ.t).
      CP.client_invariant
        cc
        (Ghost.reveal received_loop)
        (Ghost.reveal sent_loop)
        (Ghost.reveal st_loop) **
      client_endpoint_frame_ready
        cc
        cfg
        frame
        (Ghost.reveal st_loop) **
      client_endpoint_io_ready
        cc
        ch
        frame
        (Ghost.reveal received_loop)
        (Ghost.reveal sent_loop)
        (Ghost.reveal st_loop) **
      Box.pts_to buffered_len_ref buffered_len_loop **
      pure (SZ.v buffered_len_loop <= SZ.v frame.client_ep_raw_len /\
            SZ.v (R.read remaining) <= SZ.v fuel)
  {
    with received_loop sent_loop st_loop buffered_len_loop.
      assert (
        CP.client_invariant
          cc
          (Ghost.reveal received_loop)
          (Ghost.reveal sent_loop)
          (Ghost.reveal st_loop) **
        client_endpoint_frame_ready
          cc
          cfg
          frame
          (Ghost.reveal st_loop) **
        client_endpoint_io_ready
          cc
          ch
          frame
          (Ghost.reveal received_loop)
          (Ghost.reveal sent_loop)
          (Ghost.reveal st_loop) **
        Box.pts_to buffered_len_ref buffered_len_loop **
        pure (SZ.v buffered_len_loop <= SZ.v frame.client_ep_raw_len /\
              SZ.v (R.read remaining) <= SZ.v fuel));
    let tag = client_endpoint_control_tag cc received_loop sent_loop st_loop;
    let is_failed = tag = 5uy;
    let is_app_ready = tag = 2uy;
    let is_closed = tag = 4uy;
    if is_failed {
      failed := true;
      running := false
    } else if (stop_on_application_ready && is_app_ready) {
      running := false
    } else if (stop_on_closed && is_closed) {
      running := false
    } else {
      let action =
        client_endpoint_next_action
          cc
          cfg
          frame
          received_loop
          sent_loop
          st_loop;
      match action {
        PE.EndpointLocal ev local_frame -> {
          let result =
            client_run_scheduled_local_action
              cc
              cfg
              frame
              ch
              ev
              local_frame
              received_loop
              sent_loop
              st_loop;
          with received1 sent1 st1.
            assert (
              CP.client_invariant
                cc
                (Ghost.reveal received1)
                (Ghost.reveal sent1)
                (Ghost.reveal st1) **
              client_endpoint_frame_ready
                cc
                cfg
                frame
                (Ghost.reveal st1) **
              client_endpoint_io_ready
                cc
                ch
                frame
                (Ghost.reveal received1)
                (Ghost.reveal sent1)
                (Ghost.reveal st1));
          last_status := result.CPI.process_status;
          if not (result.CPI.process_status = CPI.StepOk) {
            failed := true;
            running := false
          };
          let rem_now = R.read remaining;
          assert (pure (not (rem_now = 0sz)));
          assert (pure (0 < SZ.v rem_now));
          let next = SZ.sub rem_now 1sz;
          assert (pure (SZ.v next < SZ.v rem_now));
          assert (pure (SZ.v next <= SZ.v fuel));
          remaining := next
        }
        PE.EndpointNeedInput network_frame -> {
          let buffered_len = Box.(!buffered_len_ref);
          if SZ.lte frame.client_ep_raw_len buffered_len {
            client_endpoint_cancel_action
              cc
              cfg
              frame
              st_loop
              (PE.EndpointNeedInput network_frame);
            failed := true;
            running := false
          } else {
            let read_len =
              if (buffered_len = 0sz) {
                client_read_more_endpoint_input
                  cc
                  ch
                  frame
                  buffered_len
                  received_loop
                  sent_loop
                  st_loop
              } else {
                0sz
              };
            assert (pure (SZ.v read_len <= SZ.v frame.client_ep_raw_len - SZ.v buffered_len));
            assert (pure (SZ.v buffered_len + SZ.v read_len <= SZ.v frame.client_ep_raw_len));
            SZ.fits_lte (SZ.v buffered_len + SZ.v read_len) (SZ.v frame.client_ep_raw_len);
            let total_len = buffered_len `SZ.add` read_len;
              let result =
                client_run_buffered_network_action
                  cc
                  cfg
                  frame
                  ch
                  network_frame
                  total_len
                  received_loop
                  sent_loop
                  st_loop;
              with received1 sent1 st1.
                assert (
                  CP.client_invariant
                    cc
                    (Ghost.reveal received1)
                    (Ghost.reveal sent1)
                    (Ghost.reveal st1) **
                  client_endpoint_frame_ready
                    cc
                    cfg
                    frame
                    (Ghost.reveal st1) **
                  client_endpoint_io_ready
                    cc
                    ch
                    frame
                    (Ghost.reveal received1)
                    (Ghost.reveal sent1)
                    (Ghost.reveal st1));
              let need_retry =
                result.CPI.process_status = CPI.NeedMoreInput &&
                read_len = 0sz &&
                SZ.lt total_len frame.client_ep_raw_len;
              if need_retry {
                let read_more =
                  client_read_more_endpoint_input
                    cc
                    ch
                    frame
                    total_len
                    received1
                    sent1
                    st1;
                assert (pure (SZ.v read_more <= SZ.v frame.client_ep_raw_len - SZ.v total_len));
                assert (pure (SZ.v total_len + SZ.v read_more <= SZ.v frame.client_ep_raw_len));
                SZ.fits_lte (SZ.v total_len + SZ.v read_more) (SZ.v frame.client_ep_raw_len);
                let retry_total_len = total_len `SZ.add` read_more;
                if (read_more = 0sz) {
                  failed := true;
                  running := false;
                  client_decrement_endpoint_fuel remaining fuel
                } else {
                  let retry_action =
                    client_endpoint_next_action
                      cc
                      cfg
                      frame
                      received1
                      sent1
                      st1;
                  match retry_action {
                    PE.EndpointNeedInput retry_network_frame -> {
                      let retry_result =
                        client_run_buffered_network_action
                          cc
                          cfg
                          frame
                          ch
                          retry_network_frame
                          retry_total_len
                          received1
                          sent1
                          st1;
                      with received2 sent2 st2.
                        assert (
                          CP.client_invariant
                            cc
                            (Ghost.reveal received2)
                            (Ghost.reveal sent2)
                            (Ghost.reveal st2) **
                          client_endpoint_frame_ready
                            cc
                            cfg
                            frame
                            (Ghost.reveal st2) **
                          client_endpoint_io_ready
                            cc
                            ch
                            frame
                            (Ghost.reveal received2)
                            (Ghost.reveal sent2)
                            (Ghost.reveal st2));
                      client_finish_network_result_iteration
                        cc
                        cfg
                        frame
                        ch
                        buffered_len_ref
                        retry_result
                        retry_total_len
                        false
                        stop_on_application_data
                        running
                        failed
                        app_len
                        last_status
                        remaining
                        fuel
                        received2
                        sent2
                        st2
                    }
                    PE.EndpointLocal retry_ev retry_local_frame -> {
                      client_endpoint_cancel_action
                        cc
                        cfg
                        frame
                        st1
                        (PE.EndpointLocal retry_ev retry_local_frame);
                      failed := true;
                      running := false;
                      client_decrement_endpoint_fuel remaining fuel
                    }
                    PE.EndpointDone -> {
                      client_endpoint_cancel_action
                        cc
                        cfg
                        frame
                        st1
                        PE.EndpointDone;
                      failed := true;
                      running := false;
                      client_decrement_endpoint_fuel remaining fuel
                    }
                    PE.EndpointFailed -> {
                      client_endpoint_cancel_action
                        cc
                        cfg
                        frame
                        st1
                        PE.EndpointFailed;
                      failed := true;
                      running := false;
                      client_decrement_endpoint_fuel remaining fuel
                    }
                  }
                }
              } else {
                let fail_need_more_without_input = read_len = 0sz;
                client_finish_network_result_iteration
                  cc
                  cfg
                  frame
                  ch
                  buffered_len_ref
                  result
                  total_len
                  fail_need_more_without_input
                  stop_on_application_data
                  running
                  failed
                  app_len
                  last_status
                  remaining
                  fuel
                  received1
                  sent1
                  st1
              }
          }
        }
        PE.EndpointDone -> {
          client_endpoint_cancel_action
            cc
            cfg
            frame
            st_loop
            PE.EndpointDone;
          running := false
        }
        PE.EndpointFailed -> {
          client_endpoint_cancel_action
            cc
            cfg
            frame
            st_loop
            PE.EndpointFailed;
          failed := true;
          running := false
        }
      }
    }
  };
  let still_running = R.read running;
  let did_fail = R.read failed;
  let produced = R.read app_len;
  let last = R.read last_status;
  if still_running {
    {
      client_endpoint_run_status = ClientEndpointRunFuelExhausted;
      client_endpoint_run_app_len = produced;
      client_endpoint_run_last_status = last;
    }
  } else if did_fail {
    {
      client_endpoint_run_status = ClientEndpointRunFailed;
      client_endpoint_run_app_len = produced;
      client_endpoint_run_last_status = last;
    }
  } else {
    {
      client_endpoint_run_status = ClientEndpointRunOk;
      client_endpoint_run_app_len = produced;
      client_endpoint_run_last_status = last;
    }
  }
}

let client_protocol_endpoint
  : PE.protocol_endpoint
      CP.canonical_client
      CS.connection_state
      CW.wire_message
      CTypes.client_local_event
      CTypes.local_output
      CP.client_protocol_implementation
  =
  {
    PE.pe_config = CQueries.client_next_local_action_config;
    PE.pe_frame = client_endpoint_frame;
    PE.pe_frame_ready = client_endpoint_frame_ready;
    PE.pe_io_ready = client_endpoint_io_ready;
    PE.pe_action_frame = client_endpoint_action_frame;
    PE.pe_network_continuation = client_endpoint_network_continuation;
    PE.pe_local_continuation = client_endpoint_local_continuation;
    PE.pe_next_action = client_endpoint_next_action;
    PE.pe_cancel_action = client_endpoint_cancel_action;
    PE.pe_finish_network_action = client_finish_network_action;
    PE.pe_finish_local_action = client_finish_local_action;
    PE.pe_network_io = client_network_io;
    PE.pe_network_io_continuation = client_network_io_continuation;
    PE.pe_network_input = client_network_input;
    PE.pe_network_input_len = client_network_input_len;
    PE.pe_network_output = client_network_output;
    PE.pe_network_output_len = client_network_output_len;
    PE.pe_network_input_contents = client_network_input_contents;
    PE.pe_network_old_output = client_network_old_output;
    PE.pe_prepare_network = client_prepare_network;
    PE.pe_finish_network_io = client_finish_network_io;
    PE.pe_local_io = client_local_io;
    PE.pe_local_io_continuation = client_local_io_continuation;
    PE.pe_local_output = client_local_output;
    PE.pe_local_output_len = client_local_output_len;
    PE.pe_local_old_output = client_local_old_output;
    PE.pe_prepare_local = client_prepare_local;
    PE.pe_finish_local_io = client_finish_local_io;
  }
