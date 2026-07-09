module TLS13.Impl.Server.Endpoint

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CM = TLS13.Impl.ConnectionState.Model
module Crypto = TLS13.Crypto
module CryptoSpec = TLS13.Crypto.Spec
module CPI = Common.ProtocolImplementation
module CQ = TLS13.Impl.ConnectionStateQuery
module CR = TLS13.Impl.ConnectionState.Repr
module ConnQ = TLS13.Impl.ConnectionState.Queries
module CS = TLS13.Spec.ConnectionState
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Impl.CanonicalWire
module IM = TLS13.Impl.Messages
module Mat = TLS13.Impl.Server.Material
module M = TLS13.Messages
module PE = Common.ProtocolEndpoint
module Box = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module SC = TLS13.Impl.Serializer.Common
module Seq = FStar.Seq
module S = TLS13.Impl.Server
module SQueries = TLS13.Impl.Server.CanonicalQueries
module SP = TLS13.Impl.Server.CanonicalProtocol
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module T = TLS13.Types
module TCP = Common.TCP
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec

let server_endpoint_private_bytes_of_material
  (material:B.bytes)
  : GTot B.bytes =
  CL.raw_slice material 32 64

let server_endpoint_material_bytes_match_state
  (material:B.bytes)
  (st:CS.connection_state)
  : GTot prop =
  match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
  | Some selection ->
    selection.CS.server_selected_cipher_suite ==
      T.TLS_CHACHA20_POLY1305_SHA256 /\
    selection.CS.server_selected_group == T.X25519 /\
    Seq.equal
      selection.CS.server_random
      (CL.raw_slice material 0 32) /\
    Some? selection.CS.server_key_share_private /\
    Seq.equal
      (Some?.v selection.CS.server_key_share_private)
      (server_endpoint_private_bytes_of_material material) /\
    selection.CS.server_key_share_public ==
      CryptoSpec.x25519_public_from_private
        (server_endpoint_private_bytes_of_material material)
  | None ->
    True

noeq
type server_endpoint_frame = {
  server_ep_query: SQueries.server_next_local_action_frame;
  server_ep_raw_len: SZ.t;
  server_ep_raw: V.vec U8.t;
  server_ep_network_out_len: SZ.t;
  server_ep_network_out: V.vec U8.t;
  server_ep_certificate_chain_len: SZ.t;
  server_ep_certificate_chain_len_proof:
    certificate_chain:Ghost.erased B.bytes ->
      Ghost.erased
        (SZ.v server_ep_certificate_chain_len ==
         B.length (Ghost.reveal certificate_chain));
  server_ep_certificate_chain_len_bound:
    Ghost.erased
      (SZ.v server_ep_certificate_chain_len <=
       Bounds.max_server_certificate_chain_len);
  server_ep_material_len: SZ.t;
  server_ep_material: V.vec U8.t;
  server_ep_material_spec: Ghost.erased (b:B.bytes{B.length b == 64});
  server_ep_private_len: SZ.t;
  server_ep_private: V.vec U8.t;
  server_ep_material_deferred_ready:
    st:Ghost.erased CS.connection_state ->
    action:SQueries.server_deferred_action ->
      Ghost.erased
        (SQueries.server_deferred_action_ready (Ghost.reveal st) action ==>
         server_endpoint_material_bytes_match_state
           (Ghost.reveal server_ep_material_spec)
           (Ghost.reveal st));
}

let server_endpoint_material_bytes
  (frame:server_endpoint_frame)
  : GTot B.bytes =
  Ghost.reveal frame.server_ep_material_spec

let server_endpoint_private_bytes
  (frame:server_endpoint_frame)
  : GTot B.bytes =
  server_endpoint_private_bytes_of_material
    (server_endpoint_material_bytes frame)

let server_endpoint_material_matches_state
  (frame:server_endpoint_frame)
  (st:CS.connection_state)
  : GTot prop =
  server_endpoint_material_bytes_match_state
    (server_endpoint_material_bytes frame)
    st

let server_endpoint_payloads_ready
  (frame:server_endpoint_frame)
  : slprop =
  exists* material private_key.
    V.pts_to frame.server_ep_material #1.0R material **
    V.pts_to frame.server_ep_private #1.0R private_key **
    pure (
      B.length material == SZ.v frame.server_ep_material_len /\
      SZ.v frame.server_ep_material_len == 64 /\
      B.length private_key == SZ.v frame.server_ep_private_len /\
      SZ.v frame.server_ep_private_len == 32 /\
      Seq.equal material (server_endpoint_material_bytes frame) /\
      Seq.equal private_key (server_endpoint_private_bytes frame))

let server_endpoint_material_local_frame
  (frame:server_endpoint_frame)
  (old:Ghost.erased B.bytes)
  : SP.tls_server_local_bridge_frame =
  let base = {
    SP.tls_server_local_payload = V.vec_to_array frame.server_ep_material;
    SP.tls_server_local_payload_len = frame.server_ep_material_len;
    SP.tls_server_local_app_out =
      frame.server_ep_query.SQueries.server_query_local_app_out;
    SP.tls_server_local_app_out_len =
      frame.server_ep_query.SQueries.server_query_local_app_out_len;
    SP.tls_server_local_old_app_out = old;
  } in
  {
    SP.tls_server_local_bridge_base = base;
  }

let server_endpoint_private_local_frame
  (frame:server_endpoint_frame)
  (old:Ghost.erased B.bytes)
  : SP.tls_server_local_bridge_frame =
  let base = {
    SP.tls_server_local_payload = V.vec_to_array frame.server_ep_private;
    SP.tls_server_local_payload_len = frame.server_ep_private_len;
    SP.tls_server_local_app_out =
      frame.server_ep_query.SQueries.server_query_local_app_out;
    SP.tls_server_local_app_out_len =
      frame.server_ep_query.SQueries.server_query_local_app_out_len;
    SP.tls_server_local_old_app_out = old;
  } in
  {
    SP.tls_server_local_bridge_base = base;
  }

let server_endpoint_payload_remainder_ready
  (frame:server_endpoint_frame)
  (kind:ST.local_event_kind)
  : slprop =
  match kind with
  | ST.LocalSelectServerParameters
  | ST.LocalSendServerHello ->
    exists* private_key.
      V.pts_to frame.server_ep_private #1.0R private_key **
      pure (
        B.length private_key == SZ.v frame.server_ep_private_len /\
        SZ.v frame.server_ep_private_len == 32 /\
        SZ.v frame.server_ep_material_len == 64 /\
        Seq.equal private_key (server_endpoint_private_bytes frame))
  | ST.LocalDeriveSharedSecret ->
    exists* material.
      V.pts_to frame.server_ep_material #1.0R material **
      pure (
        B.length material == SZ.v frame.server_ep_material_len /\
        SZ.v frame.server_ep_material_len == 64 /\
        SZ.v frame.server_ep_private_len == 32 /\
        Seq.equal material (server_endpoint_material_bytes frame))
  | _ ->
    server_endpoint_payloads_ready frame

let server_endpoint_payload_frame_matches
  (frame:server_endpoint_frame)
  (kind:ST.local_event_kind)
  (local_frame:SP.tls_server_local_bridge_frame)
  : prop =
  match kind with
  | ST.LocalSelectServerParameters
  | ST.LocalSendServerHello ->
    local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload ==
      V.vec_to_array frame.server_ep_material /\
    local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload_len ==
      frame.server_ep_material_len /\
    local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out ==
      frame.server_ep_query.SQueries.server_query_local_app_out /\
    local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out_len ==
      frame.server_ep_query.SQueries.server_query_local_app_out_len
  | ST.LocalDeriveSharedSecret ->
    local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload ==
      V.vec_to_array frame.server_ep_private /\
    local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload_len ==
      frame.server_ep_private_len /\
    local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out ==
      frame.server_ep_query.SQueries.server_query_local_app_out /\
    local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out_len ==
      frame.server_ep_query.SQueries.server_query_local_app_out_len
  | _ ->
    False

let server_endpoint_payload_bytes_match
  (frame:server_endpoint_frame)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  : GTot prop =
  match kind with
  | ST.LocalSelectServerParameters
  | ST.LocalSendServerHello ->
    Seq.equal payload (server_endpoint_material_bytes frame)
  | ST.LocalDeriveSharedSecret ->
    Seq.equal payload (server_endpoint_private_bytes frame)
  | _ ->
    True

let server_endpoint_payload_local_action_frame
  (frame:server_endpoint_frame)
  (st:CS.connection_state)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (local_frame:SP.tls_server_local_bridge_frame)
  : slprop =
  SQueries.server_network_persistent_resource frame.server_ep_query **
  server_endpoint_payload_remainder_ready frame kind **
  pts_to
    local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
    payload **
  pts_to frame.server_ep_query.SQueries.server_query_local_payload B.empty **
  pts_to
    local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
    (Ghost.reveal
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out) **
  pure (
    B.length payload ==
      SZ.v local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload_len /\
    B.length
      (Ghost.reveal
        local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out) ==
      SZ.v local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out_len /\
    SZ.v frame.server_ep_query.SQueries.server_query_local_payload_len == 0 /\
    server_endpoint_payload_frame_matches frame kind local_frame /\
    server_endpoint_payload_bytes_match frame kind payload /\
    server_endpoint_material_matches_state frame st /\
    ST.server_local_event_input_ready st kind payload)

let server_endpoint_payload_local_continuation
  (frame:server_endpoint_frame)
  (st:CS.connection_state)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (local_frame:SP.tls_server_local_bridge_frame)
  : slprop =
  SQueries.server_network_persistent_resource frame.server_ep_query **
  server_endpoint_payload_remainder_ready frame kind **
  pts_to frame.server_ep_query.SQueries.server_query_local_payload B.empty **
  pure (
    B.length payload ==
      SZ.v local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload_len /\
    SZ.v frame.server_ep_query.SQueries.server_query_local_payload_len == 0 /\
    server_endpoint_payload_frame_matches frame kind local_frame /\
    server_endpoint_payload_bytes_match frame kind payload /\
    server_endpoint_material_matches_state frame st /\
    ST.server_local_event_input_ready st kind payload)

let server_endpoint_frame_ready
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
  (st:CS.connection_state)
  : slprop =
  SQueries.server_next_local_action_frame_ready
    srv
    cfg
    frame.server_ep_query
    st **
  server_endpoint_payloads_ready frame

let server_endpoint_io_ready
  (_srv:SP.canonical_server)
  (ch:TCP.channel)
  (frame:server_endpoint_frame)
  (_received:B.bytes)
  (sent:B.bytes)
  (_st:CS.connection_state)
  : slprop =
  exists* raw_received raw_bytes network_out_bytes.
    TCP.is_channel ch raw_received sent **
    V.pts_to frame.server_ep_raw #1.0R raw_bytes **
    V.pts_to frame.server_ep_network_out #1.0R network_out_bytes **
    pure (
      B.length raw_bytes == SZ.v frame.server_ep_raw_len /\
      B.length network_out_bytes == SZ.v frame.server_ep_network_out_len)

let server_endpoint_action_frame
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
  (st:CS.connection_state)
  (action:PE.endpoint_action
    SP.tls_server_network_bridge_frame
    CTypes.server_local_event
    SP.tls_server_local_bridge_frame)
  : slprop =
  match action with
  | PE.EndpointNeedInput network_frame ->
    SQueries.server_next_local_action_frame_post
      srv
      cfg
      frame.server_ep_query
      st
      (CQ.NextNeedInput network_frame) **
    server_endpoint_payloads_ready frame
  | PE.EndpointLocal ev local_frame ->
    (match ev with
     | CTypes.ServerPayload kind payload ->
       server_endpoint_payload_local_action_frame
         frame
         st
         kind
         (Ghost.reveal payload)
         local_frame
     | CTypes.ServerAPI _ ->
       SQueries.server_next_local_action_frame_post
         srv
         cfg
         frame.server_ep_query
         st
         (CQ.NextLocal ev local_frame) **
       server_endpoint_payloads_ready frame)
  | PE.EndpointDone
  | PE.EndpointFailed ->
    server_endpoint_frame_ready srv cfg frame st

let server_endpoint_network_continuation
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
  (st:CS.connection_state)
  (network_frame:SP.tls_server_network_bridge_frame)
  : slprop =
  SQueries.server_next_local_action_network_continuation
    srv
    cfg
    frame.server_ep_query
    st
    network_frame **
  server_endpoint_payloads_ready frame

let server_endpoint_local_continuation
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
  (st:CS.connection_state)
  (ev:CTypes.server_local_event)
  (local_frame:SP.tls_server_local_bridge_frame)
  : slprop =
  match ev with
  | CTypes.ServerPayload kind payload ->
    server_endpoint_payload_local_continuation
      frame
      st
      kind
      (Ghost.reveal payload)
      local_frame
  | CTypes.ServerAPI _ ->
    SQueries.server_next_local_action_local_continuation
      srv
      cfg
      frame.server_ep_query
      st
      ev
      local_frame **
    server_endpoint_payloads_ready frame

fn server_endpoint_next_action
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  SP.server_invariant srv (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) **
  server_endpoint_frame_ready srv cfg frame (Ghost.reveal st)
returns action:PE.endpoint_action
  SP.tls_server_network_bridge_frame
  CTypes.server_local_event
  SP.tls_server_local_bridge_frame
ensures
  SP.server_invariant srv (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) **
  server_endpoint_action_frame srv cfg frame (Ghost.reveal st) action
{
  unfold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st));
  let cq_action =
    SQueries.run_server_next_local_action
      srv
      cfg
      frame.server_ep_query
      received
      sent
      st;
  match cq_action {
    CQ.NextNeedInput network_frame -> {
      fold (server_endpoint_action_frame
        srv
        cfg
        frame
        (Ghost.reveal st)
        (PE.EndpointNeedInput network_frame));
      PE.EndpointNeedInput network_frame
    }
    CQ.NextLocal ev local_frame -> {
      unfold (SQueries.server_next_local_action_frame_post
        srv
        cfg
        frame.server_ep_query
        (Ghost.reveal st)
        (CQ.NextLocal ev local_frame));
      match ev {
        CTypes.ServerAPI api -> {
          fold (SQueries.server_next_local_action_frame_post
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st)
            (CQ.NextLocal (CTypes.ServerAPI api) local_frame));
          fold (server_endpoint_action_frame
            srv
            cfg
            frame
            (Ghost.reveal st)
            (PE.EndpointLocal (CTypes.ServerAPI api) local_frame));
          PE.EndpointLocal (CTypes.ServerAPI api) local_frame
        }
        CTypes.ServerPayload _ _ -> {
          assert (pure False);
          unreachable ()
        }
      }
    }
    CQ.NextDeferredLocal ext -> {
      match ext {
        SQueries.ServerDeferredSelectServerParameters -> {
          unfold (SQueries.server_next_local_action_frame_post
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st)
            (CQ.NextDeferredLocal ext));
          unfold (SQueries.server_next_local_action_frame_ready
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st));
          unfold (SQueries.server_network_persistent_resource frame.server_ep_query);
          with network_current. _;
          unfold (SQueries.server_local_persistent_resource frame.server_ep_query);
          with local_current. _;
          unfold (server_endpoint_payloads_ready frame);
          with material private_key. _;
          assert (pure (B.length material == 64));
          assert (pure (CL.raw_slice material 0 32 == Seq.slice material 0 32));
          Seq.lemma_len_slice material 0 32;
          assert (pure (B.length (CL.raw_slice material 0 32) == 32));
          assert (pure (CL.raw_slice material 32 64 == Seq.slice material 32 64));
          Seq.lemma_len_slice material 32 64;
          assert (pure (B.length (CL.raw_slice material 32 64) == 32));
          let server_random : Ghost.erased (b:B.bytes{B.length b == 32}) =
            Ghost.hide (CL.raw_slice material 0 32);
          let server_private_key : Ghost.erased (b:B.bytes{B.length b == 32}) =
            Ghost.hide (CL.raw_slice material 32 64);
          unfold (SP.server_invariant
            srv
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st));
          with certificate_chain credential_identity. _;
          (Ghost.reveal srv.SP.canonical_server_supported_profile)
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st)
            certificate_chain
            credential_identity;
          assert (pure (SP.server_supported_profile_selection
            (Ghost.reveal st)
            credential_identity));
          assert (pure (SQueries.server_deferred_action_ready
            (Ghost.reveal st)
            SQueries.ServerDeferredSelectServerParameters));
          assert (pure (Some?
            (Ghost.reveal st).CS.cs_model.CS.model_config.CS.config_server));
          assert (pure (Some?
            (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_client_hello));
          assert (pure (match
              (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_client_hello,
              (Ghost.reveal st).CS.cs_model.CS.model_config.CS.config_server with
            | Some ch, Some server_cfg ->
              CS.cipher_suite_offered
                server_cfg.CS.server_supported_cipher_suites
                T.TLS_CHACHA20_POLY1305_SHA256 /\
              CS.named_group_offered
                server_cfg.CS.server_supported_groups
                T.X25519 /\
              CS.signature_scheme_offered
                server_cfg.CS.server_allowed_signature_schemes
                T.RsaPssRsaeSha256 /\
              CS.sni_policy_accepts
                server_cfg.CS.server_sni_policy
                ch.M.server_name
            | _, _ -> True));
          rewrite
            (S.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st))
            as
            (CR.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st));
          let ready =
            ConnQ.can_select_supported_server_parameters_runtime
              srv.SP.canonical_server_state
              #server_random
              #server_private_key;
          rewrite
            (CR.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st))
            as
            (S.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st));
          if ready {
            assert (pure (ready));
            assert (pure ((Ghost.reveal st).CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived));
            assert (pure ((Ghost.reveal st).CS.cs_model.CS.model_config.CS.config_role ==
              CS.ServerEndpoint));
            assert (pure (CR.server_selection_absent
              (Ghost.reveal st).CS.cs_model.CS.model_handshake));
            assert (pure (Some?
              (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_client_hello));
            assert (pure (Some?
              (Ghost.reveal st).CS.cs_model.CS.model_config.CS.config_server));
            Seq.lemma_eq_elim
              (Ghost.reveal server_random)
              (CL.raw_slice material 0 32);
            Seq.lemma_eq_elim
              (Ghost.reveal server_private_key)
              (CL.raw_slice material 32 64);
            assert (pure (ST.server_local_event_input_ready
              (Ghost.reveal st)
              ST.LocalSelectServerParameters
              material));
            fold (SP.server_invariant
              srv
              (Ghost.reveal received)
              (Ghost.reveal sent)
              (Ghost.reveal st));
            let old_local = Ghost.hide local_current;
            let local_frame =
              server_endpoint_material_local_frame frame old_local;
            V.to_array_pts_to frame.server_ep_material;
            rewrite
              (pts_to (V.vec_to_array frame.server_ep_material) material)
              as
              (pts_to
                local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
                material);
            rewrite
              (pts_to frame.server_ep_query.SQueries.server_query_local_app_out (Ghost.reveal local_current))
              as
              (pts_to
                local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
                (Ghost.reveal
                  local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out));
            with network_current.
            fold (SQueries.server_network_persistent_resource frame.server_ep_query);
            with private_key.
            fold (server_endpoint_payload_remainder_ready
              frame
              ST.LocalSelectServerParameters);
            fold (server_endpoint_payload_local_action_frame
              frame
              (Ghost.reveal st)
              ST.LocalSelectServerParameters
              material
              local_frame);
            fold (server_endpoint_action_frame
              srv
              cfg
              frame
              (Ghost.reveal st)
              (PE.EndpointLocal
                (CTypes.ServerPayload
                  ST.LocalSelectServerParameters
                  (Ghost.hide material))
                local_frame));
            PE.EndpointLocal
              (CTypes.ServerPayload
                ST.LocalSelectServerParameters
                (Ghost.hide material))
              local_frame
          } else {
            fold (SP.server_invariant
              srv
              (Ghost.reveal received)
              (Ghost.reveal sent)
              (Ghost.reveal st));
            with material private_key.
            fold (server_endpoint_payloads_ready frame);
            with network_current.
            fold (SQueries.server_network_persistent_resource frame.server_ep_query);
            with local_current.
            fold (SQueries.server_local_persistent_resource frame.server_ep_query);
            fold (SQueries.server_next_local_action_frame_ready
              srv
              cfg
              frame.server_ep_query
              (Ghost.reveal st));
            fold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st));
            fold (server_endpoint_action_frame
              srv
              cfg
              frame
              (Ghost.reveal st)
              PE.EndpointFailed);
            PE.EndpointFailed
          }
        }
        SQueries.ServerDeferredDeriveSharedSecret -> {
          unfold (SQueries.server_next_local_action_frame_post
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st)
            (CQ.NextDeferredLocal ext));
          unfold (SQueries.server_next_local_action_frame_ready
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st));
          unfold (SQueries.server_network_persistent_resource frame.server_ep_query);
          with network_current. _;
          unfold (SQueries.server_local_persistent_resource frame.server_ep_query);
          with local_current. _;
          unfold (server_endpoint_payloads_ready frame);
          with material private_key. _;
          assert (pure (SQueries.server_deferred_action_ready
            (Ghost.reveal st)
            SQueries.ServerDeferredDeriveSharedSecret));
          let material_ready =
            Ghost.reveal (frame.server_ep_material_deferred_ready
              st
              SQueries.ServerDeferredDeriveSharedSecret);
          assert (pure (server_endpoint_material_matches_state
            frame
            (Ghost.reveal st)));
          assert (pure ((Ghost.reveal st).CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived));
          assert (pure ((Ghost.reveal st).CS.cs_model.CS.model_config.CS.config_role ==
            CS.ServerEndpoint));
          assert (pure (Some?
            (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_client_hello));
          assert (pure (Some?
            (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_server_selection));
          let selection : Ghost.erased CS.server_handshake_selection =
            Ghost.hide (Some?.v
              (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_server_selection);
          assert (pure (CS.server_selection_key_share_consistent (Ghost.reveal selection)));
          assert (pure (
            (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
              Some (Ghost.reveal selection).CS.server_selected_client_hello));
          assert (pure (Some? (Ghost.reveal selection).CS.server_key_share_private));
          Seq.lemma_eq_elim
            private_key
            (server_endpoint_private_bytes frame);
          Seq.lemma_eq_elim
            (Some?.v (Ghost.reveal selection).CS.server_key_share_private)
            (server_endpoint_private_bytes frame);
          assert (pure (Some?.v (Ghost.reveal selection).CS.server_key_share_private ==
            private_key));
          assert (pure (ST.server_local_event_input_ready
            (Ghost.reveal st)
            ST.LocalDeriveSharedSecret
            private_key));
          let old_local = Ghost.hide local_current;
          let local_frame =
            server_endpoint_private_local_frame frame old_local;
          V.to_array_pts_to frame.server_ep_private;
          rewrite
            (pts_to (V.vec_to_array frame.server_ep_private) private_key)
            as
            (pts_to
              local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
              private_key);
          rewrite
            (pts_to frame.server_ep_query.SQueries.server_query_local_app_out (Ghost.reveal local_current))
            as
            (pts_to
              local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
              (Ghost.reveal
                local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out));
          with network_current.
          fold (SQueries.server_network_persistent_resource frame.server_ep_query);
          with material.
          fold (server_endpoint_payload_remainder_ready
            frame
            ST.LocalDeriveSharedSecret);
          fold (server_endpoint_payload_local_action_frame
            frame
            (Ghost.reveal st)
            ST.LocalDeriveSharedSecret
            private_key
            local_frame);
          fold (server_endpoint_action_frame
            srv
            cfg
            frame
            (Ghost.reveal st)
            (PE.EndpointLocal
              (CTypes.ServerPayload
                ST.LocalDeriveSharedSecret
                (Ghost.hide private_key))
              local_frame));
          PE.EndpointLocal
            (CTypes.ServerPayload
              ST.LocalDeriveSharedSecret
              (Ghost.hide private_key))
            local_frame
        }
        SQueries.ServerDeferredSendServerHello -> {
          unfold (SQueries.server_next_local_action_frame_post
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st)
            (CQ.NextDeferredLocal ext));
          unfold (SQueries.server_next_local_action_frame_ready
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st));
          unfold (SQueries.server_network_persistent_resource frame.server_ep_query);
          with network_current. _;
          unfold (SQueries.server_local_persistent_resource frame.server_ep_query);
          with local_current. _;
          unfold (server_endpoint_payloads_ready frame);
          with material private_key. _;
          assert (pure (SQueries.server_deferred_action_ready
            (Ghost.reveal st)
            SQueries.ServerDeferredSendServerHello));
          let material_ready =
            Ghost.reveal (frame.server_ep_material_deferred_ready
              st
              SQueries.ServerDeferredSendServerHello);
          assert (pure (server_endpoint_material_matches_state
            frame
            (Ghost.reveal st)));
          unfold (SP.server_invariant
            srv
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st));
          with certificate_chain credential_identity. _;
          rewrite
            (S.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st))
            as
            (CR.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st));
          let ready =
            ConnQ.can_send_server_hello_runtime
              srv.SP.canonical_server_state;
          rewrite
            (CR.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st))
            as
            (S.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st));
          if ready {
            assert (pure (ready));
            assert (pure ((Ghost.reveal st).CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived));
            assert (pure ((Ghost.reveal st).CS.cs_model.CS.model_config.CS.config_role ==
              CS.ServerEndpoint));
            assert (pure (Some?
              (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret));
            assert (pure (
              (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_server_hello == None));
            assert (pure (Some?
              (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_server_selection));
            assert (pure (
              B.length (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_transcript +
                90 <= Bounds.max_transcript_len));
            assert (pure (B.length (CL.raw_slice material 0 32) == 32));
            assert (pure (B.length (CL.raw_slice material 32 64) == 32));
            let sh : Ghost.erased M.server_hello =
              Ghost.hide {
                M.random = CL.raw_slice material 0 32;
                M.key_share =
                  CryptoSpec.x25519_public_from_private (CL.raw_slice material 32 64);
                M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
                M.body = B.empty;
              };
            let selection : Ghost.erased CS.server_handshake_selection =
              Ghost.hide (Some?.v
                (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_server_selection);
            Seq.lemma_eq_elim
              material
              (server_endpoint_material_bytes frame);
            assert (pure (CS.server_hello_matches_selection
              (Ghost.reveal selection)
              (Ghost.reveal sh)));
            W.lemma_serialize_server_hello_from_selection_len (Ghost.reveal sh);
            W.lemma_fixed_server_handshake_serializers
              (Ghost.reveal sh)
              { M.chain = []; M.body = B.empty }
              { M.scheme = T.RsaPssRsaeSha256; M.signature = B.empty; M.body = B.empty }
              { M.verify_data = Seq.create 32 0uy };
            W.lemma_serialize_server_hello_len (Ghost.reveal sh);
            assert (pure (B.length (W.serialize_handshake (M.ServerHello (Ghost.reveal sh))) == 90));
            assert (pure (
              B.length (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_transcript +
                B.length (W.serialize_handshake (M.ServerHello (Ghost.reveal sh))) <=
                Bounds.max_transcript_len));
            assert (pure (CS.legal_event
              (Ghost.reveal st).CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.ServerHello (Ghost.reveal sh));
              })));
            assert (pure (CS.event_raw_delta_legal
              (Ghost.reveal st).CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.ServerHello (Ghost.reveal sh));
              })
              (CS.serialized_cleartext_tls_message
                (M.TlsHandshake (M.ServerHello (Ghost.reveal sh))))
              B.empty));
            assert (pure (CM.can_send_server_hello
              (Ghost.reveal st)
              (Ghost.reveal sh)
              (CS.serialized_cleartext_tls_message
                (M.TlsHandshake (M.ServerHello (Ghost.reveal sh))))));
            assert (pure (ST.server_local_event_input_ready
              (Ghost.reveal st)
              ST.LocalSendServerHello
              material));
            fold (SP.server_invariant
              srv
              (Ghost.reveal received)
              (Ghost.reveal sent)
              (Ghost.reveal st));
            let old_local = Ghost.hide local_current;
            let local_frame =
              server_endpoint_material_local_frame frame old_local;
            V.to_array_pts_to frame.server_ep_material;
            rewrite
              (pts_to (V.vec_to_array frame.server_ep_material) material)
              as
              (pts_to
                local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
                material);
            rewrite
              (pts_to frame.server_ep_query.SQueries.server_query_local_app_out (Ghost.reveal local_current))
              as
              (pts_to
                local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
                (Ghost.reveal
                  local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out));
            with network_current.
            fold (SQueries.server_network_persistent_resource frame.server_ep_query);
            with private_key.
            fold (server_endpoint_payload_remainder_ready
              frame
              ST.LocalSendServerHello);
            fold (server_endpoint_payload_local_action_frame
              frame
              (Ghost.reveal st)
              ST.LocalSendServerHello
              material
              local_frame);
            fold (server_endpoint_action_frame
              srv
              cfg
              frame
              (Ghost.reveal st)
              (PE.EndpointLocal
                (CTypes.ServerPayload
                  ST.LocalSendServerHello
                  (Ghost.hide material))
                local_frame));
            PE.EndpointLocal
              (CTypes.ServerPayload
                ST.LocalSendServerHello
                (Ghost.hide material))
              local_frame
          } else {
            fold (SP.server_invariant
              srv
              (Ghost.reveal received)
              (Ghost.reveal sent)
              (Ghost.reveal st));
            with material private_key.
            fold (server_endpoint_payloads_ready frame);
            with network_current.
            fold (SQueries.server_network_persistent_resource frame.server_ep_query);
            with local_current.
            fold (SQueries.server_local_persistent_resource frame.server_ep_query);
            fold (SQueries.server_next_local_action_frame_ready
              srv
              cfg
              frame.server_ep_query
              (Ghost.reveal st));
            fold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st));
            fold (server_endpoint_action_frame
              srv
              cfg
              frame
              (Ghost.reveal st)
              PE.EndpointFailed);
            PE.EndpointFailed
          }
        }
        SQueries.ServerDeferredSignCertificateVerify -> {
          unfold (SQueries.server_next_local_action_frame_post
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st)
            (CQ.NextDeferredLocal ext));
          unfold (SQueries.server_next_local_action_frame_ready
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st));
          unfold (SQueries.server_network_persistent_resource frame.server_ep_query);
          with network_current. _;
          unfold (SQueries.server_local_persistent_resource frame.server_ep_query);
          with local_current. _;
          unfold (SP.server_invariant
            srv
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st));
          with certificate_chain credential_identity. _;
          (Ghost.reveal srv.SP.canonical_server_supported_profile)
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st)
            certificate_chain
            credential_identity;
          assert (pure (SP.server_supported_profile_selection
            (Ghost.reveal st)
            credential_identity));
          assert (pure (SQueries.server_deferred_action_ready
            (Ghost.reveal st)
            SQueries.ServerDeferredSignCertificateVerify));
          assert (pure ((Ghost.reveal st).CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsServerEncryptedFlightSent));
          assert (pure ((Ghost.reveal st).CS.cs_model.CS.model_config.CS.config_role ==
            CS.ServerEndpoint));
          assert (pure ((Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_certificate <> None));
          assert (pure ((Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None));
          assert (pure (
            (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None));
          assert (pure (Some?
            (Ghost.reveal st).CS.cs_model.CS.model_config.CS.config_server));
          assert (pure (SP.server_selection_present_when_required (Ghost.reveal st)));
          assert (pure (Some?
            (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_server_selection));
          assert (pure (
            (Some?.v (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_server_selection)
              .CS.server_selected_signature_scheme ==
            T.RsaPssRsaeSha256));
          assert (pure (
            (Some?.v (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_server_selection)
              .CS.server_selected_credential == credential_identity));
          assert (pure (
            (Some?.v (Ghost.reveal st).CS.cs_model.CS.model_config.CS.config_server)
              .CS.server_credential_identity == credential_identity));
          assert (pure (
            (Some?.v (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_server_selection)
              .CS.server_selected_credential ==
            (Some?.v (Ghost.reveal st).CS.cs_model.CS.model_config.CS.config_server)
              .CS.server_credential_identity));
          assert (pure (CS.signature_scheme_offered
            (Ghost.reveal st).CS.cs_model.CS.model_config.CS.config_signature_schemes
            T.RsaPssRsaeSha256));
          assert (pure (ST.server_local_event_input_ready
            (Ghost.reveal st)
            ST.LocalSignCertificateVerify
            B.empty));
          fold (SP.server_invariant
            srv
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st));
          let local_frame =
            SQueries.server_local_frame_of_current
              frame.server_ep_query
              (Ghost.hide local_current);
          let api = {
            CTypes.server_local_kind = ST.LocalSignCertificateVerify;
            CTypes.server_local_payload = B.empty;
          };
          rewrite
            (pts_to frame.server_ep_query.SQueries.server_query_local_payload B.empty)
            as
            (pts_to
              local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
              B.empty);
          rewrite
            (pts_to frame.server_ep_query.SQueries.server_query_local_app_out (Ghost.reveal local_current))
            as
            (pts_to
              local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
              (Ghost.reveal
                local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out));
          fold (SQueries.server_local_frame_resource local_frame);
          with network_current.
          fold (SQueries.server_network_persistent_resource frame.server_ep_query);
          assert (pure (SQueries.server_local_event_ready
            (Ghost.reveal st)
            (CTypes.ServerAPI api)));
          fold (SQueries.server_next_local_action_frame_post
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st)
            (CQ.NextLocal (CTypes.ServerAPI api) local_frame));
          fold (server_endpoint_action_frame
            srv
            cfg
            frame
            (Ghost.reveal st)
            (PE.EndpointLocal (CTypes.ServerAPI api) local_frame));
          PE.EndpointLocal (CTypes.ServerAPI api) local_frame
        }
      }
    }
    CQ.NextDone -> {
      SQueries.cancel_server_next_action srv cfg frame.server_ep_query st CQ.NextDone;
      fold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st));
      fold (server_endpoint_action_frame
        srv
        cfg
        frame
        (Ghost.reveal st)
        PE.EndpointDone);
      PE.EndpointDone
    }
    CQ.NextFailed -> {
      SQueries.cancel_server_next_action srv cfg frame.server_ep_query st CQ.NextFailed;
      fold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st));
      fold (server_endpoint_action_frame
        srv
        cfg
        frame
        (Ghost.reveal st)
        PE.EndpointFailed);
      PE.EndpointFailed
    }
  }
}

fn server_endpoint_cancel_action
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
  (st:Ghost.erased CS.connection_state)
  (action:PE.endpoint_action
    SP.tls_server_network_bridge_frame
    CTypes.server_local_event
    SP.tls_server_local_bridge_frame)
requires server_endpoint_action_frame srv cfg frame (Ghost.reveal st) action
ensures server_endpoint_frame_ready srv cfg frame (Ghost.reveal st)
{
  unfold (server_endpoint_action_frame srv cfg frame (Ghost.reveal st) action);
  match action {
    PE.EndpointNeedInput network_frame -> {
      SQueries.cancel_server_next_action
        srv
        cfg
        frame.server_ep_query
        st
        (CQ.NextNeedInput network_frame);
      fold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st))
    }
    PE.EndpointLocal ev local_frame -> {
      match ev {
        CTypes.ServerPayload kind payload -> {
          unfold (server_endpoint_payload_local_action_frame
            frame
            (Ghost.reveal st)
            kind
            (Ghost.reveal payload)
            local_frame);
          assert (pure (server_endpoint_payload_frame_matches frame kind local_frame));
          rewrite
            (pts_to
              local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
              (Ghost.reveal
                local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out))
            as
            (pts_to
              frame.server_ep_query.SQueries.server_query_local_app_out
              (Ghost.reveal
                local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out));
          let old_local: Ghost.erased B.bytes =
            local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_old_app_out;
          with old_local.
          fold (SQueries.server_local_persistent_resource frame.server_ep_query);
          fold (SQueries.server_next_local_action_frame_ready
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st));
          match kind {
            ST.LocalSelectServerParameters -> {
              unfold (server_endpoint_payload_remainder_ready
                frame
                ST.LocalSelectServerParameters);
              with private_key. _;
              rewrite
                (pts_to
                  local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
                  (Ghost.reveal payload))
                as
                (pts_to
                  (V.vec_to_array frame.server_ep_material)
                  (Ghost.reveal payload));
              V.to_vec_pts_to frame.server_ep_material;
              fold (server_endpoint_payloads_ready frame);
              fold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st))
            }
            ST.LocalSendServerHello -> {
              unfold (server_endpoint_payload_remainder_ready
                frame
                ST.LocalSendServerHello);
              with private_key. _;
              rewrite
                (pts_to
                  local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
                  (Ghost.reveal payload))
                as
                (pts_to
                  (V.vec_to_array frame.server_ep_material)
                  (Ghost.reveal payload));
              V.to_vec_pts_to frame.server_ep_material;
              fold (server_endpoint_payloads_ready frame);
              fold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st))
            }
            ST.LocalDeriveSharedSecret -> {
              unfold (server_endpoint_payload_remainder_ready
                frame
                ST.LocalDeriveSharedSecret);
              with material. _;
              rewrite
                (pts_to
                  local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
                  (Ghost.reveal payload))
                as
                (pts_to
                  (V.vec_to_array frame.server_ep_private)
                  (Ghost.reveal payload));
              V.to_vec_pts_to frame.server_ep_private;
              fold (server_endpoint_payloads_ready frame);
              fold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st))
            }
            ST.LocalStartServer -> { assert (pure False); unreachable () }
            ST.LocalInstallClientHandshakeTrafficKeys -> { assert (pure False); unreachable () }
            ST.LocalInstallServerHandshakeTrafficKeys -> { assert (pure False); unreachable () }
            ST.LocalInstallClientApplicationTrafficKeys -> { assert (pure False); unreachable () }
            ST.LocalInstallServerApplicationTrafficKeys -> { assert (pure False); unreachable () }
            ST.LocalSignCertificateVerify -> { assert (pure False); unreachable () }
            ST.LocalVerifyClientFinished -> { assert (pure False); unreachable () }
            ST.LocalDeliverApplicationData -> { assert (pure False); unreachable () }
            ST.LocalSendEncryptedExtensions -> { assert (pure False); unreachable () }
            ST.LocalSendCertificate -> { assert (pure False); unreachable () }
            ST.LocalSendCertificateVerify -> { assert (pure False); unreachable () }
            ST.LocalSendServerFinished -> { assert (pure False); unreachable () }
            ST.LocalSendApplicationData -> { assert (pure False); unreachable () }
            ST.LocalSendCloseNotify -> { assert (pure False); unreachable () }
            ST.LocalFail -> { assert (pure False); unreachable () }
          }
        }
        CTypes.ServerAPI _ -> {
          SQueries.cancel_server_next_action
            srv
            cfg
            frame.server_ep_query
            st
            (CQ.NextLocal ev local_frame);
          fold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st))
        }
      }
    }
    PE.EndpointDone -> {
      ()
    }
    PE.EndpointFailed -> {
      ()
    }
  }
}

noeq
type server_network_io = {
  server_nio_input: array U8.t;
  server_nio_input_len: SZ.t;
  server_nio_output: array U8.t;
  server_nio_output_len: SZ.t;
  server_nio_input_contents: Ghost.erased B.bytes;
  server_nio_old_output: Ghost.erased B.bytes;
  server_nio_raw_received: Ghost.erased B.bytes;
}

let server_network_io_continuation
  (_srv:SP.canonical_server)
  (ch:TCP.channel)
  (frame:server_endpoint_frame)
  (_received:B.bytes)
  (sent:B.bytes)
  (_st:CS.connection_state)
  (nio:server_network_io)
  : slprop =
  TCP.is_channel ch (Ghost.reveal nio.server_nio_raw_received) sent **
  pure (
    nio.server_nio_input == V.vec_to_array frame.server_ep_raw /\
    nio.server_nio_output == V.vec_to_array frame.server_ep_network_out /\
    nio.server_nio_output_len == frame.server_ep_network_out_len /\
    B.length (Ghost.reveal nio.server_nio_input_contents) == SZ.v frame.server_ep_raw_len /\
    B.length (Ghost.reveal nio.server_nio_old_output) == SZ.v nio.server_nio_output_len)

let server_network_input (nio:server_network_io) : array U8.t =
  nio.server_nio_input

let server_network_input_len (nio:server_network_io) : SZ.t =
  nio.server_nio_input_len

let server_network_output (nio:server_network_io) : array U8.t =
  nio.server_nio_output

let server_network_output_len (nio:server_network_io) : SZ.t =
  nio.server_nio_output_len

let server_network_input_contents (nio:server_network_io) : Ghost.erased B.bytes =
  nio.server_nio_input_contents

let server_network_old_output (nio:server_network_io) : Ghost.erased B.bytes =
  nio.server_nio_old_output

fn server_prepare_network
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
  (ch:TCP.channel)
  (network_frame:SP.tls_server_network_bridge_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  server_endpoint_action_frame srv cfg frame (Ghost.reveal st) (PE.EndpointNeedInput network_frame) **
  server_endpoint_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
returns nio:server_network_io
ensures
  server_network_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio **
  PE.network_buffers
    (server_network_input nio)
    (server_network_input_len nio)
    (server_network_output nio)
    (server_network_output_len nio)
    (Ghost.reveal (server_network_input_contents nio))
    (Ghost.reveal (server_network_old_output nio)) **
  SP.server_network_bridge_frame_pre
    network_frame
    (server_network_input nio)
    (server_network_input_len nio)
    (server_network_output nio)
    (server_network_output_len nio)
    (Ghost.reveal (server_network_input_contents nio))
    (Ghost.reveal (server_network_old_output nio)) **
  server_endpoint_network_continuation srv cfg frame (Ghost.reveal st) network_frame **
  pure (
    CPI.buffers_wf
      (Ghost.reveal (server_network_input_contents nio))
      (server_network_input_len nio)
      (Ghost.reveal (server_network_old_output nio))
      (server_network_output_len nio))
{
  unfold (server_endpoint_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw_received raw_bytes network_out_bytes. _;
  V.to_array_pts_to frame.server_ep_raw;
  let nread = TCP.read_full ch (V.vec_to_array frame.server_ep_raw) frame.server_ep_raw_len;
  with raw_after chunk. _;
  let rawe = Ghost.hide (Seq.append raw_received chunk);
  assert (pure (Ghost.reveal rawe == Seq.append raw_received chunk));
  rewrite
    (TCP.is_channel ch (Seq.append raw_received chunk) (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal rawe) (Ghost.reveal sent));
  V.to_array_pts_to frame.server_ep_network_out;
  let inpute = Ghost.hide raw_after;
  let old_oute = Ghost.hide network_out_bytes;
  let nio = {
    server_nio_input = V.vec_to_array frame.server_ep_raw;
    server_nio_input_len = nread;
    server_nio_output = V.vec_to_array frame.server_ep_network_out;
    server_nio_output_len = frame.server_ep_network_out_len;
    server_nio_input_contents = inpute;
    server_nio_old_output = old_oute;
    server_nio_raw_received = rawe;
  };
  rewrite
    (TCP.is_channel ch (Ghost.reveal rawe) (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal nio.server_nio_raw_received) (Ghost.reveal sent));
  fold (server_network_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio);
  unfold (server_endpoint_action_frame srv cfg frame (Ghost.reveal st) (PE.EndpointNeedInput network_frame));
  rewrite
    (pts_to (V.vec_to_array frame.server_ep_raw) raw_after)
    as
    (pts_to (server_network_input nio) (Ghost.reveal (server_network_input_contents nio)));
  rewrite
    (pts_to (V.vec_to_array frame.server_ep_network_out) network_out_bytes)
    as
    (pts_to (server_network_output nio) (Ghost.reveal (server_network_old_output nio)));
  fold (CQ.network_buffers
    (server_network_input nio)
    (server_network_input_len nio)
    (server_network_output nio)
    (server_network_output_len nio)
    (Ghost.reveal (server_network_input_contents nio))
    (Ghost.reveal (server_network_old_output nio)));
  SQueries.prepare_server_next_action_network
    srv
    cfg
    frame.server_ep_query
    network_frame
    (server_network_input nio)
    (server_network_input_len nio)
    (server_network_output nio)
    (server_network_output_len nio)
    st
    (server_network_input_contents nio)
    (server_network_old_output nio);
  unfold (CQ.network_buffers
    (server_network_input nio)
    (server_network_input_len nio)
    (server_network_output nio)
    (server_network_output_len nio)
    (Ghost.reveal (server_network_input_contents nio))
    (Ghost.reveal (server_network_old_output nio)));
  fold (PE.network_buffers
    (server_network_input nio)
    (server_network_input_len nio)
    (server_network_output nio)
    (server_network_output_len nio)
    (Ghost.reveal (server_network_input_contents nio))
    (Ghost.reveal (server_network_old_output nio)));
  fold (server_endpoint_network_continuation srv cfg frame (Ghost.reveal st) network_frame);
  nio
}

fn server_finish_network_action
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
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
  server_endpoint_network_continuation srv cfg frame (Ghost.reveal st0) network_frame **
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
ensures server_endpoint_frame_ready srv cfg frame (Ghost.reveal st1)
{
  unfold (server_endpoint_network_continuation srv cfg frame (Ghost.reveal st0) network_frame);
  SQueries.finish_server_next_action_network
    srv
    cfg
    frame.server_ep_query
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
  fold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st1))
}

fn server_finish_network_io
  (srv:SP.canonical_server)
  (ch:TCP.channel)
  (frame:server_endpoint_frame)
  (nio:server_network_io)
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
  server_network_io_continuation srv ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) nio **
  pts_to (server_network_input nio) (Ghost.reveal (server_network_input_contents nio)) **
  pts_to (server_network_output nio) (Ghost.reveal out_contents) **
  pure (
    CPI.network_process_correct
      (SP.server_protocol_implementation.CPI.pi_system srv)
      (Ghost.reveal (server_network_input_contents nio))
      (server_network_input_len nio)
      (Ghost.reveal (server_network_old_output nio))
      (Ghost.reveal out_contents)
      (server_network_output_len nio)
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
ensures server_endpoint_io_ready srv ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
{
  unfold (server_network_io_continuation srv ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) nio);
  CPI.lemma_network_process_sent_output_prefix
    (SP.server_protocol_implementation.CPI.pi_system srv)
    (Ghost.reveal (server_network_input_contents nio))
    (server_network_input_len nio)
    (Ghost.reveal (server_network_old_output nio))
    (Ghost.reveal out_contents)
    (server_network_output_len nio)
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
  let nwritten = TCP.write ch (server_network_output nio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal nio.server_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel
      ch
      (Ghost.reveal nio.server_nio_raw_received)
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
      (Ghost.reveal nio.server_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal nio.server_nio_raw_received) (Ghost.reveal sent1));
  rewrite
    (pts_to (server_network_input nio) (Ghost.reveal (server_network_input_contents nio)))
    as
    (pts_to (V.vec_to_array frame.server_ep_raw) (Ghost.reveal (server_network_input_contents nio)));
  rewrite
    (pts_to (server_network_output nio) (Ghost.reveal out_contents))
    as
    (pts_to (V.vec_to_array frame.server_ep_network_out) (Ghost.reveal out_contents));
  V.to_vec_pts_to frame.server_ep_raw;
  V.to_vec_pts_to frame.server_ep_network_out;
  fold (server_endpoint_io_ready srv ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
}

fn server_run_buffered_network_action
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
  (ch:TCP.channel)
  (network_frame:SP.tls_server_network_bridge_frame)
  (input_len:SZ.t)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  server_endpoint_action_frame
    srv
    cfg
    frame
    (Ghost.reveal st)
    (PE.EndpointNeedInput network_frame) **
  server_endpoint_io_ready
    srv
    ch
    frame
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  pure (SZ.v input_len <= SZ.v frame.server_ep_raw_len)
returns result:CPI.process_result
ensures
  exists* (received1:Ghost.erased B.bytes)
          (sent1:Ghost.erased B.bytes)
          (st1:Ghost.erased CS.connection_state).
    SP.server_invariant
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    server_endpoint_frame_ready
      srv
      cfg
      frame
      (Ghost.reveal st1) **
    server_endpoint_io_ready
      srv
      ch
      frame
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
{
  unfold (server_endpoint_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw_received raw_bytes network_out_bytes. _;
  V.to_array_pts_to frame.server_ep_raw;
  V.to_array_pts_to frame.server_ep_network_out;
  let input_vec = V.alloc 0uy input_len;
  V.to_array_pts_to input_vec;
  SC.copy_array_slice_to_array
    (V.vec_to_array frame.server_ep_raw)
    frame.server_ep_raw_len
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
    server_nio_input = V.vec_to_array input_vec;
    server_nio_input_len = input_len;
    server_nio_output = V.vec_to_array frame.server_ep_network_out;
    server_nio_output_len = frame.server_ep_network_out_len;
    server_nio_input_contents = inpute;
    server_nio_old_output = old_oute;
    server_nio_raw_received = raw_receivede;
  };
  rewrite
    (TCP.is_channel ch raw_received (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal nio.server_nio_raw_received) (Ghost.reveal sent));
  unfold (server_endpoint_action_frame srv cfg frame (Ghost.reveal st) (PE.EndpointNeedInput network_frame));
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
    (pts_to (server_network_input nio) (Ghost.reveal (server_network_input_contents nio)));
  rewrite
    (pts_to (V.vec_to_array frame.server_ep_network_out) network_out_bytes)
    as
    (pts_to (server_network_output nio) (Ghost.reveal (server_network_old_output nio)));
  fold (CQ.network_buffers
    (server_network_input nio)
    (server_network_input_len nio)
    (server_network_output nio)
    (server_network_output_len nio)
    (Ghost.reveal (server_network_input_contents nio))
    (Ghost.reveal (server_network_old_output nio)));
  SQueries.prepare_server_next_action_network
    srv
    cfg
    frame.server_ep_query
    network_frame
    (server_network_input nio)
    (server_network_input_len nio)
    (server_network_output nio)
    (server_network_output_len nio)
    st
    (server_network_input_contents nio)
    (server_network_old_output nio);
  unfold (CQ.network_buffers
    (server_network_input nio)
    (server_network_input_len nio)
    (server_network_output nio)
    (server_network_output_len nio)
    (Ghost.reveal (server_network_input_contents nio))
    (Ghost.reveal (server_network_old_output nio)));
  fold (PE.network_buffers
    (server_network_input nio)
    (server_network_input_len nio)
    (server_network_output nio)
    (server_network_output_len nio)
    (Ghost.reveal (server_network_input_contents nio))
    (Ghost.reveal (server_network_old_output nio)));
  fold (server_endpoint_network_continuation srv cfg frame (Ghost.reveal st) network_frame);
  let result =
    SP.server_process_network
      srv
      network_frame
      (server_network_input nio)
      (server_network_input_len nio)
      (server_network_output nio)
      (server_network_output_len nio)
      received
      sent
      st
      (server_network_input_contents nio)
      (server_network_old_output nio);
  unfold (SP.server_process_network_post
    srv
    network_frame
    (server_network_input nio)
    (server_network_input_len nio)
    (server_network_output nio)
    (server_network_output_len nio)
    received
    sent
    st
    (server_network_input_contents nio)
    (server_network_old_output nio)
    result);
  with received1 sent1 st1 out_contents consumed wire_outputs local_outputs.
  assert (
    SP.server_invariant
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    SP.server_network_bridge_frame_post
      network_frame
      result
      (Ghost.reveal (server_network_input_contents nio))
      (server_network_input_len nio)
      (Ghost.reveal (server_network_old_output nio))
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
    (SP.server_network_bridge_frame_post
      network_frame
      result
      (Ghost.reveal (server_network_input_contents nio))
      (server_network_input_len nio)
      (Ghost.reveal (server_network_old_output nio))
      out_contents
      (Ghost.reveal st)
      (Ghost.reveal st1)
      consumed
      wire_outputs
      local_outputs)
    as
    (SP.server_network_bridge_frame_post
      network_frame
      result
      (Ghost.reveal (server_network_input_contents nio))
      (server_network_input_len nio)
      (Ghost.reveal (server_network_old_output nio))
      (Ghost.reveal out_contentse)
      (Ghost.reveal st)
      (Ghost.reveal st1)
      (Ghost.reveal consumede)
      (Ghost.reveal wire_outputse)
      (Ghost.reveal local_outputse));
  server_finish_network_action
    srv
    cfg
    frame
    network_frame
    result
    (server_network_input_contents nio)
    (server_network_input_len nio)
    (server_network_old_output nio)
    out_contentse
    st
    st1
    consumede
    wire_outputse
    local_outputse;
  rewrite
    (pts_to (server_network_output nio) out_contents)
    as
    (pts_to (server_network_output nio) (Ghost.reveal out_contentse));
  CPI.lemma_network_process_sent_output_prefix
    (SP.server_protocol_implementation.CPI.pi_system srv)
    (Ghost.reveal (server_network_input_contents nio))
    (server_network_input_len nio)
    (Ghost.reveal (server_network_old_output nio))
    (Ghost.reveal out_contentse)
    (server_network_output_len nio)
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
  let nwritten = TCP.write ch (server_network_output nio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal nio.server_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contentse)
         then Seq.slice (Ghost.reveal out_contentse) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel
      ch
      (Ghost.reveal nio.server_nio_raw_received)
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
      (Ghost.reveal nio.server_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contentse)
         then Seq.slice (Ghost.reveal out_contentse) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal nio.server_nio_raw_received) (Ghost.reveal sent1));
  rewrite
    (pts_to (server_network_output nio) (Ghost.reveal out_contentse))
    as
    (pts_to (V.vec_to_array frame.server_ep_network_out) (Ghost.reveal out_contentse));
  rewrite
    (pts_to (server_network_input nio) (Ghost.reveal (server_network_input_contents nio)))
    as
    (pts_to (V.vec_to_array input_vec) (Ghost.reveal (server_network_input_contents nio)));
  V.to_vec_pts_to input_vec;
  V.free input_vec;
  V.to_vec_pts_to frame.server_ep_raw;
  V.to_vec_pts_to frame.server_ep_network_out;
  fold (server_endpoint_io_ready srv ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
  result
}

noeq
type server_local_io = {
  server_lio_output: array U8.t;
  server_lio_output_len: SZ.t;
  server_lio_old_output: Ghost.erased B.bytes;
  server_lio_raw_received: Ghost.erased B.bytes;
}

let server_local_io_continuation
  (_srv:SP.canonical_server)
  (ch:TCP.channel)
  (frame:server_endpoint_frame)
  (_received:B.bytes)
  (sent:B.bytes)
  (_st:CS.connection_state)
  (_ev:CTypes.server_local_event)
  (lio:server_local_io)
  : slprop =
  exists* raw_bytes.
    TCP.is_channel ch (Ghost.reveal lio.server_lio_raw_received) sent **
    V.pts_to frame.server_ep_raw #1.0R raw_bytes **
    pure (
      lio.server_lio_output == V.vec_to_array frame.server_ep_network_out /\
      lio.server_lio_output_len == frame.server_ep_network_out_len /\
      B.length (Ghost.reveal lio.server_lio_old_output) == SZ.v lio.server_lio_output_len /\
      B.length raw_bytes == SZ.v frame.server_ep_raw_len)

let server_local_output (lio:server_local_io) : array U8.t =
  lio.server_lio_output

let server_local_output_len (lio:server_local_io) : SZ.t =
  lio.server_lio_output_len

let server_local_old_output (lio:server_local_io) : Ghost.erased B.bytes =
  lio.server_lio_old_output

fn server_prepare_local
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
  (ch:TCP.channel)
  (ev:CTypes.server_local_event)
  (local_frame:SP.tls_server_local_bridge_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  server_endpoint_action_frame srv cfg frame (Ghost.reveal st) (PE.EndpointLocal ev local_frame) **
  server_endpoint_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
returns lio:server_local_io
ensures
  server_local_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio **
  PE.local_output_buffer
    (server_local_output lio)
    (server_local_output_len lio)
    (Ghost.reveal (server_local_old_output lio)) **
  SP.server_local_bridge_frame_pre
    ev
    local_frame
    (Ghost.reveal st)
    (server_local_output lio)
    (server_local_output_len lio)
    (Ghost.reveal (server_local_old_output lio)) **
  server_endpoint_local_continuation srv cfg frame (Ghost.reveal st) ev local_frame
{
  unfold (server_endpoint_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw_received raw_bytes network_out_bytes. _;
  let rawe = Ghost.hide raw_received;
  let old_oute = Ghost.hide network_out_bytes;
  V.to_array_pts_to frame.server_ep_network_out;
  let lio = {
    server_lio_output = V.vec_to_array frame.server_ep_network_out;
    server_lio_output_len = frame.server_ep_network_out_len;
    server_lio_old_output = old_oute;
    server_lio_raw_received = rawe;
  };
  rewrite
    (TCP.is_channel ch raw_received (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal lio.server_lio_raw_received) (Ghost.reveal sent));
  fold (server_local_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio);
  unfold (server_endpoint_action_frame srv cfg frame (Ghost.reveal st) (PE.EndpointLocal ev local_frame));
  rewrite
    (pts_to (V.vec_to_array frame.server_ep_network_out) network_out_bytes)
    as
    (pts_to (server_local_output lio) (Ghost.reveal (server_local_old_output lio)));
  fold (CQ.local_output_buffer
    (server_local_output lio)
    (server_local_output_len lio)
    (Ghost.reveal (server_local_old_output lio)));
  match ev {
    CTypes.ServerAPI api -> {
      SQueries.prepare_server_next_action_local
        srv
        cfg
        frame.server_ep_query
        (CTypes.ServerAPI api)
        local_frame
        (server_local_output lio)
        (server_local_output_len lio)
        st
        (server_local_old_output lio);
      unfold (CQ.local_output_buffer
        (server_local_output lio)
        (server_local_output_len lio)
        (Ghost.reveal (server_local_old_output lio)));
      fold (PE.local_output_buffer
        (server_local_output lio)
        (server_local_output_len lio)
        (Ghost.reveal (server_local_old_output lio)));
      fold (server_endpoint_local_continuation
        srv
        cfg
        frame
        (Ghost.reveal st)
        (CTypes.ServerAPI api)
        local_frame);
      rewrite
        (server_local_io_continuation
          srv
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st)
          (CTypes.ServerAPI api)
          lio)
        as
        (server_local_io_continuation
          srv
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st)
          ev
          lio);
      rewrite
        (server_endpoint_local_continuation
          srv
          cfg
          frame
          (Ghost.reveal st)
          (CTypes.ServerAPI api)
          local_frame)
        as
        (server_endpoint_local_continuation
          srv
          cfg
          frame
          (Ghost.reveal st)
          ev
          local_frame);
      lio
    }
    CTypes.ServerPayload kind payload -> {
      unfold (CQ.local_output_buffer
        (server_local_output lio)
        (server_local_output_len lio)
        (Ghost.reveal (server_local_old_output lio)));
      fold (PE.local_output_buffer
        (server_local_output lio)
        (server_local_output_len lio)
        (Ghost.reveal (server_local_old_output lio)));
      unfold (server_endpoint_payload_local_action_frame
        frame
        (Ghost.reveal st)
        kind
        (Ghost.reveal payload)
        local_frame);
      fold (SP.server_local_bridge_frame_pre
        (CTypes.ServerPayload kind payload)
        local_frame
        (Ghost.reveal st)
        (server_local_output lio)
        (server_local_output_len lio)
        (Ghost.reveal (server_local_old_output lio)));
      fold (server_endpoint_payload_local_continuation
        frame
        (Ghost.reveal st)
        kind
        (Ghost.reveal payload)
        local_frame);
      fold (server_endpoint_local_continuation
        srv
        cfg
        frame
        (Ghost.reveal st)
        (CTypes.ServerPayload kind payload)
        local_frame);
      rewrite
        (server_local_io_continuation
          srv
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st)
          (CTypes.ServerPayload kind payload)
          lio)
        as
        (server_local_io_continuation
          srv
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st)
          ev
          lio);
      rewrite
        (server_endpoint_local_continuation
          srv
          cfg
          frame
          (Ghost.reveal st)
          (CTypes.ServerPayload kind payload)
          local_frame)
        as
        (server_endpoint_local_continuation
          srv
          cfg
          frame
          (Ghost.reveal st)
          ev
          local_frame);
      lio
    }
  }
}

fn server_prepare_local_with_output
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
  (ev:CTypes.server_local_event)
  (local_frame:SP.tls_server_local_bridge_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (old_out:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  server_endpoint_action_frame srv cfg frame (Ghost.reveal st) (PE.EndpointLocal ev local_frame) **
  pts_to out (Ghost.reveal old_out) **
  pure (B.length (Ghost.reveal old_out) == SZ.v out_len)
ensures
  PE.local_output_buffer out out_len (Ghost.reveal old_out) **
  SP.server_local_bridge_frame_pre
    ev
    local_frame
    (Ghost.reveal st)
    out
    out_len
    (Ghost.reveal old_out) **
  server_endpoint_local_continuation srv cfg frame (Ghost.reveal st) ev local_frame
{
  unfold (server_endpoint_action_frame srv cfg frame (Ghost.reveal st) (PE.EndpointLocal ev local_frame));
  fold (CQ.local_output_buffer
    out
    out_len
    (Ghost.reveal old_out));
  match ev {
    CTypes.ServerAPI api -> {
      SQueries.prepare_server_next_action_local
        srv
        cfg
        frame.server_ep_query
        (CTypes.ServerAPI api)
        local_frame
        out
        out_len
        st
        old_out;
      unfold (CQ.local_output_buffer
        out
        out_len
        (Ghost.reveal old_out));
      fold (PE.local_output_buffer
        out
        out_len
        (Ghost.reveal old_out));
      fold (server_endpoint_local_continuation
        srv
        cfg
        frame
        (Ghost.reveal st)
        (CTypes.ServerAPI api)
        local_frame);
      rewrite
        (server_endpoint_local_continuation
          srv
          cfg
          frame
          (Ghost.reveal st)
          (CTypes.ServerAPI api)
          local_frame)
        as
        (server_endpoint_local_continuation
          srv
          cfg
          frame
          (Ghost.reveal st)
          ev
          local_frame)
    }
    CTypes.ServerPayload kind payload -> {
      unfold (CQ.local_output_buffer
        out
        out_len
        (Ghost.reveal old_out));
      fold (PE.local_output_buffer
        out
        out_len
        (Ghost.reveal old_out));
      unfold (server_endpoint_payload_local_action_frame
        frame
        (Ghost.reveal st)
        kind
        (Ghost.reveal payload)
        local_frame);
      fold (SP.server_local_bridge_frame_pre
        (CTypes.ServerPayload kind payload)
        local_frame
        (Ghost.reveal st)
        out
        out_len
        (Ghost.reveal old_out));
      fold (server_endpoint_payload_local_continuation
        frame
        (Ghost.reveal st)
        kind
        (Ghost.reveal payload)
        local_frame);
      fold (server_endpoint_local_continuation
        srv
        cfg
        frame
        (Ghost.reveal st)
        (CTypes.ServerPayload kind payload)
        local_frame);
      rewrite
        (server_endpoint_local_continuation
          srv
          cfg
          frame
          (Ghost.reveal st)
          (CTypes.ServerPayload kind payload)
          local_frame)
        as
        (server_endpoint_local_continuation
          srv
          cfg
          frame
          (Ghost.reveal st)
          ev
          local_frame)
    }
  }
}

fn server_finish_local_action
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
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
  server_endpoint_local_continuation srv cfg frame (Ghost.reveal st0) ev local_frame **
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
ensures server_endpoint_frame_ready srv cfg frame (Ghost.reveal st1)
{
  unfold (server_endpoint_local_continuation srv cfg frame (Ghost.reveal st0) ev local_frame);
  match ev {
    CTypes.ServerAPI api -> {
      SQueries.finish_server_next_action_local
        srv
        cfg
        frame.server_ep_query
        (CTypes.ServerAPI api)
        local_frame
        result
        old_out
        out_contents
        st0
        st1
        wire_outputs
        local_outputs;
      fold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st1))
    }
    CTypes.ServerPayload kind payload -> {
      unfold (server_endpoint_payload_local_continuation
        frame
        (Ghost.reveal st0)
        kind
        (Ghost.reveal payload)
        local_frame);
      assert (pure (server_endpoint_payload_frame_matches frame kind local_frame));
      unfold (SP.server_local_bridge_frame_post
        (CTypes.ServerPayload kind payload)
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
          local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
          app_out)
        as
        (pts_to frame.server_ep_query.SQueries.server_query_local_app_out app_out);
      with app_out.
      fold (SQueries.server_local_persistent_resource frame.server_ep_query);
      fold (SQueries.server_next_local_action_frame_ready
        srv
        cfg
        frame.server_ep_query
        (Ghost.reveal st1));
      match kind {
        ST.LocalSelectServerParameters -> {
          unfold (server_endpoint_payload_remainder_ready
            frame
            ST.LocalSelectServerParameters);
          with private_key. _;
          rewrite
            (pts_to
              local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
              (CTypes.server_local_event_api (CTypes.ServerPayload kind payload)).CTypes.server_local_payload)
            as
            (pts_to
              (V.vec_to_array frame.server_ep_material)
              (Ghost.reveal payload));
          V.to_vec_pts_to frame.server_ep_material;
          fold (server_endpoint_payloads_ready frame);
          fold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st1))
        }
        ST.LocalSendServerHello -> {
          unfold (server_endpoint_payload_remainder_ready
            frame
            ST.LocalSendServerHello);
          with private_key. _;
          rewrite
            (pts_to
              local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
              (CTypes.server_local_event_api (CTypes.ServerPayload kind payload)).CTypes.server_local_payload)
            as
            (pts_to
              (V.vec_to_array frame.server_ep_material)
              (Ghost.reveal payload));
          V.to_vec_pts_to frame.server_ep_material;
          fold (server_endpoint_payloads_ready frame);
          fold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st1))
        }
        ST.LocalDeriveSharedSecret -> {
          unfold (server_endpoint_payload_remainder_ready
            frame
            ST.LocalDeriveSharedSecret);
          with material. _;
          rewrite
            (pts_to
              local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
              (CTypes.server_local_event_api (CTypes.ServerPayload kind payload)).CTypes.server_local_payload)
            as
            (pts_to
              (V.vec_to_array frame.server_ep_private)
              (Ghost.reveal payload));
          V.to_vec_pts_to frame.server_ep_private;
          fold (server_endpoint_payloads_ready frame);
          fold (server_endpoint_frame_ready srv cfg frame (Ghost.reveal st1))
        }
        ST.LocalStartServer -> { assert (pure False); unreachable () }
        ST.LocalInstallClientHandshakeTrafficKeys -> { assert (pure False); unreachable () }
        ST.LocalInstallServerHandshakeTrafficKeys -> { assert (pure False); unreachable () }
        ST.LocalInstallClientApplicationTrafficKeys -> { assert (pure False); unreachable () }
        ST.LocalInstallServerApplicationTrafficKeys -> { assert (pure False); unreachable () }
        ST.LocalSignCertificateVerify -> { assert (pure False); unreachable () }
        ST.LocalVerifyClientFinished -> { assert (pure False); unreachable () }
        ST.LocalDeliverApplicationData -> { assert (pure False); unreachable () }
        ST.LocalSendEncryptedExtensions -> { assert (pure False); unreachable () }
        ST.LocalSendCertificate -> { assert (pure False); unreachable () }
        ST.LocalSendCertificateVerify -> { assert (pure False); unreachable () }
        ST.LocalSendServerFinished -> { assert (pure False); unreachable () }
        ST.LocalSendApplicationData -> { assert (pure False); unreachable () }
        ST.LocalSendCloseNotify -> { assert (pure False); unreachable () }
        ST.LocalFail -> { assert (pure False); unreachable () }
      }
    }
  }
}

fn server_finish_local_io
  (srv:SP.canonical_server)
  (ch:TCP.channel)
  (frame:server_endpoint_frame)
  (lio:server_local_io)
  (ev:CTypes.server_local_event)
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
  server_local_io_continuation srv ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) ev lio **
  pts_to (server_local_output lio) (Ghost.reveal out_contents) **
  pure (
    CPI.local_process_correct
      (SP.server_protocol_implementation.CPI.pi_system srv)
      ev
      (Ghost.reveal (server_local_old_output lio))
      (Ghost.reveal out_contents)
      (server_local_output_len lio)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs))
ensures server_endpoint_io_ready srv ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
{
  unfold (server_local_io_continuation srv ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) ev lio);
  with raw_bytes. _;
  CPI.lemma_local_process_sent_output_prefix
    (SP.server_protocol_implementation.CPI.pi_system srv)
    ev
    (Ghost.reveal (server_local_old_output lio))
    (Ghost.reveal out_contents)
    (server_local_output_len lio)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs);
  let nwritten = TCP.write ch (server_local_output lio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal lio.server_lio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel
      ch
      (Ghost.reveal lio.server_lio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal lio.server_lio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal lio.server_lio_raw_received) (Ghost.reveal sent1));
  rewrite
    (pts_to (server_local_output lio) (Ghost.reveal out_contents))
    as
    (pts_to (V.vec_to_array frame.server_ep_network_out) (Ghost.reveal out_contents));
  V.to_vec_pts_to frame.server_ep_network_out;
  fold (server_endpoint_io_ready srv ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
}

let server_pending_after_consumed (buffered_len consumed_len:SZ.t) : SZ.t =
  if SZ.lte consumed_len buffered_len
  then SZ.sub buffered_len consumed_len
  else 0sz

fn server_compact_buffer_suffix
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
                 new_len == server_pending_after_consumed buffered_len consumed_len /\
                 SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
                 SZ.v new_len <= SZ.v buffered_len /\
                 Seq.equal
                   (Seq.slice raw_after 0 (SZ.v new_len))
                   (Seq.slice (Ghost.reveal 'raw_bytes)
                     (SZ.v consumed_len)
                     (SZ.v buffered_len)))
{
  let new_len = SZ.sub buffered_len consumed_len;
  assert (pure (new_len == server_pending_after_consumed buffered_len consumed_len));
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

fn server_compact_buffered_input
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
                 new_len == server_pending_after_consumed buffered_len consumed_len /\
                 SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
                 SZ.v new_len <= SZ.v buffered_len)
{
  V.to_array_pts_to raw;
  let new_len =
    server_compact_buffer_suffix
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

fn server_compact_endpoint_input
  (srv:SP.canonical_server)
  (ch:TCP.channel)
  (frame:server_endpoint_frame)
  (buffered_len_ref:Box.box SZ.t)
  (buffered_len:SZ.t)
  (consumed_len:SZ.t)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
  requires server_endpoint_io_ready
             srv
             ch
             frame
             (Ghost.reveal received)
             (Ghost.reveal sent)
             (Ghost.reveal st) **
           Box.pts_to buffered_len_ref 'old_buffered_len **
           pure (SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v frame.server_ep_raw_len)
  returns new_len:SZ.t
  ensures server_endpoint_io_ready
            srv
            ch
            frame
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st) **
          Box.pts_to buffered_len_ref new_len **
          pure (new_len == server_pending_after_consumed buffered_len consumed_len /\
                SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
                SZ.v new_len <= SZ.v frame.server_ep_raw_len)
{
  unfold (server_endpoint_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw_received raw_bytes network_out_bytes. _;
  let new_len =
    server_compact_buffered_input
      frame.server_ep_raw
      frame.server_ep_raw_len
      buffered_len_ref
      buffered_len
      consumed_len;
  with raw_after.
    assert (V.pts_to frame.server_ep_raw #1.0R raw_after **
            Box.pts_to buffered_len_ref new_len);
  fold (server_endpoint_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  assert (pure (SZ.v new_len <= SZ.v buffered_len));
  assert (pure (SZ.v buffered_len <= SZ.v frame.server_ep_raw_len));
  new_len
}

fn server_read_into_raw_suffix
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

fn server_read_more_endpoint_input
  (srv:SP.canonical_server)
  (ch:TCP.channel)
  (frame:server_endpoint_frame)
  (offset:SZ.t)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
  requires server_endpoint_io_ready
             srv
             ch
             frame
             (Ghost.reveal received)
             (Ghost.reveal sent)
             (Ghost.reveal st) **
           pure (SZ.v offset <= SZ.v frame.server_ep_raw_len)
  returns read_len:SZ.t
  ensures server_endpoint_io_ready
            srv
            ch
            frame
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st) **
          pure (SZ.v read_len <= SZ.v frame.server_ep_raw_len - SZ.v offset)
{
  unfold (server_endpoint_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw_received raw_bytes network_out_bytes. _;
  let read_len =
    server_read_into_raw_suffix
      ch
      frame.server_ep_raw
      frame.server_ep_raw_len
      offset;
  with raw_received_after raw_after.
    assert (TCP.is_channel ch raw_received_after (Ghost.reveal sent) **
            V.pts_to frame.server_ep_raw #1.0R raw_after);
  fold (server_endpoint_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  read_len
}

let server_api_local_action_ready
  (_srv:SP.canonical_server)
  (ch:TCP.channel)
  (frame:server_endpoint_frame)
  (_received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  (ev:CTypes.server_local_event)
  (local_frame:SP.tls_server_local_bridge_frame)
  : slprop =
  exists* raw_received raw_bytes network_out_bytes.
    TCP.is_channel ch raw_received sent **
    V.pts_to frame.server_ep_raw #1.0R raw_bytes **
    V.pts_to frame.server_ep_network_out #1.0R network_out_bytes **
    SP.server_local_bridge_frame_pre
      ev
      local_frame
      st
      (V.vec_to_array frame.server_ep_network_out)
      frame.server_ep_network_out_len
      network_out_bytes **
    pure (
      B.length raw_bytes == SZ.v frame.server_ep_raw_len /\
      B.length network_out_bytes == SZ.v frame.server_ep_network_out_len)

fn server_run_api_local_action
  (srv:SP.canonical_server)
  (frame:server_endpoint_frame)
  (ch:TCP.channel)
  (ev:CTypes.server_local_event)
  (local_frame:SP.tls_server_local_bridge_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  server_api_local_action_ready
    srv
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
    SP.server_invariant
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    server_endpoint_io_ready
      srv
      ch
      frame
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    SP.server_local_bridge_frame_post
      ev
      local_frame
      result
      (Ghost.reveal old_out)
      (Ghost.reveal out_contents)
      (Ghost.reveal st)
      (Ghost.reveal st1)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs) **
    pure (
      CPI.local_process_correct
        (SP.server_system (Ghost.reveal srv.SP.canonical_server_initial))
        ev
        (Ghost.reveal old_out)
        (Ghost.reveal out_contents)
        frame.server_ep_network_out_len
        (Ghost.reveal received)
        (Ghost.reveal sent)
        (Ghost.reveal st)
        result
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1)
        (Ghost.reveal wire_outputs)
        (Ghost.reveal local_outputs))
{
  unfold (server_api_local_action_ready
    srv
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
  V.to_array_pts_to frame.server_ep_network_out;
  let lio = {
    server_lio_output = V.vec_to_array frame.server_ep_network_out;
    server_lio_output_len = frame.server_ep_network_out_len;
    server_lio_old_output = old_oute;
    server_lio_raw_received = rawe;
  };
  rewrite
    (TCP.is_channel ch raw_received (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal lio.server_lio_raw_received) (Ghost.reveal sent));
  fold (server_local_io_continuation
    srv
    ch
    frame
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)
    ev
    lio);
  rewrite
    (pts_to (V.vec_to_array frame.server_ep_network_out) network_out_bytes)
    as
    (pts_to (server_local_output lio) (Ghost.reveal (server_local_old_output lio)));
  let result =
    SP.server_process_local
      srv
      ev
      local_frame
      (server_local_output lio)
      (server_local_output_len lio)
      received
      sent
      st
      (server_local_old_output lio);
  with received1 sent1 st1 out_contents wire_outputs local_outputs.
  assert (
    SP.server_invariant
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    SP.server_local_bridge_frame_post
      ev
      local_frame
      result
      (Ghost.reveal (server_local_old_output lio))
      out_contents
      (Ghost.reveal st)
      (Ghost.reveal st1)
      wire_outputs
      local_outputs);
  let out_contentse = Ghost.hide out_contents;
  let wire_outputse = Ghost.hide wire_outputs;
  let local_outputse = Ghost.hide local_outputs;
  rewrite
    (SP.server_local_bridge_frame_post
      ev
      local_frame
      result
      (Ghost.reveal (server_local_old_output lio))
      out_contents
      (Ghost.reveal st)
      (Ghost.reveal st1)
      wire_outputs
      local_outputs)
    as
    (SP.server_local_bridge_frame_post
      ev
      local_frame
      result
      (Ghost.reveal (server_local_old_output lio))
      (Ghost.reveal out_contentse)
      (Ghost.reveal st)
      (Ghost.reveal st1)
      (Ghost.reveal wire_outputse)
      (Ghost.reveal local_outputse));
  assert (pure (
    CPI.local_process_correct
      (SP.server_system (Ghost.reveal srv.SP.canonical_server_initial))
      ev
      (Ghost.reveal (server_local_old_output lio))
      (Ghost.reveal out_contentse)
      frame.server_ep_network_out_len
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Ghost.reveal st)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      (Ghost.reveal wire_outputse)
      (Ghost.reveal local_outputse)));
  server_finish_local_io
    srv
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

fn server_run_scheduled_local_action
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
  (ch:TCP.channel)
  (ev:CTypes.server_local_event)
  (local_frame:SP.tls_server_local_bridge_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  server_endpoint_action_frame
    srv
    cfg
    frame
    (Ghost.reveal st)
    (PE.EndpointLocal ev local_frame) **
  server_endpoint_io_ready
    srv
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
    SP.server_invariant
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    server_endpoint_frame_ready
      srv
      cfg
      frame
      (Ghost.reveal st1) **
    server_endpoint_io_ready
      srv
      ch
      frame
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
{
  let lio =
    server_prepare_local
      srv
      cfg
      frame
      ch
      ev
      local_frame
      received
      sent
      st;
  let result =
    SP.server_process_local
      srv
      ev
      local_frame
      (server_local_output lio)
      (server_local_output_len lio)
      received
      sent
      st
      (server_local_old_output lio);
  with received1 sent1 st1 out_contents wire_outputs local_outputs.
  assert (
    SP.server_invariant
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    SP.server_local_bridge_frame_post
      ev
      local_frame
      result
      (Ghost.reveal (server_local_old_output lio))
      out_contents
      (Ghost.reveal st)
      (Ghost.reveal st1)
      wire_outputs
      local_outputs);
  let out_contentse = Ghost.hide out_contents;
  let wire_outputse = Ghost.hide wire_outputs;
  let local_outputse = Ghost.hide local_outputs;
  rewrite
    (SP.server_local_bridge_frame_post
      ev
      local_frame
      result
      (Ghost.reveal (server_local_old_output lio))
      out_contents
      (Ghost.reveal st)
      (Ghost.reveal st1)
      wire_outputs
      local_outputs)
    as
    (SP.server_local_bridge_frame_post
      ev
      local_frame
      result
      (Ghost.reveal (server_local_old_output lio))
      (Ghost.reveal out_contentse)
      (Ghost.reveal st)
      (Ghost.reveal st1)
      (Ghost.reveal wire_outputse)
      (Ghost.reveal local_outputse));
  server_finish_local_action
    srv
    cfg
    frame
    ev
    local_frame
    result
    (server_local_old_output lio)
    out_contentse
    st
    st1
    wire_outputse
    local_outputse;
  server_finish_local_io
    srv
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

fn server_scheduled_local_output_len
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
  (ev:CTypes.server_local_event)
  (local_frame:SP.tls_server_local_bridge_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  server_endpoint_action_frame
    srv
    cfg
    frame
    (Ghost.reveal st)
    (PE.EndpointLocal ev local_frame)
returns out_len:SZ.t
ensures
  SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  server_endpoint_action_frame
    srv
    cfg
    frame
    (Ghost.reveal st)
    (PE.EndpointLocal ev local_frame)
{
  let kind = CTypes.server_local_event_kind ev;
  match kind {
    ST.LocalSendServerHello -> {
      95sz
    }
    ST.LocalSendEncryptedExtensions -> {
      28sz
    }
    ST.LocalSendCertificate -> {
      let _bound = Ghost.reveal frame.server_ep_certificate_chain_len_bound;
      assert_norm (Bounds.max_server_certificate_chain_len == 16610);
      assert (pure (SZ.v frame.server_ep_certificate_chain_len + 35 <= 20000));
      SZ.fits_lte (SZ.v frame.server_ep_certificate_chain_len + 35) 20000;
      frame.server_ep_certificate_chain_len `SZ.add` 35sz
    }
    ST.LocalSendCertificateVerify -> {
      unfold (server_endpoint_action_frame
        srv
        cfg
        frame
        (Ghost.reveal st)
        (PE.EndpointLocal ev local_frame));
      match ev {
        CTypes.ServerAPI api -> {
          unfold (SQueries.server_next_local_action_frame_post
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st)
            (CQ.NextLocal (CTypes.ServerAPI api) local_frame));
          assert (pure (SQueries.server_local_event_ready
            (Ghost.reveal st)
            (CTypes.ServerAPI api)));
          SQueries.server_local_event_ready_input_wf
            (Ghost.reveal st)
            (CTypes.ServerAPI api);
          assert (pure (api.CTypes.server_local_kind ==
            ST.LocalSendCertificateVerify));
          assert (pure (ST.server_local_event_input_ready
            (Ghost.reveal st)
            ST.LocalSendCertificateVerify
            api.CTypes.server_local_payload));
          assert (pure (Some?
            (Ghost.reveal st).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
          fold (SQueries.server_next_local_action_frame_post
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st)
            (CQ.NextLocal (CTypes.ServerAPI api) local_frame));
          fold (server_endpoint_action_frame
            srv
            cfg
            frame
            (Ghost.reveal st)
            (PE.EndpointLocal (CTypes.ServerAPI api) local_frame));
          rewrite
            (server_endpoint_action_frame
              srv
              cfg
              frame
              (Ghost.reveal st)
              (PE.EndpointLocal (CTypes.ServerAPI api) local_frame))
            as
            (server_endpoint_action_frame
              srv
              cfg
              frame
              (Ghost.reveal st)
              (PE.EndpointLocal ev local_frame));
          unfold (SP.server_invariant
            srv
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st));
          with certificate_chain credential_identity. _;
          rewrite
            (S.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st))
            as
            (CR.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st));
          let snapshot =
            ConnQ.get_certificate_verify_signature_snapshot
              srv.SP.canonical_server_state;
          rewrite
            (CR.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st))
            as
            (S.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st));
          fold (SP.server_invariant
            srv
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st));
          assert (pure (SZ.v snapshot.CR.cv_signature_len <= IM.max_signature_len));
          assert_norm (IM.max_signature_len == 4096);
          assert (pure (SZ.v snapshot.CR.cv_signature_len + 30 <= 20000));
          SZ.fits_lte (SZ.v snapshot.CR.cv_signature_len + 30) 20000;
          snapshot.CR.cv_signature_len `SZ.add` 30sz
        }
        CTypes.ServerPayload payload_kind payload -> {
          unfold (server_endpoint_payload_local_action_frame
            frame
            (Ghost.reveal st)
            payload_kind
            (Ghost.reveal payload)
            local_frame);
          assert (pure (server_endpoint_payload_frame_matches
            frame
            payload_kind
            local_frame));
          assert (pure (payload_kind == ST.LocalSendCertificateVerify));
          assert (pure False);
          unreachable ()
        }
      }
    }
    ST.LocalSendServerFinished -> {
      58sz
    }
    _ -> {
      frame.server_ep_network_out_len
    }
  }
}

fn server_run_scheduled_local_action_with_endpoint_output
      (srv:SP.canonical_server)
      (cfg:SQueries.server_next_local_action_config)
      (frame:server_endpoint_frame)
      (ch:TCP.channel)
      (ev:CTypes.server_local_event)
      (local_frame:SP.tls_server_local_bridge_frame)
      (received:Ghost.erased B.bytes)
      (sent:Ghost.erased B.bytes)
      (st:Ghost.erased CS.connection_state)
    requires
      SP.server_invariant
        srv
        (Ghost.reveal received)
        (Ghost.reveal sent)
        (Ghost.reveal st) **
      server_endpoint_action_frame
        srv
        cfg
        frame
        (Ghost.reveal st)
        (PE.EndpointLocal ev local_frame) **
      server_endpoint_io_ready
        srv
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
        SP.server_invariant
          srv
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal st1) **
        server_endpoint_frame_ready
          srv
          cfg
          frame
          (Ghost.reveal st1) **
        server_endpoint_io_ready
          srv
          ch
          frame
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal st1)
    {
      let output_len =
        server_scheduled_local_output_len
          srv
          cfg
          frame
          ev
          local_frame
          received
          sent
          st;
      unfold (server_endpoint_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
      with raw_received raw_bytes network_out_bytes. _;
      let tmp = V.alloc 0uy output_len;
      V.to_array_pts_to tmp;
      let old_oute = Ghost.hide (Seq.create (SZ.v output_len) 0uy);
      rewrite
        (pts_to (V.vec_to_array tmp) (Seq.create (SZ.v output_len) 0uy))
        as
        (pts_to (V.vec_to_array tmp) (Ghost.reveal old_oute));
      server_prepare_local_with_output
        srv
        cfg
        frame
        ev
        local_frame
        (V.vec_to_array tmp)
        output_len
        old_oute
        st;
      let result =
        SP.server_process_local
          srv
          ev
          local_frame
          (V.vec_to_array tmp)
          output_len
          received
          sent
          st
          old_oute;
      with received1 sent1 st1 out_contents wire_outputs local_outputs.
      assert (
        SP.server_invariant
          srv
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal st1) **
        SP.server_local_bridge_frame_post
          ev
          local_frame
          result
          (Ghost.reveal old_oute)
          out_contents
          (Ghost.reveal st)
          (Ghost.reveal st1)
          wire_outputs
          local_outputs **
        pts_to (V.vec_to_array tmp) out_contents);
      let out_contentse = Ghost.hide out_contents;
      let wire_outputse = Ghost.hide wire_outputs;
      let local_outputse = Ghost.hide local_outputs;
      rewrite
        (SP.server_local_bridge_frame_post
          ev
          local_frame
          result
          (Ghost.reveal old_oute)
          out_contents
          (Ghost.reveal st)
          (Ghost.reveal st1)
          wire_outputs
          local_outputs)
        as
        (SP.server_local_bridge_frame_post
          ev
          local_frame
          result
          (Ghost.reveal old_oute)
          (Ghost.reveal out_contentse)
          (Ghost.reveal st)
          (Ghost.reveal st1)
          (Ghost.reveal wire_outputse)
          (Ghost.reveal local_outputse));
      server_finish_local_action
        srv
        cfg
        frame
        ev
        local_frame
        result
        old_oute
        out_contentse
        st
        st1
        wire_outputse
        local_outputse;
      rewrite
        (pts_to (V.vec_to_array tmp) out_contents)
        as
        (pts_to (V.vec_to_array tmp) (Ghost.reveal out_contentse));
      CPI.lemma_local_process_sent_output_prefix
        (SP.server_protocol_implementation.CPI.pi_system srv)
        ev
        (Ghost.reveal old_oute)
        (Ghost.reveal out_contentse)
        output_len
        (Ghost.reveal received)
        (Ghost.reveal sent)
        (Ghost.reveal st)
        result
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1)
        (Ghost.reveal wire_outputse)
        (Ghost.reveal local_outputse);
      let nwritten = TCP.write ch (V.vec_to_array tmp) result.CPI.process_produced_len;
      assert (pure (nwritten == result.CPI.process_produced_len));
      rewrite
        (TCP.is_channel
          ch
          raw_received
          (Seq.append
            (Ghost.reveal sent)
            (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contentse)
             then Seq.slice (Ghost.reveal out_contentse) 0 (SZ.v nwritten)
             else Seq.create 0 0uy)))
        as
        (TCP.is_channel
          ch
          raw_received
          (Seq.append
            (Ghost.reveal sent)
            (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contentse)
             then Seq.slice (Ghost.reveal out_contentse) 0 (SZ.v result.CPI.process_produced_len)
             else Seq.create 0 0uy)));
      rewrite
        (TCP.is_channel
          ch
          raw_received
          (Seq.append
            (Ghost.reveal sent)
            (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contentse)
             then Seq.slice (Ghost.reveal out_contentse) 0 (SZ.v result.CPI.process_produced_len)
             else Seq.create 0 0uy)))
        as
        (TCP.is_channel ch raw_received (Ghost.reveal sent1));
      V.to_vec_pts_to tmp;
      V.free tmp;
      fold (server_endpoint_io_ready srv ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
      result
    }

    type server_endpoint_run_status =
  | ServerEndpointRunOk
  | ServerEndpointRunFailed
  | ServerEndpointRunFuelExhausted

noeq
type server_endpoint_run_result = {
  server_endpoint_run_status: server_endpoint_run_status;
  server_endpoint_run_app_len: SZ.t;
  server_endpoint_run_last_status: CPI.process_status;
}

fn server_decrement_endpoint_fuel
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

fn server_update_refs_after_network_result
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

fn server_finish_network_result_iteration
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
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
  requires SP.server_invariant
             srv
             (Ghost.reveal received)
             (Ghost.reveal sent)
             (Ghost.reveal st) **
           server_endpoint_frame_ready
             srv
             cfg
             frame
             (Ghost.reveal st) **
           server_endpoint_io_ready
             srv
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
           pure (SZ.v 'buffered_len <= SZ.v frame.server_ep_raw_len /\
                 SZ.v total_len <= SZ.v frame.server_ep_raw_len /\
                 not (Ghost.reveal 'rem = 0sz) /\
                 SZ.v (Ghost.reveal 'rem) <= SZ.v fuel)
  ensures exists* buffered_len1 running1 failed1 app_len1 last_status1 rem1.
            SP.server_invariant
              srv
              (Ghost.reveal received)
              (Ghost.reveal sent)
              (Ghost.reveal st) **
            server_endpoint_frame_ready
              srv
              cfg
              frame
              (Ghost.reveal st) **
            server_endpoint_io_ready
              srv
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
            pure (SZ.v buffered_len1 <= SZ.v frame.server_ep_raw_len /\
                  SZ.v rem1 <= SZ.v fuel)
{
  last_status := result.CPI.process_status;
  if SZ.lte result.CPI.process_consumed_len total_len {
    let _ =
      server_compact_endpoint_input
        srv
        ch
        frame
        buffered_len_ref
        total_len
        result.CPI.process_consumed_len
        received
        sent
        st;
    server_update_refs_after_network_result
      result
      stop_on_application_data
      fail_need_more_without_input
      running
      failed
      app_len;
    server_decrement_endpoint_fuel remaining fuel
  } else {
    failed := true;
    running := false;
    server_decrement_endpoint_fuel remaining fuel
  }
}

fn server_endpoint_control_tag
  (srv:SP.canonical_server)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
  requires SP.server_invariant
             srv
             (Ghost.reveal received)
             (Ghost.reveal sent)
             (Ghost.reveal st)
  returns tag:U8.t
  ensures SP.server_invariant
            srv
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st)
{
  unfold (SP.server_invariant srv (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with certificate_chain credential_identity. _;
  rewrite
    (S.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st))
    as
    (CR.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st));
  let snapshot = ConnQ.get_control_snapshot srv.SP.canonical_server_state;
  let tag = snapshot.CR.snapshot_control_tag;
  rewrite
    (CR.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st))
    as
    (S.connection_exactly srv.SP.canonical_server_state (Ghost.reveal st));
  fold (SP.server_invariant srv (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  tag
}

fn server_endpoint_run_workflow
  (srv:SP.canonical_server)
  (cfg:SQueries.server_next_local_action_config)
  (frame:server_endpoint_frame)
  (ch:TCP.channel)
  (buffered_len_ref:Box.box SZ.t)
  (stop_on_application_data:bool)
  (stop_on_application_ready:bool)
  (stop_on_closed:bool)
  (fuel:SZ.t)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
  requires SP.server_invariant
             srv
             (Ghost.reveal received)
             (Ghost.reveal sent)
             (Ghost.reveal st) **
           server_endpoint_frame_ready
             srv
             cfg
             frame
             (Ghost.reveal st) **
           server_endpoint_io_ready
             srv
             ch
             frame
             (Ghost.reveal received)
             (Ghost.reveal sent)
             (Ghost.reveal st) **
           Box.pts_to buffered_len_ref 'buffered_len **
           pure (SZ.v 'buffered_len <= SZ.v frame.server_ep_raw_len)
  returns run_result:server_endpoint_run_result
  ensures exists* (received1:Ghost.erased B.bytes)
                  (sent1:Ghost.erased B.bytes)
                  (st1:Ghost.erased CS.connection_state)
                  (buffered_len1:SZ.t).
            SP.server_invariant
              srv
              (Ghost.reveal received1)
              (Ghost.reveal sent1)
              (Ghost.reveal st1) **
            server_endpoint_frame_ready
              srv
              cfg
              frame
              (Ghost.reveal st1) **
            server_endpoint_io_ready
              srv
              ch
              frame
              (Ghost.reveal received1)
              (Ghost.reveal sent1)
              (Ghost.reveal st1) **
            Box.pts_to buffered_len_ref buffered_len1 **
            pure (SZ.v buffered_len1 <= SZ.v frame.server_ep_raw_len)
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
      SP.server_invariant
        srv
        (Ghost.reveal received_loop)
        (Ghost.reveal sent_loop)
        (Ghost.reveal st_loop) **
      server_endpoint_frame_ready
        srv
        cfg
        frame
        (Ghost.reveal st_loop) **
      server_endpoint_io_ready
        srv
        ch
        frame
        (Ghost.reveal received_loop)
        (Ghost.reveal sent_loop)
        (Ghost.reveal st_loop) **
      Box.pts_to buffered_len_ref buffered_len_loop **
      pure (SZ.v buffered_len_loop <= SZ.v frame.server_ep_raw_len /\
            SZ.v (R.read remaining) <= SZ.v fuel)
  {
    with received_loop sent_loop st_loop buffered_len_loop.
      assert (
        SP.server_invariant
          srv
          (Ghost.reveal received_loop)
          (Ghost.reveal sent_loop)
          (Ghost.reveal st_loop) **
        server_endpoint_frame_ready
          srv
          cfg
          frame
          (Ghost.reveal st_loop) **
        server_endpoint_io_ready
          srv
          ch
          frame
          (Ghost.reveal received_loop)
          (Ghost.reveal sent_loop)
          (Ghost.reveal st_loop) **
        Box.pts_to buffered_len_ref buffered_len_loop **
        pure (SZ.v buffered_len_loop <= SZ.v frame.server_ep_raw_len /\
              SZ.v (R.read remaining) <= SZ.v fuel));
    let tag = server_endpoint_control_tag srv received_loop sent_loop st_loop;
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
        server_endpoint_next_action
          srv
          cfg
          frame
          received_loop
          sent_loop
          st_loop;
      match action {
        PE.EndpointLocal ev local_frame -> {
          let result =
            server_run_scheduled_local_action_with_endpoint_output
              srv
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
              SP.server_invariant
                srv
                (Ghost.reveal received1)
                (Ghost.reveal sent1)
                (Ghost.reveal st1) **
              server_endpoint_frame_ready
                srv
                cfg
                frame
                (Ghost.reveal st1) **
              server_endpoint_io_ready
                srv
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
          if SZ.lte frame.server_ep_raw_len buffered_len {
            server_endpoint_cancel_action
              srv
              cfg
              frame
              st_loop
              (PE.EndpointNeedInput network_frame);
            failed := true;
            running := false
          } else {
            let read_len =
              if (buffered_len = 0sz) {
                server_read_more_endpoint_input
                  srv
                  ch
                  frame
                  buffered_len
                  received_loop
                  sent_loop
                  st_loop
              } else {
                0sz
              };
            assert (pure (SZ.v read_len <= SZ.v frame.server_ep_raw_len - SZ.v buffered_len));
            assert (pure (SZ.v buffered_len + SZ.v read_len <= SZ.v frame.server_ep_raw_len));
            SZ.fits_lte (SZ.v buffered_len + SZ.v read_len) (SZ.v frame.server_ep_raw_len);
            let total_len = buffered_len `SZ.add` read_len;
            let result =
              server_run_buffered_network_action
                srv
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
                SP.server_invariant
                  srv
                  (Ghost.reveal received1)
                  (Ghost.reveal sent1)
                  (Ghost.reveal st1) **
                server_endpoint_frame_ready
                  srv
                  cfg
                  frame
                  (Ghost.reveal st1) **
                server_endpoint_io_ready
                  srv
                  ch
                  frame
                  (Ghost.reveal received1)
                  (Ghost.reveal sent1)
                  (Ghost.reveal st1));
            let need_retry =
              result.CPI.process_status = CPI.NeedMoreInput &&
              read_len = 0sz &&
              SZ.lt total_len frame.server_ep_raw_len;
            if need_retry {
              let read_more =
                server_read_more_endpoint_input
                  srv
                  ch
                  frame
                  total_len
                  received1
                  sent1
                  st1;
              assert (pure (SZ.v read_more <= SZ.v frame.server_ep_raw_len - SZ.v total_len));
              assert (pure (SZ.v total_len + SZ.v read_more <= SZ.v frame.server_ep_raw_len));
              SZ.fits_lte (SZ.v total_len + SZ.v read_more) (SZ.v frame.server_ep_raw_len);
              let retry_total_len = total_len `SZ.add` read_more;
              if (read_more = 0sz) {
                failed := true;
                running := false;
                server_decrement_endpoint_fuel remaining fuel
              } else {
                let retry_action =
                  server_endpoint_next_action
                    srv
                    cfg
                    frame
                    received1
                    sent1
                    st1;
                match retry_action {
                  PE.EndpointNeedInput retry_network_frame -> {
                    let retry_result =
                      server_run_buffered_network_action
                        srv
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
                        SP.server_invariant
                          srv
                          (Ghost.reveal received2)
                          (Ghost.reveal sent2)
                          (Ghost.reveal st2) **
                        server_endpoint_frame_ready
                          srv
                          cfg
                          frame
                          (Ghost.reveal st2) **
                        server_endpoint_io_ready
                          srv
                          ch
                          frame
                          (Ghost.reveal received2)
                          (Ghost.reveal sent2)
                          (Ghost.reveal st2));
                    server_finish_network_result_iteration
                      srv
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
                    server_endpoint_cancel_action
                      srv
                      cfg
                      frame
                      st1
                      (PE.EndpointLocal retry_ev retry_local_frame);
                    failed := true;
                    running := false;
                    server_decrement_endpoint_fuel remaining fuel
                  }
                  PE.EndpointDone -> {
                    server_endpoint_cancel_action
                      srv
                      cfg
                      frame
                      st1
                      PE.EndpointDone;
                    failed := true;
                    running := false;
                    server_decrement_endpoint_fuel remaining fuel
                  }
                  PE.EndpointFailed -> {
                    server_endpoint_cancel_action
                      srv
                      cfg
                      frame
                      st1
                      PE.EndpointFailed;
                    failed := true;
                    running := false;
                    server_decrement_endpoint_fuel remaining fuel
                  }
                }
              }
            } else {
              let fail_need_more_without_input = read_len = 0sz;
              server_finish_network_result_iteration
                srv
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
          server_endpoint_cancel_action
            srv
            cfg
            frame
            st_loop
            PE.EndpointDone;
          running := false
        }
        PE.EndpointFailed -> {
          server_endpoint_cancel_action
            srv
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
      server_endpoint_run_status = ServerEndpointRunFuelExhausted;
      server_endpoint_run_app_len = produced;
      server_endpoint_run_last_status = last;
    }
  } else if did_fail {
    {
      server_endpoint_run_status = ServerEndpointRunFailed;
      server_endpoint_run_app_len = produced;
      server_endpoint_run_last_status = last;
    }
  } else {
    {
      server_endpoint_run_status = ServerEndpointRunOk;
      server_endpoint_run_app_len = produced;
      server_endpoint_run_last_status = last;
    }
  }
}

noextract
let server_protocol_endpoint
  : PE.protocol_endpoint
      SP.canonical_server
      CS.connection_state
      CW.wire_message
      CTypes.server_local_event
      CTypes.local_output
      SP.server_protocol_implementation
  =
  {
    PE.pe_config = SQueries.server_next_local_action_config;
    PE.pe_frame = server_endpoint_frame;
    PE.pe_frame_ready = server_endpoint_frame_ready;
    PE.pe_io_ready = server_endpoint_io_ready;
    PE.pe_action_frame = server_endpoint_action_frame;
    PE.pe_network_continuation = server_endpoint_network_continuation;
    PE.pe_local_continuation = server_endpoint_local_continuation;
    PE.pe_next_action = server_endpoint_next_action;
    PE.pe_cancel_action = server_endpoint_cancel_action;
    PE.pe_finish_network_action = server_finish_network_action;
    PE.pe_finish_local_action = server_finish_local_action;
    PE.pe_network_io = server_network_io;
    PE.pe_network_io_continuation = server_network_io_continuation;
    PE.pe_network_input = server_network_input;
    PE.pe_network_input_len = server_network_input_len;
    PE.pe_network_output = server_network_output;
    PE.pe_network_output_len = server_network_output_len;
    PE.pe_network_input_contents = server_network_input_contents;
    PE.pe_network_old_output = server_network_old_output;
    PE.pe_prepare_network = server_prepare_network;
    PE.pe_finish_network_io = server_finish_network_io;
    PE.pe_local_io = server_local_io;
    PE.pe_local_io_continuation = server_local_io_continuation;
    PE.pe_local_output = server_local_output;
    PE.pe_local_output_len = server_local_output_len;
    PE.pe_local_old_output = server_local_old_output;
    PE.pe_prepare_local = server_prepare_local;
    PE.pe_finish_local_io = server_finish_local_io;
  }
