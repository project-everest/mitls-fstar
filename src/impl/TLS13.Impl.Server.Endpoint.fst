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
module CQ = Common.ConnectionStateQuery
module CR = TLS13.Impl.ConnectionState.Repr
module ConnQ = TLS13.Impl.ConnectionState.Queries
module CS = TLS13.Spec.ConnectionState
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Impl.CanonicalWire
module Mat = TLS13.Impl.Server.Material
module M = TLS13.Messages
module PE = Common.ProtocolEndpoint
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
  server_ep_material_len: SZ.t;
  server_ep_material: V.vec U8.t;
  server_ep_material_spec: Ghost.erased (b:B.bytes{B.length b == 64});
  server_ep_material_bridge_proof:
    old:Ghost.erased B.bytes ->
      Ghost.erased
        (SP.server_local_bridge_obligation {
          SP.tls_server_local_payload = V.vec_to_array server_ep_material;
          SP.tls_server_local_payload_len = server_ep_material_len;
          SP.tls_server_local_app_out =
            server_ep_query.SQueries.server_query_local_app_out;
          SP.tls_server_local_app_out_len =
            server_ep_query.SQueries.server_query_local_app_out_len;
          SP.tls_server_local_old_app_out = old;
        });
  server_ep_private_len: SZ.t;
  server_ep_private: V.vec U8.t;
  server_ep_private_bridge_proof:
    old:Ghost.erased B.bytes ->
      Ghost.erased
        (SP.server_local_bridge_obligation {
          SP.tls_server_local_payload = V.vec_to_array server_ep_private;
          SP.tls_server_local_payload_len = server_ep_private_len;
          SP.tls_server_local_app_out =
            server_ep_query.SQueries.server_query_local_app_out;
          SP.tls_server_local_app_out_len =
            server_ep_query.SQueries.server_query_local_app_out_len;
          SP.tls_server_local_old_app_out = old;
        });
  server_ep_material_external_ready:
    st:Ghost.erased CS.connection_state ->
    ext:SQueries.server_external_action ->
      Ghost.erased
        (SQueries.server_external_action_ready (Ghost.reveal st) ext ==>
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
    SP.tls_server_local_bridge_proof =
      frame.server_ep_material_bridge_proof old;
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
    SP.tls_server_local_bridge_proof =
      frame.server_ep_private_bridge_proof old;
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
    CQ.NextExternal ext -> {
      match ext {
        SQueries.ServerExternalSelectServerParameters -> {
          unfold (SQueries.server_next_local_action_frame_post
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st)
            (CQ.NextExternal ext));
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
          srv.SP.canonical_server_supported_profile
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st)
            certificate_chain
            credential_identity;
          assert (pure (SP.server_supported_profile_selection
            (Ghost.reveal st)
            credential_identity));
          assert (pure (SQueries.server_external_action_ready
            (Ghost.reveal st)
            SQueries.ServerExternalSelectServerParameters));
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
        SQueries.ServerExternalDeriveSharedSecret -> {
          unfold (SQueries.server_next_local_action_frame_post
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st)
            (CQ.NextExternal ext));
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
          assert (pure (SQueries.server_external_action_ready
            (Ghost.reveal st)
            SQueries.ServerExternalDeriveSharedSecret));
          let material_ready =
            Ghost.reveal (frame.server_ep_material_external_ready
              st
              SQueries.ServerExternalDeriveSharedSecret);
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
        SQueries.ServerExternalSendServerHello -> {
          unfold (SQueries.server_next_local_action_frame_post
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st)
            (CQ.NextExternal ext));
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
          assert (pure (SQueries.server_external_action_ready
            (Ghost.reveal st)
            SQueries.ServerExternalSendServerHello));
          let material_ready =
            Ghost.reveal (frame.server_ep_material_external_ready
              st
              SQueries.ServerExternalSendServerHello);
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
        SQueries.ServerExternalSignCertificateVerify -> {
          unfold (SQueries.server_next_local_action_frame_post
            srv
            cfg
            frame.server_ep_query
            (Ghost.reveal st)
            (CQ.NextExternal ext));
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
          srv.SP.canonical_server_supported_profile
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st)
            certificate_chain
            credential_identity;
          assert (pure (SP.server_supported_profile_selection
            (Ghost.reveal st)
            credential_identity));
          assert (pure (SQueries.server_external_action_ready
            (Ghost.reveal st)
            SQueries.ServerExternalSignCertificateVerify));
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
    PE.pe_channel = TCP.channel;
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
