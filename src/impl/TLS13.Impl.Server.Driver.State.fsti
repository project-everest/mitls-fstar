module TLS13.Impl.Server.Driver.State

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module IO = Common.TCP
module IM = TLS13.Impl.Messages
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module S = TLS13.Impl.Server
module SQueries = TLS13.Impl.Server.CanonicalQueries
module EP = TLS13.Impl.Server.Endpoint
module ST = TLS13.Impl.Server.Types
module Box = Pulse.Lib.Box
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module MR = Pulse.Lib.MonotonicGhostRef
module SP = TLS13.Impl.Server.CanonicalProtocol

val driver_network_out_capacity : c:SZ.t { SZ.v c == 20000 }
val driver_app_out_capacity :
  c:SZ.t { SZ.v c == 16640 /\ IM.max_record_fragment_len <= SZ.v c }
val driver_rx_capacity : c:SZ.t { SZ.v c == 65535 }
val driver_material_capacity : c:SZ.t { SZ.v c == 64 }
val driver_certificate_verify_input_capacity :
  c:SZ.t { SZ.v c == 256 /\ Bounds.max_certificate_verify_input_len <= SZ.v c }
val driver_signature_capacity :
  c:SZ.t { SZ.v c == 4096 /\ IM.max_signature_len <= SZ.v c }

val no_channel : option IO.channel

noeq type server_driver = {
  server_driver_server: S.server;
  server_driver_credentials: O.server_credentials;
  server_driver_channel: Box.box (option IO.channel);
  server_driver_buffered_len: Box.box SZ.t;
  server_driver_empty_payload: V.vec U8.t;
  server_driver_raw: V.vec U8.t;
  server_driver_network_out: V.vec U8.t;
  server_driver_material_payload: V.vec U8.t;
  server_driver_certificate_verify_input: V.vec U8.t;
  server_driver_signature: V.vec U8.t;
  server_driver_app_out: V.vec U8.t;
  // Ghost/erased fields — zero-cost in C extraction
  server_driver_progress: MR.mref SP.server_progress_preorder;
  server_driver_initial: Ghost.erased CS.connection_state;
  server_driver_supported_profile:
    Ghost.erased
      (SP.server_supported_profile_proof (Ghost.reveal server_driver_initial));
}

noextract
let server_driver_canonical (d: server_driver) : SP.canonical_server = {
  SP.canonical_server_state = d.server_driver_server;
  SP.canonical_server_credentials = d.server_driver_credentials;
  SP.canonical_server_progress = d.server_driver_progress;
  SP.canonical_server_initial = d.server_driver_initial;
  SP.canonical_server_supported_profile = d.server_driver_supported_profile;
}

noextract
let server_driver_canonical_progress
  (d: server_driver)
  (st: CS.connection_state)
  : slprop =
  MR.pts_to d.server_driver_progress #1.0R st **
  MR.snapshot d.server_driver_progress (Ghost.reveal d.server_driver_initial)

noextract
val server_driver_endpoint_config
  (d: server_driver)
  : SQueries.server_next_local_action_config

noextract
val server_driver_endpoint_frame
  (d: server_driver)
  (network_app_out: array U8.t)
  (network_app_out_len: SZ.t)
  (local_payload: array U8.t)
  (local_payload_len: SZ.t)
  (local_app_out: array U8.t)
  (local_app_out_len: SZ.t)
  (certificate_chain_len: SZ.t)
  (certificate_chain_len_proof:
    (certificate_chain:Ghost.erased B.bytes ->
      Ghost.erased
        (SZ.v certificate_chain_len == B.length (Ghost.reveal certificate_chain))))
  (certificate_chain_len_bound:
    Ghost.erased
      (SZ.v certificate_chain_len <= Bounds.max_server_certificate_chain_len))
  (material_spec: Ghost.erased (b:B.bytes{B.length b == 64}))
  (private_key: V.vec U8.t)
  (material_deferred_ready:
    (st:Ghost.erased CS.connection_state ->
    action:SQueries.server_deferred_action ->
      Ghost.erased
        (SQueries.server_deferred_action_ready (Ghost.reveal st) action ==>
         EP.server_endpoint_material_bytes_match_state
           (Ghost.reveal material_spec)
           (Ghost.reveal st))))
  : EP.server_endpoint_frame

type server_driver_transport_status =
  | ServerDriverTransportOk
  | ServerDriverListenFailed
  | ServerDriverAcceptFailed

noextract
let logged_received_bytes_accounted
  (logged:B.bytes)
  (consumed:B.bytes)
  : prop
  =
  B.length logged <= B.length consumed /\
  (forall b. SeqP.count b logged <= SeqP.count b consumed)

noextract
let server_driver_wire_logs_match_witness
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (consumed:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : prop
  =
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent /\
  B.length buffered == SZ.v buffered_len /\
  Seq.equal (B.append consumed buffered) received /\
  logged_received_bytes_accounted st.CS.cs_wire_log.CL.raw_received consumed /\
  (ST.server_connection_control_not_failed st ==>
    Seq.equal st.CS.cs_wire_log.CL.raw_received consumed)

noextract
let server_driver_wire_logs_match
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : prop
  =
  exists consumed.
    server_driver_wire_logs_match_witness
      st
      received
      sent
      consumed
      buffered
      buffered_len

val lemma_logged_received_bytes_accounted_transport
  (st:CS.connection_state)
  (received:B.bytes)
  (consumed:B.bytes)
  (buffered:B.bytes)
  : Lemma
      (requires
        logged_received_bytes_accounted st.CS.cs_wire_log.CL.raw_received consumed /\
        Seq.equal (B.append consumed buffered) received)
      (ensures
        B.length st.CS.cs_wire_log.CL.raw_received <= B.length received /\
        (forall b.
          SeqP.count b st.CS.cs_wire_log.CL.raw_received <=
          SeqP.count b received))

val lemma_server_driver_wire_logs_match_received_accounted
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires server_driver_wire_logs_match st received sent buffered buffered_len)
      (ensures
        B.length st.CS.cs_wire_log.CL.raw_received <= B.length received /\
        (forall b.
          SeqP.count b st.CS.cs_wire_log.CL.raw_received <=
          SeqP.count b received))

val lemma_server_driver_wire_logs_match_received_exact_prefix
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        server_driver_wire_logs_match st received sent buffered buffered_len /\
        ST.server_connection_control_not_failed st)
      (ensures
        exists retained.
          Seq.equal received
            (B.append st.CS.cs_wire_log.CL.raw_received retained))

val lemma_server_driver_wire_logs_match_received_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        server_driver_wire_logs_match st received sent buffered buffered_len /\
        ST.server_connection_control_not_failed st /\
        buffered_len == 0sz)
      (ensures
        B.length received == B.length st.CS.cs_wire_log.CL.raw_received)

noextract
let server_driver_config_matches_credentials
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : prop
  =
  match st.CS.cs_model.CS.model_config.CS.config_server with
  | Some cfg ->
    cfg.CS.server_certificate_chain == certificate_chain /\
    cfg.CS.server_credential_identity == credential_identity
  | None -> False

noextract
let server_driver_selection_present_when_required
  (st:CS.connection_state)
  : prop =
  let selection = st.CS.cs_model.CS.model_handshake.CS.hs_server_selection in
  match st.CS.cs_model.CS.model_control with
  | CS.ControlHandshaking CS.HsServerHelloSent ->
    Some? selection
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent ->
    Some? selection
  | CS.ControlHandshaking CS.HsServerFinishedSent ->
    Some? selection
  | CS.ControlHandshaking CS.HsClientFinishedReceived ->
    Some? selection
  | CS.ControlApplicationData ->
    Some? selection
  | CS.ControlClosing ->
    Some? selection
  | CS.ControlClosed ->
    Some? selection
  | _ ->
    True

noextract
let server_driver_supported_profile_selection
  (st:CS.connection_state)
  (credential_identity:CS.server_credential_identity)
  : prop =
  CS.signature_scheme_offered
    st.CS.cs_model.CS.model_config.CS.config_signature_schemes
    T.RsaPssRsaeSha256 /\
  server_driver_selection_present_when_required st /\
  (match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
   | Some selection ->
     selection.CS.server_selected_signature_scheme == T.RsaPssRsaeSha256 /\
     selection.CS.server_selected_credential == credential_identity
   | None ->
     True)

noextract
let server_driver_buffers
  (d:server_driver)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : slprop
  =
  Box.pts_to d.server_driver_buffered_len buffered_len **
  exists* empty_payload raw network_out material cv_input signature app_out.
    V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
    V.pts_to d.server_driver_raw #1.0R raw **
    V.pts_to d.server_driver_network_out #1.0R network_out **
    V.pts_to d.server_driver_material_payload #1.0R material **
    V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
    V.pts_to d.server_driver_signature #1.0R signature **
    V.pts_to d.server_driver_app_out #1.0R app_out **
    pure (
      B.length empty_payload == 0 /\
      B.length raw == SZ.v driver_rx_capacity /\
      B.length buffered == SZ.v buffered_len /\
      SZ.v buffered_len <= SZ.v driver_rx_capacity /\
      Seq.equal buffered (Seq.slice raw 0 (SZ.v buffered_len)) /\
      B.length network_out == SZ.v driver_network_out_capacity /\
      B.length material == SZ.v driver_material_capacity /\
      B.length cv_input == SZ.v driver_certificate_verify_input_capacity /\
      B.length signature == SZ.v driver_signature_capacity /\
      B.length app_out == SZ.v driver_app_out_capacity /\
      Bounds.max_certificate_verify_input_len <=
        SZ.v driver_certificate_verify_input_capacity /\
      IM.max_signature_len <= SZ.v driver_signature_capacity /\
      IM.max_record_fragment_len <= SZ.v driver_app_out_capacity /\
      V.is_full_vec d.server_driver_empty_payload /\
      V.is_full_vec d.server_driver_raw /\
      V.is_full_vec d.server_driver_network_out /\
      V.is_full_vec d.server_driver_material_payload /\
      V.is_full_vec d.server_driver_certificate_verify_input /\
      V.is_full_vec d.server_driver_signature /\
      V.is_full_vec d.server_driver_app_out)

noextract
let server_driver_buffers_with_app_out
  (d:server_driver)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  (app_out:B.bytes)
  : slprop
  =
  Box.pts_to d.server_driver_buffered_len buffered_len **
  exists* empty_payload raw network_out material cv_input signature.
    V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
    V.pts_to d.server_driver_raw #1.0R raw **
    V.pts_to d.server_driver_network_out #1.0R network_out **
    V.pts_to d.server_driver_material_payload #1.0R material **
    V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
    V.pts_to d.server_driver_signature #1.0R signature **
    V.pts_to d.server_driver_app_out #1.0R app_out **
    pure (
      B.length empty_payload == 0 /\
      B.length raw == SZ.v driver_rx_capacity /\
      B.length buffered == SZ.v buffered_len /\
      SZ.v buffered_len <= SZ.v driver_rx_capacity /\
      Seq.equal buffered (Seq.slice raw 0 (SZ.v buffered_len)) /\
      B.length network_out == SZ.v driver_network_out_capacity /\
      B.length material == SZ.v driver_material_capacity /\
      B.length cv_input == SZ.v driver_certificate_verify_input_capacity /\
      B.length signature == SZ.v driver_signature_capacity /\
      B.length app_out == SZ.v driver_app_out_capacity /\
      Bounds.max_certificate_verify_input_len <=
        SZ.v driver_certificate_verify_input_capacity /\
      IM.max_signature_len <= SZ.v driver_signature_capacity /\
      IM.max_record_fragment_len <= SZ.v driver_app_out_capacity /\
      V.is_full_vec d.server_driver_empty_payload /\
      V.is_full_vec d.server_driver_raw /\
      V.is_full_vec d.server_driver_network_out /\
      V.is_full_vec d.server_driver_material_payload /\
      V.is_full_vec d.server_driver_certificate_verify_input /\
      V.is_full_vec d.server_driver_signature /\
      V.is_full_vec d.server_driver_app_out)

noextract
let server_driver_live
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop
  =
  S.connection_exactly d.server_driver_server st **
  O.is_server_credentials
    d.server_driver_credentials
    certificate_chain
    credential_identity **
  Box.pts_to d.server_driver_channel no_channel **
  server_driver_buffers d B.empty 0sz **
  pure (ST.server_end_to_end_invariant st /\
        server_driver_config_matches_credentials
          st
          certificate_chain
          credential_identity /\
        server_driver_supported_profile_selection st credential_identity /\
        server_driver_wire_logs_match st B.empty B.empty B.empty 0sz)

noextract
let server_driver_connected
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  (received:B.bytes)
  (sent:B.bytes)
  : slprop
  =
  S.connection_exactly d.server_driver_server st **
  O.is_server_credentials
    d.server_driver_credentials
    certificate_chain
    credential_identity **
  exists* ch buffered buffered_len.
    Box.pts_to d.server_driver_channel (Some ch) **
    IO.is_channel ch received sent **
    server_driver_buffers d buffered buffered_len **
    pure (ST.server_end_to_end_invariant st /\
          server_driver_config_matches_credentials
            st
            certificate_chain
            credential_identity /\
          server_driver_supported_profile_selection st credential_identity /\
          server_driver_wire_logs_match st received sent buffered buffered_len)

noextract
(**
  Endpoint-owned connected server state.

  The endpoint frame owns the resources consumed by [Server.Endpoint], including
  the canonical progress/current-state resource.  It is separate from the legacy
  public predicate while the driver workflows are still routed through the direct
  low-level path.  The server endpoint requires a distinct private-key vec, so
  callers provide that through [frame] instead of treating the 64-byte material
  vec as a splittable subview.
**)
let server_driver_endpoint_connected
  (d:server_driver)
  (cfg:SQueries.server_next_local_action_config)
  (frame:EP.server_endpoint_frame)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  (canonical_received:B.bytes)
  (canonical_sent:B.bytes)
  (transport_received:B.bytes)
  (transport_sent:B.bytes)
  : slprop
  =
  SP.server_invariant
    (server_driver_canonical d)
    canonical_received
    canonical_sent
    st **
  O.is_server_credentials
    d.server_driver_credentials
    certificate_chain
    credential_identity **
  exists* ch buffered_len.
    Box.pts_to d.server_driver_channel (Some ch) **
    Box.pts_to d.server_driver_buffered_len buffered_len **
    EP.server_endpoint_frame_ready
      (server_driver_canonical d)
      cfg
      frame
      st **
    EP.server_endpoint_io_ready
      (server_driver_canonical d)
      ch
      frame
      transport_received
      transport_sent
      st **
    pure (ST.server_end_to_end_invariant st /\
          server_driver_config_matches_credentials
            st
            certificate_chain
            credential_identity /\
          server_driver_supported_profile_selection st credential_identity /\
          (exists buffered.
            server_driver_wire_logs_match
              st
              transport_received
              transport_sent
              buffered
              buffered_len) /\
          Seq.equal canonical_sent transport_sent)

noextract
let server_driver_connected_with_app_out
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  (received:B.bytes)
  (sent:B.bytes)
  (app_out:B.bytes)
  : slprop
  =
  S.connection_exactly d.server_driver_server st **
  O.is_server_credentials
    d.server_driver_credentials
    certificate_chain
    credential_identity **
  exists* ch buffered buffered_len.
    Box.pts_to d.server_driver_channel (Some ch) **
    IO.is_channel ch received sent **
    server_driver_buffers_with_app_out d buffered buffered_len app_out **
    pure (ST.server_end_to_end_invariant st /\
          server_driver_config_matches_credentials
           st
           certificate_chain
           credential_identity /\
          server_driver_supported_profile_selection st credential_identity /\
          server_driver_wire_logs_match st received sent buffered buffered_len)

fn forget_server_driver_connected_app_out
  (d:server_driver)
  requires server_driver_connected_with_app_out
           d
           'st
           'certificate_chain
           'credential_identity
           'received
           'sent
           'app_out
  ensures server_driver_connected
           d
           'st
           'certificate_chain
           'credential_identity
           'received
           'sent

fn expose_server_driver_connected_app_out
  (d:server_driver)
  requires server_driver_connected
           d
           'st
           'certificate_chain
           'credential_identity
           'received
           'sent
  ensures exists* app_out.
           server_driver_connected_with_app_out
             d
             'st
             'certificate_chain
             'credential_identity
             'received
             'sent
             app_out

noextract
let server_driver_closed
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop
  =
  S.connection_exactly d.server_driver_server st **
  O.is_server_credentials
    d.server_driver_credentials
    certificate_chain
    credential_identity **
  Box.pts_to d.server_driver_channel no_channel **
  exists* buffered buffered_len.
    server_driver_buffers d buffered buffered_len **
    pure (ST.server_end_to_end_invariant st)

val lemma_legal_response_network_out_len
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires ST.legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out)
      (ensures
        SZ.v resp.ST.network_out_len <= B.length network_out /\
        B.length (ST.response_network_out resp network_out) ==
          SZ.v resp.ST.network_out_len)

val lemma_legal_response_for_event_wire_lengths
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires ST.legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out)
      (ensures
        B.length st1.CS.cs_wire_log.CL.raw_sent ==
          B.length st0.CS.cs_wire_log.CL.raw_sent + B.length raw_sent /\
        B.length st1.CS.cs_wire_log.CL.raw_received ==
          B.length st0.CS.cs_wire_log.CL.raw_received + B.length raw_received /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_sent
          (B.append st0.CS.cs_wire_log.CL.raw_sent raw_sent) /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_received
          (B.append st0.CS.cs_wire_log.CL.raw_received raw_received))

val lemma_local_event_wire_lengths
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires ST.server_local_event_end_to_end_correct
        st0 st1 resp kind payload network_out app_out)
      (ensures
        B.length st1.CS.cs_wire_log.CL.raw_sent ==
          B.length st0.CS.cs_wire_log.CL.raw_sent + SZ.v resp.ST.network_out_len /\
        B.length st1.CS.cs_wire_log.CL.raw_received ==
          B.length st0.CS.cs_wire_log.CL.raw_received /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_sent
          (B.append
            st0.CS.cs_wire_log.CL.raw_sent
            (ST.response_network_out resp network_out)) /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_received
          st0.CS.cs_wire_log.CL.raw_received /\
        SZ.v resp.ST.network_out_len <= B.length network_out)

val lemma_server_local_event_received_exact_when_nonfailed
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  (received:B.bytes)
  (sent:B.bytes)
  (consumed:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        ST.server_local_event_end_to_end_correct
          st0 st1 resp kind payload network_out app_out /\
        server_driver_wire_logs_match_witness
          st0 received sent consumed buffered buffered_len)
      (ensures
        ST.server_connection_control_not_failed st1 ==>
          Seq.equal st1.CS.cs_wire_log.CL.raw_received consumed)

val lemma_logged_received_bytes_accounted_append_delta
  (old_logged:B.bytes)
  (old_consumed:B.bytes)
  (raw_delta:B.bytes)
  (consumed_delta:B.bytes)
  : Lemma
      (requires
        logged_received_bytes_accounted old_logged old_consumed /\
        (Seq.equal raw_delta B.empty \/ Seq.equal raw_delta consumed_delta))
      (ensures
        logged_received_bytes_accounted
          (B.append old_logged raw_delta)
          (B.append old_consumed consumed_delta))
