module TLS13.Impl.Server.CanonicalProtocol

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CPI = Common.ProtocolImplementation
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module CW = TLS13.Impl.CanonicalWire
module CTypes = TLS13.Impl.CanonicalTypes
module ID = FStar.IndefiniteDescription
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module O = TLS13.OpenSSL
module RVD = TLS13.Wire.Spec.RevealDecode
module RTC = FStar.ReflexiveTransitiveClosure
module S = TLS13.Impl.Server
module Seq = FStar.Seq
module SM = Common.StateMachine
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module TCP = Common.TCP
module T = TLS13.Types
module U8 = FStar.UInt8
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module WS = TLS13.Wire.Spec

(**
  Canonical Common.ProtocolImplementation boundary for the low-level server.

  Credential-dependent local APIs ([process_local_event_with_credentials] and
  the certificate/certificate-verify helpers) are deliberately outside this
  first plain boundary.
 **)

let server_local_outputs_match
  (ev:CS.conn_event)
  (outs:list CTypes.local_output)
  : prop =
  Seq.equal
    (CTypes.local_outputs_app_bytes outs)
    (CL.concat_bytes (CS.conn_event_app_received_delta ev))

let server_wire_outputs_match
  (raw_sent:B.bytes)
  (outs:list CW.wire_message)
  : prop =
  Seq.equal
    (WF.serialize_all CW.tls_record_wire_format outs)
    raw_sent

let server_api_event_matches
  (api:CTypes.server_api_event)
  (ev:CS.conn_event)
  : prop =
  ST.local_event_kind_matches
    api.CTypes.server_local_kind
    api.CTypes.server_local_payload
    ev

let server_step
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message CTypes.local_output)
  : GTot prop =
  match ev with
  | SM.WireEvent wire ->
    exists msg.
      let conn_ev =
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = msg;
        } in
      CS.legal_connection_delta
        st0
        {
          CS.delta_event = conn_ev;
          CS.delta_raw_sent =
            WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
          CS.delta_raw_received = CW.wire_serialize wire;
        }
        st1 /\
      CS.sent_event_nonempty_seal_projection
        st0.CS.cs_model
        conn_ev
        (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
      CS.received_event_nonempty_decode_projection
        st0.CS.cs_model
        conn_ev
        (CW.wire_serialize wire) /\
      server_local_outputs_match conn_ev out.SM.so_local_outputs
  | SM.LocalEvent local ->
    let api = CTypes.server_local_event_api local in
      exists conn_ev raw_sent.
        server_api_event_matches api conn_ev /\
        server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
        server_local_outputs_match conn_ev out.SM.so_local_outputs /\
        CS.legal_connection_delta
          st0
          {
           CS.delta_event = conn_ev;
           CS.delta_raw_sent = raw_sent;
           CS.delta_raw_received = B.empty;
          }
           st1 /\
        CS.sent_event_nonempty_seal_projection
          st0.CS.cs_model
          conn_ev
          raw_sent /\
        CS.received_event_nonempty_decode_projection
          st0.CS.cs_model
          conn_ev
          B.empty

noextract
let server_state_machine
  (initial:CS.connection_state)
  : SM.state_machine
      CS.connection_state
      CW.wire_message
      CTypes.server_local_event
      CTypes.local_output
  =
  {
    SM.sm_initial_state = initial;
    SM.sm_step = server_step;
  }

noextract
let server_system
  (initial:CS.connection_state)
  : WFSM.wire_format_state_machine
      CS.connection_state
      CW.wire_message
      CTypes.server_local_event
      CTypes.local_output
  =
  {
    WFSM.wfsm_state_machine = server_state_machine initial;
    WFSM.wfsm_wire_format = CW.tls_record_wire_format;
  }

let server_canonical_step_rel
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : prop =
  exists ev out. server_step st0 ev st1 out

let server_progress_preorder =
  RTC.closure server_canonical_step_rel

let server_invariant_pure
  (initial:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  : prop =
  ST.server_end_to_end_invariant st /\
  st.CS.cs_model.CS.model_config == initial.CS.cs_model.CS.model_config /\
  Seq.equal received st.CS.cs_wire_log.CL.raw_received /\
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent /\
  Seq.equal initial.CS.cs_wire_log.CL.raw_received B.empty /\
  Seq.equal initial.CS.cs_wire_log.CL.raw_sent B.empty

let server_config_matches_credentials
  (initial:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : prop =
  match initial.CS.cs_model.CS.model_config.CS.config_server with
  | Some cfg ->
    cfg.CS.server_certificate_chain == certificate_chain /\
    cfg.CS.server_credential_identity == credential_identity
  | None -> False

let server_selection_present_when_required
  (st:CS.connection_state)
  : prop =
  let selection = st.CS.cs_model.CS.model_handshake.CS.hs_server_selection in
  match st.CS.cs_model.CS.model_control with
  | CS.ControlHandshaking CS.HsServerHelloSent
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent
  | CS.ControlHandshaking CS.HsServerFinishedSent
  | CS.ControlHandshaking CS.HsClientFinishedReceived
  | CS.ControlApplicationData
  | CS.ControlClosing
  | CS.ControlClosed ->
    Some? selection
  | _ ->
    True

let server_supported_profile_selection
  (st:CS.connection_state)
  (credential_identity:CS.server_credential_identity)
  : prop =
  CS.signature_scheme_offered
    st.CS.cs_model.CS.model_config.CS.config_signature_schemes
    T.RsaPssRsaeSha256 /\
  (match st.CS.cs_model.CS.model_config.CS.config_server with
   | Some cfg ->
     CS.cipher_suite_offered
       cfg.CS.server_supported_cipher_suites
       T.TLS_CHACHA20_POLY1305_SHA256 /\
     CS.named_group_offered
       cfg.CS.server_supported_groups
       T.X25519 /\
     CS.signature_scheme_offered
       cfg.CS.server_allowed_signature_schemes
       T.RsaPssRsaeSha256 /\
     (match st.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
      | Some ch ->
        CS.sni_policy_accepts cfg.CS.server_sni_policy ch.M.server_name
      | None ->
        True)
   | None ->
     False) /\
  server_selection_present_when_required st /\
  (match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
   | Some selection ->
     selection.CS.server_selected_signature_scheme == T.RsaPssRsaeSha256 /\
     selection.CS.server_selected_credential == credential_identity
   | None ->
     True)

type server_supported_profile_proof
  (initial:CS.connection_state)
  =
  received:B.bytes ->
  sent:B.bytes ->
  st:CS.connection_state ->
  certificate_chain:B.bytes ->
  credential_identity:CS.server_credential_identity ->
    Lemma
      (requires
        server_invariant_pure
          initial
          received
          sent
          st /\
        server_config_matches_credentials
          initial
          certificate_chain
          credential_identity)
      (ensures
        server_supported_profile_selection st credential_identity)

type server_supported_profile_provider =
  initial:CS.connection_state -> server_supported_profile_proof initial

noeq
type canonical_server = {
  canonical_server_state: S.server;
  canonical_server_credentials: O.server_credentials;
  canonical_server_progress: MR.mref server_progress_preorder;
  canonical_server_initial: Ghost.erased CS.connection_state;
  canonical_server_supported_profile:
    Ghost.erased
      (server_supported_profile_proof (Ghost.reveal canonical_server_initial));
}

noeq
type tls_server_network_frame = {
  tls_server_network_app_out: array U8.t;
  tls_server_network_app_out_len: SZ.t;
  tls_server_network_old_app_out: Ghost.erased B.bytes;
}

noeq
type tls_server_local_frame = {
  tls_server_local_payload: array U8.t;
  tls_server_local_payload_len: SZ.t;
  tls_server_local_app_out: array U8.t;
  tls_server_local_app_out_len: SZ.t;
  tls_server_local_old_app_out: Ghost.erased B.bytes;
}

let server_response_wire_outputs
  (resp:ST.server_response)
  (network_out:B.bytes)
  : GTot (list CW.wire_message) =
  CW.wire_outputs_of_full_record (ST.response_network_out resp network_out)

let server_response_local_outputs
  (resp:ST.server_response)
  (app_out:B.bytes)
  : GTot (list CTypes.local_output) =
  CTypes.local_outputs_of_app_bytes (ST.response_app_out resp app_out)

let lemma_server_response_local_outputs_match
  (resp:ST.server_response)
  (ev:CS.conn_event)
  (app_out:B.bytes)
  : Lemma
      (requires ST.response_app_out_matches_event resp ev app_out)
      (ensures
        server_local_outputs_match
          ev
          (server_response_local_outputs resp app_out))
=
  let app_bytes = ST.response_app_out resp app_out in
  CTypes.lemma_local_outputs_of_app_bytes_exact app_bytes;
  Seq.lemma_eq_elim
    app_bytes
    (ST.event_api_app_out ev)

let lemma_server_consumed_prefix_parse
  (input:B.bytes)
  (buffer_resp:ST.server_buffer_response)
  : Lemma
      (requires
        SZ.v buffer_resp.ST.consumed_len <= B.length input /\
        CT.raw_record_parse_success
          (ST.server_network_consumed_prefix buffer_resp input))
      (ensures
        exists msg residual.
          CPI.consumed_by_parse
            CW.tls_record_wire_format
            input
            msg
            (ST.server_network_consumed_prefix buffer_resp input)
            residual /\
          Seq.equal
            (CW.wire_serialize msg)
            (ST.server_network_consumed_prefix buffer_resp input))
=
  let consumed = ST.server_network_consumed_prefix buffer_resp input in
  assert (consumed == Seq.slice input 0 (SZ.v buffer_resp.ST.consumed_len));
  assert (exists outer_ct outer_fragment.
    WS.parse_record_wire consumed ==
      Some (outer_ct, outer_fragment, B.length consumed));
  let outer_ct =
    ID.indefinite_description_ghost
      T.content_type
      (fun outer_ct -> exists outer_fragment.
        WS.parse_record_wire consumed ==
          Some (outer_ct, outer_fragment, B.length consumed)) in
  let outer_fragment =
    ID.indefinite_description_ghost
      M.sealed_record
      (fun outer_fragment ->
        WS.parse_record_wire consumed ==
          Some (outer_ct, outer_fragment, B.length consumed)) in
  Seq.lemma_len_slice input 0 (SZ.v buffer_resp.ST.consumed_len);
  assert (B.length consumed == SZ.v buffer_resp.ST.consumed_len);
  RVD.lemma_parse_record_wire_from_prefix
    input
    outer_ct
    outer_fragment
    (SZ.v buffer_resp.ST.consumed_len);
  let residual = Seq.slice input (SZ.v buffer_resp.ST.consumed_len) (B.length input) in
  Seq.lemma_split input (SZ.v buffer_resp.ST.consumed_len);
  match CW.wire_parse input with
  | Some (msg, parsed_residual) ->
    assert (Seq.equal parsed_residual residual);
    assert (msg == msg);
    assert (Seq.equal input (Seq.append consumed residual));
    assert (CPI.consumed_by_parse
      CW.tls_record_wire_format
      input
      msg
      consumed
      residual);
    assert (Seq.equal (CW.wire_serialize msg) consumed);
    assert (exists msg' residual'.
      CPI.consumed_by_parse
        CW.tls_record_wire_format
        input
        msg'
        consumed
        residual' /\
      Seq.equal (CW.wire_serialize msg') consumed)
  | None ->
    assert False

let lemma_received_tls_raw_delta_legal_raw_record_parse_success
  (st0:CS.connection_state)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  : Lemma
      (requires CT.received_tls_raw_delta_legal st0 msg raw_received)
      (ensures CT.raw_record_parse_success raw_received)
=
  let received_msg = {
    CL.message_direction = CL.Received;
    CL.message_value = msg;
  } in
  assert (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent received_msg)
    B.empty
    raw_received);
  assert (CS.network_message_raw_delta_legal
    st0.CS.cs_model
    received_msg
    raw_received);
  if CS.network_message_is_cleartext CL.Received msg then (
    match msg with
    | M.TlsHandshake (M.ClientHello _) ->
      assert (CS.received_cleartext_tls_message_raw msg raw_received);
      assert (exists fragment.
        WS.parse_record_wire raw_received ==
          Some (T.Handshake, fragment, B.length raw_received) /\
        WS.parse_tls_message T.Handshake fragment == Some msg);
      let fragment =
        ID.indefinite_description_ghost
          B.bytes
          (fun fragment ->
            WS.parse_record_wire raw_received ==
              Some (T.Handshake, fragment, B.length raw_received) /\
            WS.parse_tls_message T.Handshake fragment == Some msg) in
      assert (exists outer_ct outer_fragment.
        WS.parse_record_wire raw_received ==
          Some (outer_ct, outer_fragment, B.length raw_received))
    | M.TlsHandshake M.HelloRetryRequest ->
      assert (CS.cleartext_tls_message_raw msg raw_received);
      assert (CS.raw_records_exactly raw_received T.Handshake 1);
      CSL.lemma_raw_records_exactly_one_parse_record raw_received T.Handshake;
      assert (exists fragment.
        WS.parse_record raw_received == Some (T.Handshake, fragment, B.length raw_received));
      let fragment =
        ID.indefinite_description_ghost
          B.bytes
          (fun fragment ->
            WS.parse_record raw_received == Some (T.Handshake, fragment, B.length raw_received)) in
      WS.lemma_parse_record_implies_parse_record_wire raw_received;
      assert (WS.parse_record_wire raw_received ==
        Some (T.Handshake, fragment, B.length raw_received));
      assert (exists outer_ct outer_fragment.
        WS.parse_record_wire raw_received ==
          Some (outer_ct, outer_fragment, B.length raw_received))
    | M.TlsHandshake (M.ServerHello sh) ->
      assert (CS.cleartext_tls_message_raw msg raw_received);
      let (outer_ct, outer_fragment) = WS.serialize_tls_message msg in
      assert (Seq.equal
        raw_received
        (WS.serialize_record outer_ct outer_fragment));
      WS.lemma_serialize_tls_message_handshake (M.ServerHello sh);
      assert (outer_ct == T.Handshake);
      assert (outer_fragment == WS.serialize_handshake (M.ServerHello sh));
      WS.lemma_serialize_server_hello_len sh;
      assert (M.server_hello_max_len <= 16640);
      assert (B.length outer_fragment <= 16640);
      WS.lemma_parse_record_serialize_record outer_ct outer_fragment;
      WS.lemma_parse_record_implies_parse_record_wire
        (WS.serialize_record outer_ct outer_fragment);
      Seq.lemma_eq_elim
        raw_received
        (WS.serialize_record outer_ct outer_fragment);
      assert (WS.parse_record_wire raw_received ==
        Some (outer_ct, outer_fragment, B.length raw_received));
      assert (exists outer_ct' outer_fragment'.
        WS.parse_record_wire raw_received ==
          Some (outer_ct', outer_fragment', B.length raw_received))
    | M.TlsChangeCipherSpec ->
      assert (CS.cleartext_tls_message_raw msg raw_received);
      let outer_ct = T.ChangeCipherSpec in
      let outer_fragment = B.singleton 1uy in
      WS.lemma_serialize_tls_message_change_cipher_spec ();
      assert (Seq.equal
        raw_received
        (WS.serialize_record outer_ct outer_fragment));
      assert_norm (B.length (B.singleton 1uy) == 1);
      assert (B.length outer_fragment <= 16640);
      WS.lemma_parse_record_serialize_record outer_ct outer_fragment;
      WS.lemma_parse_record_implies_parse_record_wire
        (WS.serialize_record outer_ct outer_fragment);
      Seq.lemma_eq_elim
        raw_received
        (WS.serialize_record outer_ct outer_fragment);
      assert (WS.parse_record_wire raw_received ==
        Some (outer_ct, outer_fragment, B.length raw_received));
      assert (exists outer_ct' outer_fragment'.
        WS.parse_record_wire raw_received ==
          Some (outer_ct', outer_fragment', B.length raw_received))
    | _ ->
      assert False
  ) else (
    assert (CS.raw_records_exactly
      raw_received
      T.ApplicationData
      (CS.protected_record_count CL.Received msg));
    assert (CS.protected_record_count CL.Received msg == 1);
    CSL.lemma_raw_records_exactly_one_parse_record raw_received T.ApplicationData;
    assert (exists fragment.
      WS.parse_record raw_received == Some (T.ApplicationData, fragment, B.length raw_received));
    let fragment =
      ID.indefinite_description_ghost
        B.bytes
        (fun fragment ->
          WS.parse_record raw_received == Some (T.ApplicationData, fragment, B.length raw_received)) in
    WS.lemma_parse_record_implies_parse_record_wire raw_received;
    assert (WS.parse_record_wire raw_received ==
      Some (T.ApplicationData, fragment, B.length raw_received));
    assert (exists outer_ct outer_fragment.
      WS.parse_record_wire raw_received ==
        Some (outer_ct, outer_fragment, B.length raw_received))
  )

let lemma_server_network_step_ok_legal_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:ST.server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        ST.server_network_consumed_input_projection
          st0
          st1
          buffer_resp
          input
          network_out
          app_out /\
        buffer_resp.ST.response.ST.status == ST.StepOk)
      (ensures
        exists msg.
          ST.legal_network_response
            st0
            st1
            buffer_resp.ST.response
            msg
            (ST.server_network_consumed_prefix buffer_resp input)
            network_out
            app_out)
=
  assert (ST.server_network_step_ok_received_decode_projection
    st0
    st1
    buffer_resp
    input
    network_out
    app_out);
  assert (exists msg.
    CT.received_tls_raw_delta_legal
      st0
      msg
      (ST.server_network_consumed_prefix buffer_resp input) /\
    ST.server_decoded_message_event_projection
      st0
      st1
      buffer_resp.ST.response
      msg
      (ST.server_network_consumed_prefix buffer_resp input)
      network_out
      app_out /\
    (if CS.network_message_is_cleartext CL.Received msg
     then True
     else
       ST.server_protected_record_decode_correct
         st0
         (ST.server_network_consumed_prefix buffer_resp input)
         msg));
  let msg =
    ID.indefinite_description_ghost
      M.tls_message
      (fun msg ->
        CT.received_tls_raw_delta_legal
          st0
          msg
          (ST.server_network_consumed_prefix buffer_resp input) /\
        ST.server_decoded_message_event_projection
          st0
          st1
          buffer_resp.ST.response
          msg
          (ST.server_network_consumed_prefix buffer_resp input)
          network_out
          app_out /\
        (if CS.network_message_is_cleartext CL.Received msg
         then True
         else
           ST.server_protected_record_decode_correct
             st0
             (ST.server_network_consumed_prefix buffer_resp input)
             msg)) in
  assert (ST.server_decoded_message_event_projection
    st0
    st1
    buffer_resp.ST.response
    msg
    (ST.server_network_consumed_prefix buffer_resp input)
    network_out
    app_out);
  if ST.legal_network_response
    st0
    st1
    buffer_resp.ST.response
    msg
    (ST.server_network_consumed_prefix buffer_resp input)
    network_out
    app_out
  then (
    assert (exists msg'.
      ST.legal_network_response
        st0
        st1
        buffer_resp.ST.response
        msg'
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out)
  ) else (
    assert (ST.unexpected_message_response
      st0
      st1
      buffer_resp.ST.response
      network_out
      app_out);
    assert (buffer_resp.ST.response.ST.status == ST.IllegalTransition);
    assert False
  )

let lemma_server_network_step_ok_received_decode_legal_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:ST.server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        ST.server_network_consumed_input_projection
          st0
          st1
          buffer_resp
          input
          network_out
          app_out /\
        buffer_resp.ST.response.ST.status == ST.StepOk)
      (ensures
        exists msg.
          CT.received_tls_raw_delta_legal
            st0
            msg
            (ST.server_network_consumed_prefix buffer_resp input) /\
          ST.legal_network_response
            st0
            st1
            buffer_resp.ST.response
            msg
            (ST.server_network_consumed_prefix buffer_resp input)
            network_out
            app_out /\
          (if CS.network_message_is_cleartext CL.Received msg
           then True
           else
             ST.server_protected_record_decode_correct
               st0
               (ST.server_network_consumed_prefix buffer_resp input)
               msg))
=
  assert (ST.server_network_step_ok_received_decode_projection
    st0
    st1
    buffer_resp
    input
    network_out
    app_out);
  assert (exists msg.
    CT.received_tls_raw_delta_legal
      st0
      msg
      (ST.server_network_consumed_prefix buffer_resp input) /\
    ST.server_decoded_message_event_projection
      st0
      st1
      buffer_resp.ST.response
      msg
      (ST.server_network_consumed_prefix buffer_resp input)
      network_out
      app_out /\
    (if CS.network_message_is_cleartext CL.Received msg
     then True
     else
       ST.server_protected_record_decode_correct
         st0
         (ST.server_network_consumed_prefix buffer_resp input)
         msg));
  let msg =
    ID.indefinite_description_ghost
      M.tls_message
      (fun msg ->
        CT.received_tls_raw_delta_legal
          st0
          msg
          (ST.server_network_consumed_prefix buffer_resp input) /\
        ST.server_decoded_message_event_projection
          st0
          st1
          buffer_resp.ST.response
          msg
          (ST.server_network_consumed_prefix buffer_resp input)
          network_out
          app_out /\
        (if CS.network_message_is_cleartext CL.Received msg
         then True
         else
           ST.server_protected_record_decode_correct
             st0
             (ST.server_network_consumed_prefix buffer_resp input)
             msg)) in
  assert (ST.server_decoded_message_event_projection
    st0
    st1
    buffer_resp.ST.response
    msg
    (ST.server_network_consumed_prefix buffer_resp input)
    network_out
    app_out);
  if ST.legal_network_response
    st0
    st1
    buffer_resp.ST.response
    msg
    (ST.server_network_consumed_prefix buffer_resp input)
    network_out
    app_out
  then (
    assert (exists msg'.
      CT.received_tls_raw_delta_legal
        st0
        msg'
        (ST.server_network_consumed_prefix buffer_resp input) /\
      ST.legal_network_response
        st0
        st1
        buffer_resp.ST.response
        msg'
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out /\
      (if CS.network_message_is_cleartext CL.Received msg'
       then True
       else
         ST.server_protected_record_decode_correct
           st0
           (ST.server_network_consumed_prefix buffer_resp input)
           msg'))
  ) else (
    assert (ST.unexpected_message_response
      st0
      st1
      buffer_resp.ST.response
      network_out
      app_out);
    assert (buffer_resp.ST.response.ST.status == ST.IllegalTransition);
    assert False
  )

let lemma_server_network_step_ok_process_correct
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:ST.server_buffer_response)
  (input:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (app_out:B.bytes)
  (received0:B.bytes)
  (sent0:B.bytes)
  : Lemma
      (requires
        CPI.buffers_wf input input_len old_network_out out_len /\
        B.length input == SZ.v input_len /\
        B.length network_out == B.length old_network_out /\
        Seq.equal received0 st0.CS.cs_wire_log.CL.raw_received /\
        Seq.equal sent0 st0.CS.cs_wire_log.CL.raw_sent /\
        ST.server_network_bytes_end_to_end_correct
          st0
          st1
          buffer_resp
          input
          network_out
          app_out /\
        ST.server_network_consumed_input_projection
          st0
          st1
          buffer_resp
          input
          network_out
          app_out /\
        buffer_resp.ST.response.ST.status == ST.StepOk)
      (ensures
        CPI.network_process_correct
          (server_system initial)
          input
          input_len
          old_network_out
          network_out
          out_len
          received0
          sent0
          st0
          (CTypes.server_process_result buffer_resp)
          st1.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_sent
          st1
          (ST.server_network_consumed_prefix buffer_resp input)
          (server_response_wire_outputs buffer_resp.ST.response network_out)
          (server_response_local_outputs buffer_resp.ST.response app_out))
=
  let resp = buffer_resp.ST.response in
  let consumed = ST.server_network_consumed_prefix buffer_resp input in
  let wire_outputs = server_response_wire_outputs resp network_out in
  let local_outputs = server_response_local_outputs resp app_out in
  assert (resp.ST.status == ST.StepOk);
  assert (consumed == ST.server_network_consumed_prefix buffer_resp input);
  lemma_server_network_step_ok_received_decode_legal_response
    st0
    st1
    buffer_resp
    input
    network_out
    app_out;
  assert (exists msg.
    CT.received_tls_raw_delta_legal
      st0
      msg
      (ST.server_network_consumed_prefix buffer_resp input) /\
    ST.legal_network_response
      st0
      st1
      resp
      msg
      (ST.server_network_consumed_prefix buffer_resp input)
      network_out
      app_out /\
    (if CS.network_message_is_cleartext CL.Received msg
     then True
     else
       ST.server_protected_record_decode_correct
         st0
         (ST.server_network_consumed_prefix buffer_resp input)
         msg));
  let msg =
    ID.indefinite_description_ghost
      M.tls_message
      (fun msg ->
        CT.received_tls_raw_delta_legal
          st0
          msg
          (ST.server_network_consumed_prefix buffer_resp input) /\
        ST.legal_network_response
          st0
          st1
          resp
          msg
          (ST.server_network_consumed_prefix buffer_resp input)
          network_out
          app_out /\
        (if CS.network_message_is_cleartext CL.Received msg
         then True
         else
           ST.server_protected_record_decode_correct
             st0
             (ST.server_network_consumed_prefix buffer_resp input)
             msg)) in
  assert (CT.received_tls_raw_delta_legal
    st0
    msg
    consumed);
  assert (ST.legal_network_response
    st0
    st1
    resp
    msg
    consumed
    network_out
    app_out);
  assert (ST.legal_response_for_event
    st0
    st1
    resp
    (ST.received_message_event msg)
    B.empty
    consumed
    network_out
    app_out);
  assert (CT.received_tls_raw_delta_legal st0 msg consumed);
  lemma_received_tls_raw_delta_legal_raw_record_parse_success
    st0
    msg
    consumed;
  lemma_server_consumed_prefix_parse input buffer_resp;
  let wire =
    ID.indefinite_description_ghost
      CW.wire_message
      (fun wire -> exists residual.
        CPI.consumed_by_parse
          CW.tls_record_wire_format
          input
          wire
          consumed
          residual /\
        Seq.equal (CW.wire_serialize wire) consumed) in
  let residual =
    ID.indefinite_description_ghost
      B.bytes
      (fun residual ->
        CPI.consumed_by_parse
          CW.tls_record_wire_format
          input
          wire
          consumed
          residual /\
        Seq.equal (CW.wire_serialize wire) consumed) in
  assert (CPI.consumed_by_parse
    CW.tls_record_wire_format
    input
    wire
    consumed
    residual);
  assert (Seq.equal (CW.wire_serialize wire) consumed);
  assert (resp.ST.network_out_len == 0sz);
  Seq.lemma_len_slice network_out 0 0;
  Seq.lemma_eq_intro (ST.response_network_out resp network_out) B.empty;
  assert (Seq.equal (ST.response_network_out resp network_out) B.empty);
  CW.lemma_wire_outputs_of_empty ();
  assert (wire_outputs == []);
  lemma_server_response_local_outputs_match resp (ST.received_message_event msg) app_out;
  assert (server_local_outputs_match (ST.received_message_event msg) local_outputs);
  assert (CS.legal_connection_delta
    st0
    {
      CS.delta_event = ST.received_message_event msg;
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = consumed;
    }
    st1);
  assert (B.length (WF.serialize_all CW.tls_record_wire_format wire_outputs) == 0);
  assert (CS.sent_event_nonempty_seal_projection
    st0.CS.cs_model
    (ST.received_message_event msg)
    (WF.serialize_all CW.tls_record_wire_format wire_outputs));
  ST.lemma_server_received_message_event_decode_projection
    st0
    msg
    consumed;
  assert (CS.received_event_nonempty_decode_projection
    st0.CS.cs_model
    (ST.received_message_event msg)
    consumed);
  assert (server_step
    st0
    (SM.WireEvent wire)
    st1
    (CPI.step_output wire_outputs local_outputs));
  Seq.lemma_eq_elim received0 st0.CS.cs_wire_log.CL.raw_received;
  Seq.lemma_eq_elim sent0 st0.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim consumed (CW.wire_serialize wire);
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    (Seq.append received0 consumed));
  CL.lemma_append_empty_right st0.CS.cs_wire_log.CL.raw_sent;
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (Seq.append sent0 B.empty));
  assert (Seq.equal
    B.empty
    (WF.serialize_all CW.tls_record_wire_format wire_outputs));
  Seq.lemma_len_slice input 0 (B.length input);
  assert (Seq.equal (CPI.input_bytes input input_len) input);
  Seq.lemma_eq_elim (CPI.input_bytes input input_len) input;
  assert (CPI.consumed_by_parse
    CW.tls_record_wire_format
    (CPI.input_bytes input input_len)
    wire
    consumed
    residual);
  assert (CPI.output_written network_out resp.ST.network_out_len B.empty);
  assert ((CTypes.server_process_result buffer_resp).CPI.process_status == CPI.StepOk);
  assert (SZ.v buffer_resp.ST.consumed_len <= B.length input);
  assert (consumed == Seq.slice input 0 (SZ.v buffer_resp.ST.consumed_len));
  Seq.lemma_len_slice input 0 (SZ.v buffer_resp.ST.consumed_len);
  assert (B.length consumed == SZ.v buffer_resp.ST.consumed_len);
  assert (SZ.v (CTypes.server_process_result buffer_resp).CPI.process_consumed_len ==
    B.length consumed);
  let produced = B.empty in
  assert (Seq.equal
    produced
    (WF.serialize_all CW.tls_record_wire_format wire_outputs));
  assert (CPI.output_written
    network_out
    (CTypes.server_process_result buffer_resp).CPI.process_produced_len
    produced);
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (Seq.append sent0 produced));
  assert (CPI.consumed_by_parse
    (server_system initial).WFSM.wfsm_wire_format
    (CPI.input_bytes input input_len)
    wire
    consumed
    residual);
  assert (Seq.equal
    produced
    (WF.serialize_all
      (server_system initial).WFSM.wfsm_wire_format
      wire_outputs));
  assert (exists msg' residual' produced.
    CPI.consumed_by_parse
      CW.tls_record_wire_format
      (CPI.input_bytes input input_len)
      msg'
      consumed
      residual' /\
    SZ.v (CTypes.server_process_result buffer_resp).CPI.process_consumed_len ==
      B.length consumed /\
    (server_system initial).WFSM.wfsm_state_machine.SM.sm_step
      st0
      (SM.WireEvent msg')
      st1
      (CPI.step_output wire_outputs local_outputs) /\
    Seq.equal
      produced
      (WF.serialize_all CW.tls_record_wire_format wire_outputs) /\
    CPI.output_written
      network_out
      (CTypes.server_process_result buffer_resp).CPI.process_produced_len
      produced /\
    Seq.equal st1.CS.cs_wire_log.CL.raw_received (Seq.append received0 consumed) /\
    Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced));
  match (CTypes.server_process_result buffer_resp).CPI.process_status with
  | CPI.StepOk ->
    assert (CPI.buffers_wf input input_len old_network_out out_len);
    assert (Seq.length network_out == Seq.length old_network_out);
    assert (exists msg' residual' produced.
      CPI.consumed_by_parse
        (server_system initial).WFSM.wfsm_wire_format
        (CPI.input_bytes input input_len)
        msg'
        consumed
        residual' /\
      SZ.v (CTypes.server_process_result buffer_resp).CPI.process_consumed_len ==
        B.length consumed /\
      (server_system initial).WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.WireEvent msg')
        st1
        (CPI.step_output wire_outputs local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all
          (server_system initial).WFSM.wfsm_wire_format
          wire_outputs) /\
      CPI.output_written
        network_out
        (CTypes.server_process_result buffer_resp).CPI.process_produced_len
        produced /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_received (Seq.append received0 consumed) /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced));
    assert (CPI.network_process_correct
      (server_system initial)
      input
      input_len
      old_network_out
      network_out
      out_len
      received0
      sent0
      st0
      (CTypes.server_process_result buffer_resp)
      st1.CS.cs_wire_log.CL.raw_received
      st1.CS.cs_wire_log.CL.raw_sent
      st1
      consumed
      wire_outputs
      local_outputs)
  | _ ->
    assert False

[@@pulse_unfold]
let server_network_frame_pre
  (frame:tls_server_network_frame)
  (_input:array U8.t)
  (input_len:SZ.t)
  (_out:array U8.t)
  (out_len:SZ.t)
  (input_contents:B.bytes)
  (old_network_out:B.bytes)
  : slprop =
  pts_to
    frame.tls_server_network_app_out
    (Ghost.reveal frame.tls_server_network_old_app_out) **
  pure (
    B.length input_contents == SZ.v input_len /\
    B.length old_network_out == SZ.v out_len /\
    B.length (Ghost.reveal frame.tls_server_network_old_app_out) ==
      SZ.v frame.tls_server_network_app_out_len)

let server_network_frame_post
  (frame:tls_server_network_frame)
  (result:CPI.process_result)
  (input_contents:B.bytes)
  (_input_len:SZ.t)
  (_old_network_out:B.bytes)
  (network_out:B.bytes)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (consumed:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  : slprop =
  exists* (app_out:B.bytes) (buffer_resp:ST.server_buffer_response).
    pts_to frame.tls_server_network_app_out app_out **
    pure (
      result == CTypes.server_process_result buffer_resp /\
      ST.server_network_bytes_end_to_end_correct
        st0
        st1
        buffer_resp
        input_contents
        network_out
        app_out /\
      ST.server_network_consumed_input_projection
        st0
        st1
        buffer_resp
        input_contents
        network_out
        app_out /\
      Seq.equal
        consumed
        (ST.server_network_consumed_prefix buffer_resp input_contents) /\
      wire_outputs ==
        server_response_wire_outputs buffer_resp.ST.response network_out /\
      local_outputs ==
        server_response_local_outputs buffer_resp.ST.response app_out)

[@@pulse_unfold]
let server_local_frame_pre
  (ev:CTypes.server_local_event)
  (frame:tls_server_local_frame)
  (st0:CS.connection_state)
  (_out:array U8.t)
  (out_len:SZ.t)
  (old_network_out:B.bytes)
  : slprop =
  let api = CTypes.server_local_event_api ev in
  pts_to frame.tls_server_local_payload api.CTypes.server_local_payload **
  pts_to
    frame.tls_server_local_app_out
    (Ghost.reveal frame.tls_server_local_old_app_out) **
  pure (
    B.length api.CTypes.server_local_payload ==
      SZ.v frame.tls_server_local_payload_len /\
    B.length old_network_out == SZ.v out_len /\
    B.length (Ghost.reveal frame.tls_server_local_old_app_out) ==
      SZ.v frame.tls_server_local_app_out_len /\
    ST.server_local_event_input_ready
      st0
      api.CTypes.server_local_kind
      api.CTypes.server_local_payload)

let server_local_frame_post
  (ev:CTypes.server_local_event)
  (frame:tls_server_local_frame)
  (result:CPI.process_result)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  : slprop =
  let api = CTypes.server_local_event_api ev in
  exists* (app_out:B.bytes) (resp:ST.server_response).
    pts_to frame.tls_server_local_payload api.CTypes.server_local_payload **
    pts_to frame.tls_server_local_app_out app_out **
    pure (
      result == CTypes.server_local_process_result resp /\
      ST.server_local_event_end_to_end_correct
        st0
        st1
        resp
        api.CTypes.server_local_kind
        api.CTypes.server_local_payload
        network_out
        app_out /\
      wire_outputs ==
        server_response_wire_outputs resp network_out /\
      local_outputs ==
        server_response_local_outputs resp app_out)

let server_state_ahead
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : prop =
  CPI.state_ahead (server_system initial) st0 st1

let lemma_server_canonical_step_rel_state_ahead
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires server_canonical_step_rel st0 st1)
      (ensures server_state_ahead initial st0 st1)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event CW.wire_message CTypes.server_local_event)
      (fun ev -> exists out. server_step st0 ev st1 out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output CW.wire_message CTypes.local_output)
      (fun out -> server_step st0 ev st1 out) in
  let tr = {
    SM.tr_event = ev;
    SM.tr_next_state = st1;
    SM.tr_output = out;
  } in
  assert (SM.trace_reaches
    (server_system initial).WFSM.wfsm_state_machine
    st0
    [tr]
    st1);
  assert (exists trace.
    SM.trace_reaches
      (server_system initial).WFSM.wfsm_state_machine
      st0
      trace
      st1)

let lemma_server_progress_state_ahead
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires server_progress_preorder st0 st1)
      (ensures server_state_ahead initial st0 st1)
=
  RTC.induct
    server_canonical_step_rel
    (fun x y -> server_state_ahead initial x y)
    (fun x ->
      SM.lemma_state_evolves_refl
        (server_system initial).WFSM.wfsm_state_machine
        x)
    (fun x y ->
      lemma_server_canonical_step_rel_state_ahead initial x y)
    (fun x y z ->
      SM.lemma_state_evolves_trans
        (server_system initial).WFSM.wfsm_state_machine
        x
        y
        z)
    st0
    st1
    ()

let lemma_server_step_wire_log_delta
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message CTypes.local_output)
  : Lemma
      (requires server_step st0 ev st1 out)
      (ensures
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_sent
          (B.append
            st0.CS.cs_wire_log.CL.raw_sent
            (WF.serialize_all
              CW.tls_record_wire_format
              out.SM.so_wire_outputs)) /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          (B.append
            st0.CS.cs_wire_log.CL.raw_received
            (WF.serialize_all
              CW.tls_record_wire_format
              (WFSM.event_input_messages ev))))
=
  match ev with
  | SM.WireEvent wire ->
    eliminate exists msg.
      (let conn_ev =
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = msg;
        } in
      CS.legal_connection_delta
        st0
        {
          CS.delta_event = conn_ev;
          CS.delta_raw_sent =
            WF.serialize_all
              CW.tls_record_wire_format
              out.SM.so_wire_outputs;
          CS.delta_raw_received = CW.wire_serialize wire;
        }
        st1 /\
      server_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns
      Seq.equal
        st1.CS.cs_wire_log.CL.raw_sent
        (B.append
          st0.CS.cs_wire_log.CL.raw_sent
          (WF.serialize_all
            CW.tls_record_wire_format
            out.SM.so_wire_outputs)) /\
      Seq.equal
        st1.CS.cs_wire_log.CL.raw_received
        (B.append
          st0.CS.cs_wire_log.CL.raw_received
          (WF.serialize_all
            CW.tls_record_wire_format
            (WFSM.event_input_messages ev)))
    with _.
    (
      assert (WFSM.event_input_messages ev == [wire]);
      Seq.append_empty_r (CW.wire_serialize wire)
    )
  | SM.LocalEvent local ->
    let api = CTypes.server_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      server_api_event_matches api conn_ev /\
      server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      server_local_outputs_match conn_ev out.SM.so_local_outputs /\
      CS.legal_connection_delta
        st0
        {
          CS.delta_event = conn_ev;
          CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty;
        }
        st1
    returns
      Seq.equal
        st1.CS.cs_wire_log.CL.raw_sent
        (B.append
          st0.CS.cs_wire_log.CL.raw_sent
          (WF.serialize_all
            CW.tls_record_wire_format
            out.SM.so_wire_outputs)) /\
      Seq.equal
        st1.CS.cs_wire_log.CL.raw_received
        (B.append
          st0.CS.cs_wire_log.CL.raw_received
          (WF.serialize_all
            CW.tls_record_wire_format
            (WFSM.event_input_messages ev)))
    with _.
    (
      assert (WFSM.event_input_messages ev == []);
      assert (Seq.equal
        (WF.serialize_all CW.tls_record_wire_format [])
        Seq.empty);
      CW.lemma_b_empty_seq_empty ();
      Seq.lemma_eq_elim
        raw_sent
        (WF.serialize_all
          CW.tls_record_wire_format
          out.SM.so_wire_outputs)
    )

let rec lemma_server_trace_wire_logs_match
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (trace:list
    (SM.transition
      CS.connection_state
      CW.wire_message
      CTypes.server_local_event
      CTypes.local_output))
  (st1:CS.connection_state)
  : Lemma
      (requires
        SM.trace_reaches
          (server_state_machine initial)
          st0
          trace
          st1)
      (ensures
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_sent
          (B.append
            st0.CS.cs_wire_log.CL.raw_sent
            (WF.serialize_all
              CW.tls_record_wire_format
              (SM.trace_wire_outputs trace))) /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          (B.append
            st0.CS.cs_wire_log.CL.raw_received
            (WF.serialize_all
              CW.tls_record_wire_format
              (WFSM.trace_input_messages trace))))
      (decreases trace)
=
  match trace with
  | [] ->
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_sent;
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received
  | tr :: rest ->
    assert (server_step
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output);
    lemma_server_step_wire_log_delta
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output;
    lemma_server_trace_wire_logs_match
      initial
      tr.SM.tr_next_state
      rest
      st1;
    let step_sent =
      WF.serialize_all
        CW.tls_record_wire_format
        tr.SM.tr_output.SM.so_wire_outputs in
    let rest_sent =
      WF.serialize_all
        CW.tls_record_wire_format
        (SM.trace_wire_outputs rest) in
    let step_received =
      WF.serialize_all
        CW.tls_record_wire_format
        (WFSM.event_input_messages tr.SM.tr_event) in
    let rest_received =
      WF.serialize_all
        CW.tls_record_wire_format
        (WFSM.trace_input_messages rest) in
    CW.lemma_wire_serialize_all_append
      tr.SM.tr_output.SM.so_wire_outputs
      (SM.trace_wire_outputs rest);
    CW.lemma_wire_serialize_all_append
      (WFSM.event_input_messages tr.SM.tr_event)
      (WFSM.trace_input_messages rest);
    Seq.lemma_eq_elim
      tr.SM.tr_next_state.CS.cs_wire_log.CL.raw_sent
      (B.append st0.CS.cs_wire_log.CL.raw_sent step_sent);
    Seq.lemma_eq_elim
      tr.SM.tr_next_state.CS.cs_wire_log.CL.raw_received
      (B.append st0.CS.cs_wire_log.CL.raw_received step_received);
    Seq.append_assoc st0.CS.cs_wire_log.CL.raw_sent step_sent rest_sent;
    Seq.append_assoc st0.CS.cs_wire_log.CL.raw_received step_received rest_received;
    assert (Seq.equal
      st1.CS.cs_wire_log.CL.raw_sent
      (B.append
        st0.CS.cs_wire_log.CL.raw_sent
        (B.append step_sent rest_sent)));
    assert (Seq.equal
      st1.CS.cs_wire_log.CL.raw_received
      (B.append
        st0.CS.cs_wire_log.CL.raw_received
        (B.append step_received rest_received)))

let lemma_server_state_ahead_valid_byte_trace
  (initial:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  : Lemma
      (requires
        server_invariant_pure initial received sent st /\
        server_state_ahead initial initial st)
      (ensures
        WFSM.valid_byte_trace
          (server_system initial)
          received
          st
          sent
          Seq.empty)
=
  eliminate exists trace.
    SM.trace_reaches
      (server_system initial).WFSM.wfsm_state_machine
      initial
      trace
      st
  returns
    WFSM.valid_byte_trace
      (server_system initial)
      received
      st
      sent
      Seq.empty
  with _.
  (
    assert ((server_system initial).WFSM.wfsm_state_machine ==
      server_state_machine initial);
    assert ((server_system initial).WFSM.wfsm_wire_format ==
      CW.tls_record_wire_format);
    lemma_server_trace_wire_logs_match
      initial
      initial
      trace
      st;
    CW.lemma_wire_parse_serialize_all_inverse
      (WFSM.trace_input_messages trace);
    Seq.append_empty_l
      (WF.serialize_all
        CW.tls_record_wire_format
        (SM.trace_wire_outputs trace));
    Seq.append_empty_l
      (WF.serialize_all
        CW.tls_record_wire_format
        (WFSM.trace_input_messages trace));
    Seq.lemma_eq_elim initial.CS.cs_wire_log.CL.raw_sent B.empty;
    Seq.lemma_eq_elim initial.CS.cs_wire_log.CL.raw_received B.empty;
    Seq.lemma_eq_elim
      st.CS.cs_wire_log.CL.raw_sent
      (WF.serialize_all
        CW.tls_record_wire_format
        (SM.trace_wire_outputs trace));
    Seq.lemma_eq_elim
      st.CS.cs_wire_log.CL.raw_received
      (WF.serialize_all
        CW.tls_record_wire_format
        (WFSM.trace_input_messages trace));
    Seq.lemma_eq_elim sent st.CS.cs_wire_log.CL.raw_sent;
    Seq.lemma_eq_elim received st.CS.cs_wire_log.CL.raw_received;
    assert (WF.parses_as
      CW.tls_record_wire_format
      received
      (WFSM.trace_input_messages trace)
      Seq.empty);
    assert (exists trace'.
      SM.trace_reaches
        (server_system initial).WFSM.wfsm_state_machine
        (server_system initial).WFSM.wfsm_state_machine.SM.sm_initial_state
        trace'
        st /\
      WF.parses_as
        (server_system initial).WFSM.wfsm_wire_format
        received
        (WFSM.trace_input_messages trace')
        Seq.empty /\
      Seq.equal
        sent
        (WF.serialize_all
          (server_system initial).WFSM.wfsm_wire_format
          (SM.trace_wire_outputs trace')))
  )

let lemma_server_legal_delta_histories_ahead
  (st0:CS.connection_state)
  (delta:CS.connection_delta)
  (st1:CS.connection_state)
  : Lemma
      (requires CS.legal_connection_delta st0 delta st1)
      (ensures
        TCP.bytes_extends
          st0.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_received /\
        TCP.bytes_extends
          st0.CS.cs_wire_log.CL.raw_sent
          st1.CS.cs_wire_log.CL.raw_sent)
=
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    (B.append st0.CS.cs_wire_log.CL.raw_received delta.CS.delta_raw_received));
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (B.append st0.CS.cs_wire_log.CL.raw_sent delta.CS.delta_raw_sent));
  CPI.lemma_bytes_extends_append_equal
    st0.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_received
    delta.CS.delta_raw_received;
  CPI.lemma_bytes_extends_append_equal
    st0.CS.cs_wire_log.CL.raw_sent
    st1.CS.cs_wire_log.CL.raw_sent
    delta.CS.delta_raw_sent

let lemma_server_step_histories_ahead
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message CTypes.local_output)
  : Lemma
      (requires server_step st0 ev st1 out)
      (ensures
        TCP.bytes_extends
          st0.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_received /\
        TCP.bytes_extends
          st0.CS.cs_wire_log.CL.raw_sent
          st1.CS.cs_wire_log.CL.raw_sent)
=
  match ev with
  | SM.WireEvent wire ->
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg ->
          let conn_ev =
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = msg;
            } in
          CS.legal_connection_delta
            st0
            {
              CS.delta_event = conn_ev;
              CS.delta_raw_sent =
                WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
              CS.delta_raw_received = CW.wire_serialize wire;
            }
            st1 /\
          server_local_outputs_match conn_ev out.SM.so_local_outputs) in
    let conn_ev =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = msg;
      } in
    let delta = {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent =
        WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
      CS.delta_raw_received = CW.wire_serialize wire;
    } in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_server_legal_delta_histories_ahead st0 delta st1
  | SM.LocalEvent local ->
    let api = CTypes.server_local_event_api local in
    let conn_ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun conn_ev ->
          exists raw_sent raw_received.
            server_api_event_matches api conn_ev /\
            server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
            server_local_outputs_match conn_ev out.SM.so_local_outputs /\
            CS.legal_connection_delta
              st0
              {
                CS.delta_event = conn_ev;
                CS.delta_raw_sent = raw_sent;
                CS.delta_raw_received = raw_received;
              }
              st1) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent ->
          exists raw_received.
            server_api_event_matches api conn_ev /\
            server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
            server_local_outputs_match conn_ev out.SM.so_local_outputs /\
            CS.legal_connection_delta
              st0
              {
                CS.delta_event = conn_ev;
                CS.delta_raw_sent = raw_sent;
                CS.delta_raw_received = raw_received;
              }
              st1) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          server_api_event_matches api conn_ev /\
          server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
          server_local_outputs_match conn_ev out.SM.so_local_outputs /\
          CS.legal_connection_delta
            st0
            {
              CS.delta_event = conn_ev;
              CS.delta_raw_sent = raw_sent;
              CS.delta_raw_received = raw_received;
            }
            st1) in
    let delta = {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    } in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_server_legal_delta_histories_ahead st0 delta st1

let lemma_server_canonical_step_rel_histories_ahead
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires server_canonical_step_rel st0 st1)
      (ensures
        TCP.bytes_extends
          st0.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_received /\
        TCP.bytes_extends
          st0.CS.cs_wire_log.CL.raw_sent
          st1.CS.cs_wire_log.CL.raw_sent)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event CW.wire_message CTypes.server_local_event)
      (fun ev -> exists out. server_step st0 ev st1 out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output CW.wire_message CTypes.local_output)
      (fun out -> server_step st0 ev st1 out) in
  lemma_server_step_histories_ahead st0 ev st1 out

let lemma_server_progress_histories_ahead
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires server_progress_preorder st0 st1)
      (ensures
        TCP.bytes_extends
          st0.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_received /\
        TCP.bytes_extends
          st0.CS.cs_wire_log.CL.raw_sent
          st1.CS.cs_wire_log.CL.raw_sent)
=
  RTC.induct
    server_canonical_step_rel
    (fun x y ->
      TCP.bytes_extends
        x.CS.cs_wire_log.CL.raw_received
        y.CS.cs_wire_log.CL.raw_received /\
      TCP.bytes_extends
        x.CS.cs_wire_log.CL.raw_sent
        y.CS.cs_wire_log.CL.raw_sent)
    (fun x ->
      CPI.lemma_bytes_extends_refl x.CS.cs_wire_log.CL.raw_received;
      CPI.lemma_bytes_extends_refl x.CS.cs_wire_log.CL.raw_sent)
    (fun x y ->
      lemma_server_canonical_step_rel_histories_ahead x y)
    (fun x y z ->
      CPI.lemma_bytes_extends_trans
        x.CS.cs_wire_log.CL.raw_received
        y.CS.cs_wire_log.CL.raw_received
        z.CS.cs_wire_log.CL.raw_received;
      CPI.lemma_bytes_extends_trans
        x.CS.cs_wire_log.CL.raw_sent
        y.CS.cs_wire_log.CL.raw_sent
        z.CS.cs_wire_log.CL.raw_sent)
    st0
    st1
    ()

let server_invariant
  (srv:canonical_server)
  (received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  : slprop =
  exists* certificate_chain credential_identity.
    S.connection_exactly srv.canonical_server_state st **
    O.is_server_credentials
      srv.canonical_server_credentials
      certificate_chain
      credential_identity **
    MR.pts_to srv.canonical_server_progress #1.0R st **
    MR.snapshot
      srv.canonical_server_progress
      (Ghost.reveal srv.canonical_server_initial) **
    pure (
      server_invariant_pure
        (Ghost.reveal srv.canonical_server_initial)
        received
        sent
        st /\
      server_config_matches_credentials
        (Ghost.reveal srv.canonical_server_initial)
        certificate_chain
        credential_identity)

[@@pulse_unfold]
let server_snapshot
  (srv:canonical_server)
  (received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  : slprop =
  MR.snapshot srv.canonical_server_progress st **
  pure (server_invariant_pure
    (Ghost.reveal srv.canonical_server_initial)
    received
    sent
    st)

ghost fn server_invariant_valid
  (srv:canonical_server)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires server_invariant
  srv
  (Ghost.reveal received)
  (Ghost.reveal sent)
  (Ghost.reveal st)
ensures server_invariant
  srv
  (Ghost.reveal received)
  (Ghost.reveal sent)
  (Ghost.reveal st) **
  pure (
    WFSM.valid_byte_trace
      (server_system (Ghost.reveal srv.canonical_server_initial))
      (Ghost.reveal received)
      (Ghost.reveal st)
      (Ghost.reveal sent)
      Seq.empty)
{
  unfold (server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  with certificate_chain credential_identity. _;
  MR.recall_snapshot
    srv.canonical_server_progress
    #1.0R
    #(Ghost.reveal st)
    #(Ghost.reveal srv.canonical_server_initial);
  lemma_server_progress_state_ahead
    (Ghost.reveal srv.canonical_server_initial)
    (Ghost.reveal srv.canonical_server_initial)
    (Ghost.reveal st);
  lemma_server_state_ahead_valid_byte_trace
    (Ghost.reveal srv.canonical_server_initial)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st);
  assert (pure (server_invariant_pure
    (Ghost.reveal srv.canonical_server_initial)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)));
  assert (pure (WFSM.valid_byte_trace
    (server_system (Ghost.reveal srv.canonical_server_initial))
    (Ghost.reveal received)
    (Ghost.reveal st)
    (Ghost.reveal sent)
    Seq.empty));
  with certificate_chain credential_identity.
  fold (server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st))
}

fn new_canonical_server
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  (#supported_profile_provider:erased server_supported_profile_provider)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len /\
                 B.length 'certificate_chain_bytes <=
                   TLS13.Impl.ConnectionState.Bounds.max_server_certificate_chain_len)
  returns result:option canonical_server
  ensures pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (match result with
           | Some srv ->
             exists* credential_identity.
               server_invariant
                 srv
                 B.empty
                 B.empty
                 (CR.server_initial_state
                   (Ghost.reveal 'certificate_chain_bytes)
                   credential_identity) **
               pure (ST.server_end_to_end_invariant
                 (CR.server_initial_state
                   (Ghost.reveal 'certificate_chain_bytes)
                   credential_identity))
           | None ->
             emp)
{
  let creds_opt =
    O.server_credentials_new
      certificate_chain
      certificate_chain_len
      private_key
      private_key_len;
  match creds_opt {
  None -> {
    None
  }
  Some creds -> {
    with credential_identity. assert (
      O.is_server_credentials
        creds
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity);
    let erased_identity : erased CS.server_credential_identity =
      Ghost.hide credential_identity;
    let s =
      S.new_server_erased_credential_identity
        certificate_chain
        certificate_chain_len
        #erased_identity;
    assert (pure (Ghost.reveal erased_identity == credential_identity));
    rewrite
      (S.connection_exactly
        s
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          (Ghost.reveal erased_identity)))
      as
      (S.connection_exactly
        s
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity));
    let progress = MR.alloc #_ #server_progress_preorder
      (CR.server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity);
    MR.take_snapshot
      progress
      (CR.server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity);
    let srv = {
      canonical_server_state = s;
      canonical_server_credentials = creds;
      canonical_server_progress = progress;
      canonical_server_initial =
        Ghost.hide
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity);
      canonical_server_supported_profile =
        Ghost.hide
          ((Ghost.reveal supported_profile_provider)
            (CR.server_initial_state
              (Ghost.reveal 'certificate_chain_bytes)
              credential_identity));
    };
    rewrite
      (S.connection_exactly
        s
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity))
      as
      (S.connection_exactly
        srv.canonical_server_state
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity));
    rewrite
      (O.is_server_credentials
        creds
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity)
      as
      (O.is_server_credentials
        srv.canonical_server_credentials
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity);
    rewrite
      (MR.pts_to
        progress
        #1.0R
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity))
      as
      (MR.pts_to
        srv.canonical_server_progress
        #1.0R
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity));
    rewrite
      (MR.snapshot
        progress
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity))
      as
      (MR.snapshot
        srv.canonical_server_progress
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity));
    assert (pure (Ghost.reveal srv.canonical_server_initial ==
      (CR.server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity)));
    rewrite
      (MR.snapshot
        srv.canonical_server_progress
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity))
      as
      (MR.snapshot
        srv.canonical_server_progress
        (Ghost.reveal srv.canonical_server_initial));
    assert (pure (Seq.equal B.empty
      (CR.server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity).CS.cs_wire_log.CL.raw_received));
    assert (pure (Seq.equal B.empty
      (CR.server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity).CS.cs_wire_log.CL.raw_sent));
    assert (pure (server_invariant_pure
      (CR.server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity)
      B.empty
      B.empty
      (CR.server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity)));
    assert (pure (server_config_matches_credentials
      (CR.server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity)
      (Ghost.reveal 'certificate_chain_bytes)
      credential_identity));
    fold
      (server_invariant
        srv
        B.empty
        B.empty
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity));
    Some srv
  }
  }
}

ghost fn take_server_snapshot
  (srv:canonical_server)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires server_invariant
  srv
  (Ghost.reveal received)
  (Ghost.reveal sent)
  (Ghost.reveal st)
ensures server_invariant
  srv
  (Ghost.reveal received)
  (Ghost.reveal sent)
  (Ghost.reveal st) **
  server_snapshot
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)
{
  unfold (server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  with certificate_chain credential_identity. _;
  MR.take_snapshot
    srv.canonical_server_progress
    (Ghost.reveal st);
  assert (pure (server_invariant_pure
    (Ghost.reveal srv.canonical_server_initial)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)));
  with certificate_chain credential_identity.
  fold (server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  fold (server_snapshot
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st))
}

ghost fn recall_server_snapshot
  (srv:canonical_server)
  (snapshot_received:Ghost.erased B.bytes)
  (snapshot_sent:Ghost.erased B.bytes)
  (snapshot_state:Ghost.erased CS.connection_state)
  (current_received:Ghost.erased B.bytes)
  (current_sent:Ghost.erased B.bytes)
  (current_state:Ghost.erased CS.connection_state)
requires server_snapshot
  srv
  (Ghost.reveal snapshot_received)
  (Ghost.reveal snapshot_sent)
  (Ghost.reveal snapshot_state) **
  server_invariant
    srv
    (Ghost.reveal current_received)
    (Ghost.reveal current_sent)
    (Ghost.reveal current_state)
ensures server_snapshot
  srv
  (Ghost.reveal snapshot_received)
  (Ghost.reveal snapshot_sent)
  (Ghost.reveal snapshot_state) **
  server_invariant
    srv
    (Ghost.reveal current_received)
    (Ghost.reveal current_sent)
    (Ghost.reveal current_state) **
  pure (
    CPI.state_ahead
      (server_system (Ghost.reveal srv.canonical_server_initial))
      (Ghost.reveal snapshot_state)
      (Ghost.reveal current_state) /\
    CPI.histories_ahead
      (Ghost.reveal snapshot_received)
      (Ghost.reveal snapshot_sent)
      (Ghost.reveal current_received)
      (Ghost.reveal current_sent))
{
  unfold (server_snapshot
    srv
    (Ghost.reveal snapshot_received)
    (Ghost.reveal snapshot_sent)
    (Ghost.reveal snapshot_state));
  unfold (server_invariant
    srv
    (Ghost.reveal current_received)
    (Ghost.reveal current_sent)
    (Ghost.reveal current_state));
  with certificate_chain credential_identity. _;
  MR.recall_snapshot
    srv.canonical_server_progress
    #1.0R
    #(Ghost.reveal current_state)
    #(Ghost.reveal snapshot_state);
  lemma_server_progress_state_ahead
    (Ghost.reveal srv.canonical_server_initial)
    (Ghost.reveal snapshot_state)
    (Ghost.reveal current_state);
  lemma_server_progress_histories_ahead
    (Ghost.reveal snapshot_state)
    (Ghost.reveal current_state);
  assert (pure (CPI.state_ahead
    (server_system (Ghost.reveal srv.canonical_server_initial))
    (Ghost.reveal snapshot_state)
    (Ghost.reveal current_state)));
  assert (pure (server_invariant_pure
    (Ghost.reveal srv.canonical_server_initial)
    (Ghost.reveal snapshot_received)
    (Ghost.reveal snapshot_sent)
    (Ghost.reveal snapshot_state)));
  assert (pure (server_invariant_pure
    (Ghost.reveal srv.canonical_server_initial)
    (Ghost.reveal current_received)
    (Ghost.reveal current_sent)
    (Ghost.reveal current_state)));
  assert (pure (CPI.histories_ahead
    (Ghost.reveal snapshot_received)
    (Ghost.reveal snapshot_sent)
    (Ghost.reveal current_received)
    (Ghost.reveal current_sent)));
  with certificate_chain credential_identity.
  fold (server_invariant
    srv
    (Ghost.reveal current_received)
    (Ghost.reveal current_sent)
    (Ghost.reveal current_state));
  fold (server_snapshot
    srv
    (Ghost.reveal snapshot_received)
    (Ghost.reveal snapshot_sent)
    (Ghost.reveal snapshot_state))
}

let server_network_frame_post_fact
  (frame:tls_server_network_frame)
  (result:CPI.process_result)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (consumed:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  (app_out:B.bytes)
  (buffer_resp:ST.server_buffer_response)
  : prop =
  result == CTypes.server_process_result buffer_resp /\
  ST.server_network_bytes_end_to_end_correct
    st0
    st1
    buffer_resp
    input_contents
    network_out
    app_out /\
  ST.server_network_consumed_input_projection
    st0
    st1
    buffer_resp
    input_contents
    network_out
    app_out /\
  Seq.equal
    consumed
    (ST.server_network_consumed_prefix buffer_resp input_contents) /\
  wire_outputs ==
    server_response_wire_outputs buffer_resp.ST.response network_out /\
  local_outputs ==
    server_response_local_outputs buffer_resp.ST.response app_out

let server_network_common_witness
  (initial:CS.connection_state)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (base:tls_server_network_frame)
  (st1:CS.connection_state)
  (app_out:B.bytes)
  (buffer_resp:ST.server_buffer_response)
  (consumed:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  : prop =
  let result = CTypes.server_process_result buffer_resp in
  let received1 = st1.CS.cs_wire_log.CL.raw_received in
  let sent1 = st1.CS.cs_wire_log.CL.raw_sent in
  server_invariant_pure initial received1 sent1 st1 /\
  server_network_frame_post_fact
    base
    result
    input_contents
    input_len
    old_network_out
    network_out
    st0
    st1
    consumed
    wire_outputs
    local_outputs
    app_out
    buffer_resp /\
  CPI.network_process_correct
    (server_system initial)
    input_contents
    input_len
    old_network_out
    network_out
    out_len
    received0
    sent0
    st0
    result
    received1
    sent1
    st1
    consumed
    wire_outputs
    local_outputs

let server_network_bridge_result
  (initial:CS.connection_state)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (base:tls_server_network_frame)
  (st1:CS.connection_state)
  (app_out:B.bytes)
  (buffer_resp:ST.server_buffer_response)
  : prop =
  exists consumed wire_outputs local_outputs.
    server_network_common_witness
      initial
      received0
      sent0
      st0
      input_contents
      input_len
      old_network_out
      network_out
      out_len
      base
      st1
      app_out
      buffer_resp
      consumed
      wire_outputs
      local_outputs

let lemma_server_network_step_ok_bridge_result
  (initial:CS.connection_state)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (base:tls_server_network_frame)
  (st1:CS.connection_state)
  (app_out:B.bytes)
  (buffer_resp:ST.server_buffer_response)
  : Lemma
      (requires
        server_invariant_pure initial received0 sent0 st0 /\
        CPI.buffers_wf input_contents input_len old_network_out out_len /\
        B.length input_contents == SZ.v input_len /\
        B.length network_out == B.length old_network_out /\
        B.length app_out == SZ.v base.tls_server_network_app_out_len /\
        ST.server_network_bytes_end_to_end_correct
          st0
          st1
          buffer_resp
          input_contents
          network_out
          app_out /\
        ST.server_network_consumed_input_projection
          st0
          st1
          buffer_resp
          input_contents
          network_out
          app_out /\
        buffer_resp.ST.response.ST.status == ST.StepOk)
      (ensures
        server_network_bridge_result
          initial
          received0
          sent0
          st0
          input_contents
          input_len
          old_network_out
          network_out
          out_len
          base
          st1
          app_out
          buffer_resp)
=
  let consumed = ST.server_network_consumed_prefix buffer_resp input_contents in
  let wire_outputs =
    server_response_wire_outputs buffer_resp.ST.response network_out in
  let local_outputs =
    server_response_local_outputs buffer_resp.ST.response app_out in
  lemma_server_network_step_ok_process_correct
    initial
    st0
    st1
    buffer_resp
    input_contents
    input_len
    old_network_out
    network_out
    out_len
    app_out
    received0
    sent0;
  lemma_server_network_step_ok_legal_response
    st0
    st1
    buffer_resp
    input_contents
    network_out
    app_out;
  let msg =
    ID.indefinite_description_ghost
      M.tls_message
      (fun msg ->
        ST.legal_network_response
          st0
          st1
          buffer_resp.ST.response
          msg
          consumed
          network_out
          app_out) in
  assert (ST.legal_network_response
    st0
    st1
    buffer_resp.ST.response
    msg
    consumed
    network_out
    app_out);
  ST.lemma_legal_network_response_preserves_config
    st0
    st1
    buffer_resp.ST.response
    msg
    consumed
    network_out
    app_out;
  assert (server_invariant_pure
    initial
    st1.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_sent
    st1);
  assert (server_network_frame_post_fact
    base
    (CTypes.server_process_result buffer_resp)
    input_contents
    input_len
    old_network_out
    network_out
    st0
    st1
    consumed
    wire_outputs
    local_outputs
    app_out
    buffer_resp);
  assert (server_network_common_witness
    initial
    received0
    sent0
    st0
    input_contents
    input_len
    old_network_out
    network_out
    out_len
    base
    st1
    app_out
    buffer_resp
    consumed
    wire_outputs
    local_outputs);
  assert (exists consumed' wire_outputs' local_outputs'.
    server_network_common_witness
      initial
      received0
      sent0
      st0
      input_contents
      input_len
      old_network_out
      network_out
      out_len
      base
      st1
      app_out
      buffer_resp
      consumed'
      wire_outputs'
      local_outputs')

// Partial non-StepOk bridge lemmas for the stuttering network results.  These
// are not yet enough to discharge server_network_bridge_obligation globally:
// NeedMoreInput still needs the concrete output-stutter fact, and both
// stuttering branches need the app-output length fact, threaded from the server
// network wrapper.
let lemma_server_network_need_more_input_bridge_result
  (initial:CS.connection_state)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (base:tls_server_network_frame)
  (st1:CS.connection_state)
  (app_out:B.bytes)
  (buffer_resp:ST.server_buffer_response)
  : Lemma
      (requires
        server_invariant_pure initial received0 sent0 st0 /\
        CPI.buffers_wf input_contents input_len old_network_out out_len /\
        B.length input_contents == SZ.v input_len /\
        B.length network_out == B.length old_network_out /\
        B.length app_out == SZ.v base.tls_server_network_app_out_len /\
        ST.server_network_bytes_end_to_end_correct
          st0
          st1
          buffer_resp
          input_contents
          network_out
          app_out /\
        ST.server_network_consumed_input_projection
          st0
          st1
          buffer_resp
          input_contents
          network_out
          app_out /\
        buffer_resp.ST.response.ST.status == ST.NeedMoreInput /\
        WS.parse_record_wire input_contents == None /\
        Seq.equal network_out old_network_out /\
        buffer_resp.ST.response.ST.app_out_len == 0sz)
      (ensures
        server_network_bridge_result
          initial
          received0
          sent0
          st0
          input_contents
          input_len
          old_network_out
          network_out
          out_len
          base
          st1
          app_out
          buffer_resp)
=
  let resp = buffer_resp.ST.response in
  let result = CTypes.server_process_result buffer_resp in
  let consumed = ST.server_network_consumed_prefix buffer_resp input_contents in
  let wire_outputs = server_response_wire_outputs resp network_out in
  let local_outputs = server_response_local_outputs resp app_out in
  assert (resp.ST.status == ST.NeedMoreInput);
  assert (st1 == st0);
  assert (buffer_resp.ST.consumed_len == 0sz);
  assert (resp.ST.network_out_len == 0sz);
  assert (resp.ST.app_out_len == 0sz);
  assert (result.CPI.process_status == CPI.NeedMoreInput);
  assert (result.CPI.process_consumed_len == 0sz);
  assert (result.CPI.process_produced_len == 0sz);
  assert (consumed == Seq.slice input_contents 0 0);
  Seq.lemma_len_slice input_contents 0 0;
  Seq.lemma_eq_intro consumed B.empty;
  assert (Seq.equal consumed B.empty);
  assert (Seq.equal consumed Seq.empty);
  assert (CPI.bounded_len input_contents input_len == B.length input_contents);
  assert (CPI.input_bytes input_contents input_len ==
    Seq.slice input_contents 0 (B.length input_contents));
  Seq.lemma_len_slice input_contents 0 (B.length input_contents);
  Seq.lemma_eq_intro (CPI.input_bytes input_contents input_len) input_contents;
  assert (Seq.equal (CPI.input_bytes input_contents input_len) input_contents);
  Seq.lemma_eq_elim (CPI.input_bytes input_contents input_len) input_contents;
  CW.lemma_wire_parse_none input_contents;
  assert (CW.tls_record_wire_format.WF.wf_parse
    (CPI.input_bytes input_contents input_len) == None);
  assert (ST.response_network_out resp network_out == Seq.slice network_out 0 0);
  Seq.lemma_len_slice network_out 0 0;
  Seq.lemma_eq_intro (ST.response_network_out resp network_out) B.empty;
  assert (Seq.equal (ST.response_network_out resp network_out) B.empty);
  Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
  CW.lemma_wire_outputs_of_empty ();
  assert (wire_outputs == []);
  assert (ST.response_app_out resp app_out == Seq.slice app_out 0 0);
  Seq.lemma_len_slice app_out 0 0;
  Seq.lemma_eq_intro (ST.response_app_out resp app_out) B.empty;
  assert (Seq.equal (ST.response_app_out resp app_out) B.empty);
  Seq.lemma_eq_elim (ST.response_app_out resp app_out) B.empty;
  assert (local_outputs == []);
  Seq.lemma_eq_elim received0 st0.CS.cs_wire_log.CL.raw_received;
  Seq.lemma_eq_elim sent0 st0.CS.cs_wire_log.CL.raw_sent;
  assert (Seq.equal st1.CS.cs_wire_log.CL.raw_received received0);
  assert (Seq.equal st1.CS.cs_wire_log.CL.raw_sent sent0);
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  assert (CPI.same_abstract_state
    received0
    sent0
    st1.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_sent
    st0
    st1);
  assert (Seq.equal network_out old_network_out);
  assert (CPI.network_process_correct
    (server_system initial)
    input_contents
    input_len
    old_network_out
    network_out
    out_len
    received0
    sent0
    st0
    result
    st1.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_sent
    st1
    consumed
    wire_outputs
    local_outputs);
  assert (server_invariant_pure
    initial
    st1.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_sent
    st1);
  assert (server_network_frame_post_fact
    base
    result
    input_contents
    input_len
    old_network_out
    network_out
    st0
    st1
    consumed
    wire_outputs
    local_outputs
    app_out
    buffer_resp);
  assert (server_network_common_witness
    initial
    received0
    sent0
    st0
    input_contents
    input_len
    old_network_out
    network_out
    out_len
    base
    st1
    app_out
    buffer_resp
    consumed
    wire_outputs
    local_outputs);
  assert (exists consumed' wire_outputs' local_outputs'.
    server_network_common_witness
      initial
      received0
      sent0
      st0
      input_contents
      input_len
      old_network_out
      network_out
      out_len
      base
      st1
      app_out
      buffer_resp
      consumed'
      wire_outputs'
      local_outputs')

let lemma_server_network_illegal_transition_bridge_result
  (initial:CS.connection_state)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (base:tls_server_network_frame)
  (st1:CS.connection_state)
  (app_out:B.bytes)
  (buffer_resp:ST.server_buffer_response)
  : Lemma
      (requires
        server_invariant_pure initial received0 sent0 st0 /\
        CPI.buffers_wf input_contents input_len old_network_out out_len /\
        B.length input_contents == SZ.v input_len /\
        B.length network_out == B.length old_network_out /\
        B.length app_out == SZ.v base.tls_server_network_app_out_len /\
        ST.server_network_bytes_end_to_end_correct
          st0
          st1
          buffer_resp
          input_contents
          network_out
          app_out /\
        ST.server_network_consumed_input_projection
          st0
          st1
          buffer_resp
          input_contents
          network_out
          app_out /\
        buffer_resp.ST.response.ST.status == ST.IllegalTransition /\
        buffer_resp.ST.response.ST.app_out_len == 0sz)
      (ensures
        server_network_bridge_result
          initial
          received0
          sent0
          st0
          input_contents
          input_len
          old_network_out
          network_out
          out_len
          base
          st1
          app_out
          buffer_resp)
=
  let resp = buffer_resp.ST.response in
  let result = CTypes.server_process_result buffer_resp in
  let consumed = ST.server_network_consumed_prefix buffer_resp input_contents in
  let wire_outputs = server_response_wire_outputs resp network_out in
  let local_outputs = server_response_local_outputs resp app_out in
  assert (resp.ST.status == ST.IllegalTransition);
  assert (st1 == st0);
  assert (buffer_resp.ST.consumed_len == 0sz);
  assert (resp.ST.network_out_len == 0sz);
  assert (resp.ST.app_out_len == 0sz);
  assert (result.CPI.process_status == CPI.IllegalTransition);
  assert (result.CPI.process_consumed_len == 0sz);
  assert (result.CPI.process_produced_len == 0sz);
  assert (consumed == Seq.slice input_contents 0 0);
  Seq.lemma_len_slice input_contents 0 0;
  Seq.lemma_eq_intro consumed B.empty;
  assert (Seq.equal consumed B.empty);
  assert (Seq.equal consumed Seq.empty);
  assert (ST.response_network_out resp network_out == Seq.slice network_out 0 0);
  Seq.lemma_len_slice network_out 0 0;
  Seq.lemma_eq_intro (ST.response_network_out resp network_out) B.empty;
  assert (Seq.equal (ST.response_network_out resp network_out) B.empty);
  Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
  CW.lemma_wire_outputs_of_empty ();
  assert (wire_outputs == []);
  assert (ST.response_app_out resp app_out == Seq.slice app_out 0 0);
  Seq.lemma_len_slice app_out 0 0;
  Seq.lemma_eq_intro (ST.response_app_out resp app_out) B.empty;
  assert (Seq.equal (ST.response_app_out resp app_out) B.empty);
  Seq.lemma_eq_elim (ST.response_app_out resp app_out) B.empty;
  assert (local_outputs == []);
  assert (CPI.network_error_refines_state_machine
    (server_system initial)
    (CPI.input_bytes input_contents input_len)
    st0
    st1
    consumed
    wire_outputs
    local_outputs);
  assert (Seq.equal
    B.empty
    (WF.serialize_all (server_system initial).WFSM.wfsm_wire_format wire_outputs));
  CPI.lemma_output_prefix_empty network_out;
  assert (CPI.output_written network_out result.CPI.process_produced_len B.empty);
  Seq.lemma_eq_elim received0 st0.CS.cs_wire_log.CL.raw_received;
  Seq.lemma_eq_elim sent0 st0.CS.cs_wire_log.CL.raw_sent;
  assert (Seq.equal st1.CS.cs_wire_log.CL.raw_received received0);
  assert (Seq.equal st1.CS.cs_wire_log.CL.raw_sent sent0);
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    (Seq.append received0 consumed));
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (Seq.append sent0 B.empty));
  assert (exists produced.
    SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
    CPI.network_error_refines_state_machine
      (server_system initial)
      (CPI.input_bytes input_contents input_len)
      st0
      st1
      consumed
      wire_outputs
      local_outputs /\
    Seq.equal
      produced
      (WF.serialize_all (server_system initial).WFSM.wfsm_wire_format wire_outputs) /\
    CPI.output_written network_out result.CPI.process_produced_len produced /\
    Seq.equal
      st1.CS.cs_wire_log.CL.raw_received
      (Seq.append received0 consumed) /\
    Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced));
  assert (CPI.network_process_correct
    (server_system initial)
    input_contents
    input_len
    old_network_out
    network_out
    out_len
    received0
    sent0
    st0
    result
    st1.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_sent
    st1
    consumed
    wire_outputs
    local_outputs);
  assert (server_invariant_pure
    initial
    st1.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_sent
    st1);
  assert (server_network_frame_post_fact
    base
    result
    input_contents
    input_len
    old_network_out
    network_out
    st0
    st1
    consumed
    wire_outputs
    local_outputs
    app_out
    buffer_resp);
  assert (server_network_common_witness
    initial
    received0
    sent0
    st0
    input_contents
    input_len
    old_network_out
    network_out
    out_len
    base
    st1
    app_out
    buffer_resp
    consumed
    wire_outputs
    local_outputs);
  assert (exists consumed' wire_outputs' local_outputs'.
    server_network_common_witness
      initial
      received0
      sent0
      st0
      input_contents
      input_len
      old_network_out
      network_out
      out_len
      base
      st1
      app_out
      buffer_resp
      consumed'
      wire_outputs'
      local_outputs')

let server_network_bridge_obligation
  (base:tls_server_network_frame)
  : prop =
  forall initial received0 sent0 st0 input_contents input_len old_network_out
         network_out out_len st1 app_out buffer_resp.
    server_invariant_pure initial received0 sent0 st0 /\
    CPI.buffers_wf input_contents input_len old_network_out out_len /\
    B.length input_contents == SZ.v input_len /\
    B.length network_out == B.length old_network_out /\
    B.length app_out == SZ.v base.tls_server_network_app_out_len /\
    ST.server_network_bytes_end_to_end_correct
      st0
      st1
      buffer_resp
      input_contents
      network_out
      app_out /\
    ST.server_network_consumed_input_projection
      st0
      st1
      buffer_resp
      input_contents
      network_out
      app_out /\
    (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
      WS.parse_record_wire input_contents == None)
    ==> server_network_bridge_result
          initial
          received0
          sent0
          st0
          input_contents
          input_len
          old_network_out
          network_out
          out_len
          base
          st1
          app_out
          buffer_resp

noeq
type tls_server_network_bridge_frame = {
  tls_server_network_bridge_base: tls_server_network_frame;
  tls_server_network_bridge_proof:
    Ghost.erased
      (server_network_bridge_obligation tls_server_network_bridge_base);
}

let lemma_server_network_bridge_frame_obligation
  (frame:tls_server_network_bridge_frame)
  : Lemma
      (ensures
        server_network_bridge_obligation frame.tls_server_network_bridge_base)
=
  let _ = Ghost.reveal frame.tls_server_network_bridge_proof in
  ()

[@@pulse_unfold]
let server_network_bridge_frame_pre
  (frame:tls_server_network_bridge_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (input_contents:B.bytes)
  (old_network_out:B.bytes)
  : slprop =
  server_network_frame_pre
    frame.tls_server_network_bridge_base
    input
    input_len
    out
    out_len
    input_contents
    old_network_out

let server_network_bridge_frame_post
  (frame:tls_server_network_bridge_frame)
  (result:CPI.process_result)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (consumed:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  : slprop =
  exists* (app_out:B.bytes).
    pts_to
      frame.tls_server_network_bridge_base.tls_server_network_app_out
      app_out **
    pure (
      B.length app_out ==
        SZ.v frame.tls_server_network_bridge_base.tls_server_network_app_out_len)

let server_local_api_frame_post_fact
  (api:CTypes.server_api_event)
  (frame:tls_server_local_frame)
  (result:CPI.process_result)
  (_old_network_out:B.bytes)
  (network_out:B.bytes)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  (app_out:B.bytes)
  (resp:ST.server_response)
  : prop =
  result == CTypes.server_local_process_result resp /\
  ST.server_local_event_end_to_end_correct
    st0
    st1
    resp
    api.CTypes.server_local_kind
    api.CTypes.server_local_payload
    network_out
    app_out /\
  wire_outputs ==
    server_response_wire_outputs resp network_out /\
  local_outputs ==
    server_response_local_outputs resp app_out

let server_local_common_witness
  (initial:CS.connection_state)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (local_ev:CTypes.server_local_event)
  (api:CTypes.server_api_event)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (base:tls_server_local_frame)
  (st1:CS.connection_state)
  (app_out:B.bytes)
  (resp:ST.server_response)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  : prop =
  let result = CTypes.server_local_process_result resp in
  let received1 = st1.CS.cs_wire_log.CL.raw_received in
  let sent1 = st1.CS.cs_wire_log.CL.raw_sent in
  server_invariant_pure initial received1 sent1 st1 /\
  api == CTypes.server_local_event_api local_ev /\
  server_local_api_frame_post_fact
    api
    base
    result
    old_network_out
    network_out
    st0
    st1
    wire_outputs
    local_outputs
    app_out
    resp /\
  CPI.local_process_correct
    (server_system initial)
    local_ev
    old_network_out
    network_out
    out_len
    received0
    sent0
    st0
    result
    received1
    sent1
    st1
    wire_outputs
    local_outputs

let server_local_bridge_result
  (initial:CS.connection_state)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (local_ev:CTypes.server_local_event)
  (api:CTypes.server_api_event)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (base:tls_server_local_frame)
  (st1:CS.connection_state)
  (app_out:B.bytes)
  (resp:ST.server_response)
  : prop =
  exists wire_outputs local_outputs.
    server_local_common_witness
      initial
      received0
      sent0
      st0
      local_ev
      api
      old_network_out
      network_out
      out_len
      base
      st1
      app_out
      resp
      wire_outputs
      local_outputs

let server_local_bridge_obligation
  (base:tls_server_local_frame)
  : prop =
  forall initial received0 sent0 st0 local_ev api old_network_out network_out out_len
         st1 app_out resp.
    server_invariant_pure initial received0 sent0 st0 /\
    api == CTypes.server_local_event_api local_ev /\
    SZ.v out_len == B.length old_network_out /\
    B.length network_out == B.length old_network_out /\
    B.length app_out == SZ.v base.tls_server_local_app_out_len /\
    B.length api.CTypes.server_local_payload ==
      SZ.v base.tls_server_local_payload_len /\
    ST.server_local_event_input_ready
      st0
      api.CTypes.server_local_kind
      api.CTypes.server_local_payload /\
    ST.server_local_event_end_to_end_correct
      st0
      st1
      resp
      api.CTypes.server_local_kind
      api.CTypes.server_local_payload
      network_out
      app_out
    ==> server_local_bridge_result
          initial
          received0
          sent0
          st0
          local_ev
          api
          old_network_out
          network_out
          out_len
          base
          st1
          app_out
          resp

noeq
type tls_server_local_bridge_frame = {
  tls_server_local_bridge_base: tls_server_local_frame;
  tls_server_local_bridge_proof:
    Ghost.erased
      (server_local_bridge_obligation tls_server_local_bridge_base);
}

let lemma_server_local_bridge_frame_obligation
  (frame:tls_server_local_bridge_frame)
  : Lemma
      (ensures
        server_local_bridge_obligation frame.tls_server_local_bridge_base)
=
  let _ = Ghost.reveal frame.tls_server_local_bridge_proof in
  ()

[@@pulse_unfold]
let server_local_bridge_frame_pre
  (ev:CTypes.server_local_event)
  (frame:tls_server_local_bridge_frame)
  (st0:CS.connection_state)
  (out:array U8.t)
  (out_len:SZ.t)
  (old_network_out:B.bytes)
  : slprop =
  server_local_frame_pre
    ev
    frame.tls_server_local_bridge_base
    st0
    out
    out_len
    old_network_out

let server_local_bridge_frame_post
  (ev:CTypes.server_local_event)
  (frame:tls_server_local_bridge_frame)
  (result:CPI.process_result)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  : slprop =
  let api = CTypes.server_local_event_api ev in
  exists* (app_out:B.bytes).
    pts_to
      frame.tls_server_local_bridge_base.tls_server_local_payload
      api.CTypes.server_local_payload **
    pts_to
      frame.tls_server_local_bridge_base.tls_server_local_app_out
      app_out **
    pure (
      B.length app_out ==
        SZ.v frame.tls_server_local_bridge_base.tls_server_local_app_out_len)

let server_process_network_post
  (srv:canonical_server)
  (frame:tls_server_network_bridge_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased B.bytes)
  (sent0:erased B.bytes)
  (st0:erased CS.connection_state)
  (input_contents:erased B.bytes)
  (old_out:erased B.bytes)
  (result:CPI.process_result)
  : slprop =
  exists* (received1:Ghost.erased B.bytes)
          (sent1:Ghost.erased B.bytes)
          (st1:Ghost.erased CS.connection_state)
          (out_contents:B.bytes)
          (consumed:B.bytes)
          (wire_outputs:list CW.wire_message)
          (local_outputs:list CTypes.local_output).
    server_invariant
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    server_network_bridge_frame_post
      frame
      result
      (Ghost.reveal input_contents)
      input_len
      (Ghost.reveal old_out)
      out_contents
      (Ghost.reveal st0)
      (Ghost.reveal st1)
      consumed
      wire_outputs
      local_outputs **
    pts_to input (Ghost.reveal input_contents) **
    pts_to out out_contents **
    pure (
      CPI.network_process_correct
        (server_system (Ghost.reveal srv.canonical_server_initial))
        (Ghost.reveal input_contents)
        input_len
        (Ghost.reveal old_out)
        out_contents
        out_len
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)
        result
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1)
        consumed
        wire_outputs
        local_outputs)

// Prove server_canonical_step_rel st0 st1 in the non-StepOk, st1 <> st0 case for
// the network handler.  Mirrors lemma_client_network_nonstep_canonical_step in
// TLS13.Impl.Client.CanonicalProtocol.fst.
let lemma_server_network_nonstep_canonical_step
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:ST.server_buffer_response)
  (input_contents:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        buffer_resp.ST.response.ST.status <> ST.StepOk /\
        st1 <> st0 /\
        ST.server_network_bytes_end_to_end_correct
          st0 st1 buffer_resp input_contents network_out app_out /\
        ST.server_network_consumed_input_projection
          st0 st1 buffer_resp input_contents network_out app_out)
      (ensures server_canonical_step_rel st0 st1)
  =
  let resp = buffer_resp.ST.response in
  // Inner helper: construct a LocalFail canonical step from a legal_connection_delta.
  let lemma_localfail_step
    (err:T.tls_error)
    (conn_ev:CS.conn_event)
    : Lemma
        (requires
          conn_ev == CS.ConnLocalEvent (CS.LocalFail err) /\
          CS.legal_connection_delta st0 {
            CS.delta_event = conn_ev;
            CS.delta_raw_sent = B.empty;
            CS.delta_raw_received = B.empty;
          } st1)
        (ensures server_canonical_step_rel st0 st1)
    =
    CW.lemma_wire_outputs_of_empty ();
    Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format []) B.empty;
    let api : CTypes.server_api_event = {
      CTypes.server_local_kind = ST.LocalFail;
      CTypes.server_local_payload = B.empty;
    } in
    assert (server_api_event_matches api conn_ev);
    assert (server_wire_outputs_match B.empty []);
    assert (server_local_outputs_match conn_ev []);
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format [];
      CS.delta_raw_received = B.empty;
    } st1);
    assert (B.length (WF.serialize_all CW.tls_record_wire_format []) == 0);
    assert (CS.sent_event_nonempty_seal_projection
      st0.CS.cs_model
      conn_ev
      (WF.serialize_all CW.tls_record_wire_format []));
    assert (B.length B.empty == 0);
    assert (CS.received_event_nonempty_decode_projection
      st0.CS.cs_model
      conn_ev
      B.empty);
    assert (server_step st0 (SM.LocalEvent (CTypes.ServerAPI api)) st1 (CPI.step_output [] []))
  in
  if resp.ST.status = ST.DecodeError then (
    // DecodeError → LocalFail (tls_decode_error)
    assert (ST.decode_error_response st0 st1 resp network_out app_out);
    let decode_err : T.tls_error = T.AlertError T.DecodeError in
    let conn_ev = CS.ConnLocalEvent (CS.LocalFail decode_err) in
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    } st1);
    lemma_localfail_step decode_err conn_ev
  ) else (
    // NeedMoreInput and IllegalTransition give st1 == st0 → contradicts st1 <> st0.
    // OutputBufferTooSmall gives False.
    // So must be ConnectionFailed.
    assert (resp.ST.status = ST.ConnectionFailed);
    assert (ST.server_network_connection_failed_consumed_prefix
      st0 st1 buffer_resp input_contents network_out app_out);
    let alert =
      ID.indefinite_description_ghost
        T.alert_description
        (fun alert -> exists raw_received.
          Seq.equal raw_received (ST.server_network_consumed_prefix buffer_resp input_contents) /\
          ST.legal_network_response st0 st1 resp (M.TlsAlert alert) raw_received network_out app_out /\
          CS.received_event_nonempty_decode_projection
            st0.CS.cs_model
            (ST.received_message_event (M.TlsAlert alert))
            raw_received) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          Seq.equal raw_received (ST.server_network_consumed_prefix buffer_resp input_contents) /\
          ST.legal_network_response st0 st1 resp (M.TlsAlert alert) raw_received network_out app_out /\
          CS.received_event_nonempty_decode_projection
            st0.CS.cs_model
            (ST.received_message_event (M.TlsAlert alert))
            raw_received) in
    assert (ST.legal_network_response st0 st1 resp (M.TlsAlert alert) raw_received network_out app_out);
    assert (ST.legal_response_for_event st0 st1 resp
      (ST.received_message_event (M.TlsAlert alert))
      B.empty
      raw_received
      network_out
      app_out);
    assert (CT.received_tls_raw_delta_legal st0 (M.TlsAlert alert) raw_received);
    lemma_received_tls_raw_delta_legal_raw_record_parse_success st0 (M.TlsAlert alert) raw_received;
    assert (CT.raw_record_parse_success raw_received);
    let outer_ct =
      ID.indefinite_description_ghost
        T.content_type
        (fun outer_ct -> exists outer_fragment.
          WS.parse_record_wire raw_received ==
            Some (outer_ct, outer_fragment, B.length raw_received)) in
    let outer_fragment =
      ID.indefinite_description_ghost
        B.bytes
        (fun outer_fragment ->
          WS.parse_record_wire raw_received ==
            Some (outer_ct, outer_fragment, B.length raw_received)) in
    let wire : CW.wire_message = {
      CW.wm_raw = raw_received;
      CW.wm_content_type = outer_ct;
      CW.wm_fragment = outer_fragment;
      CW.wm_parse_ok = ();
    } in
    assert (CW.wire_serialize wire == raw_received);
    assert (SZ.v resp.ST.network_out_len == 0);
    Seq.lemma_len_slice network_out 0 0;
    Seq.lemma_eq_intro (ST.response_network_out resp network_out) B.empty;
    assert (Seq.equal (ST.response_network_out resp network_out) B.empty);
    CW.lemma_wire_outputs_of_empty ();
    Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format []) B.empty;
    let conn_ev = ST.received_message_event (M.TlsAlert alert) in
    let local_outputs = server_response_local_outputs resp app_out in
    lemma_server_response_local_outputs_match resp conn_ev app_out;
    assert (server_local_outputs_match conn_ev local_outputs);
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format [];
      CS.delta_raw_received = CW.wire_serialize wire;
    } st1);
    assert (B.length (WF.serialize_all CW.tls_record_wire_format []) == 0);
    assert (CS.sent_event_nonempty_seal_projection
      st0.CS.cs_model
      conn_ev
      (WF.serialize_all CW.tls_record_wire_format []));
    assert (CS.received_event_nonempty_decode_projection
      st0.CS.cs_model
      conn_ev
      raw_received);
    assert (CS.received_event_nonempty_decode_projection
      st0.CS.cs_model
      conn_ev
      (CW.wire_serialize wire));
    assert (server_step st0 (SM.WireEvent wire) st1 (CPI.step_output [] local_outputs));
    assert (server_canonical_step_rel st0 st1)
  )

// Prove server_progress_preorder st0 st1 from server_network_common_witness.
// Mirrors lemma_client_network_common_witness_progress.
let lemma_server_network_common_witness_progress
  (initial:CS.connection_state)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (base:tls_server_network_frame)
  (st1:CS.connection_state)
  (app_out:B.bytes)
  (buffer_resp:ST.server_buffer_response)
  (consumed:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  : Lemma
      (requires
        server_network_common_witness
          initial received0 sent0 st0 input_contents input_len
          old_network_out network_out out_len base st1 app_out buffer_resp
          consumed wire_outputs local_outputs)
      (ensures server_progress_preorder st0 st1)
  =
  let result = CTypes.server_process_result buffer_resp in
  if result.CPI.process_status = CPI.StepOk then (
    CPI.lemma_network_process_ok_refines_transition
      (server_system initial)
      input_contents
      input_len
      old_network_out
      network_out
      out_len
      received0
      sent0
      st0
      result
      st1.CS.cs_wire_log.CL.raw_received
      st1.CS.cs_wire_log.CL.raw_sent
      st1
      consumed
      wire_outputs
      local_outputs;
    assert (exists msg residual produced.
      CPI.consumed_by_parse
        (server_system initial).WFSM.wfsm_wire_format
        (CPI.input_bytes input_contents input_len)
        msg
        consumed
        residual /\
      SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
      (server_system initial).WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.WireEvent msg)
        st1
        (CPI.step_output wire_outputs local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all (server_system initial).WFSM.wfsm_wire_format wire_outputs) /\
      CPI.output_written network_out result.CPI.process_produced_len produced /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_received (Seq.append received0 consumed) /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced));
    let msg =
      ID.indefinite_description_ghost
        CW.wire_message
        (fun msg -> exists residual produced.
          CPI.consumed_by_parse
            (server_system initial).WFSM.wfsm_wire_format
            (CPI.input_bytes input_contents input_len)
            msg
            consumed
            residual /\
          SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
          (server_system initial).WFSM.wfsm_state_machine.SM.sm_step
            st0
            (SM.WireEvent msg)
            st1
            (CPI.step_output wire_outputs local_outputs) /\
          Seq.equal
            produced
            (WF.serialize_all (server_system initial).WFSM.wfsm_wire_format wire_outputs) /\
          CPI.output_written network_out result.CPI.process_produced_len produced /\
          Seq.equal st1.CS.cs_wire_log.CL.raw_received (Seq.append received0 consumed) /\
          Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced)) in
    assert (server_step
      st0
      (SM.WireEvent msg)
      st1
      (CPI.step_output wire_outputs local_outputs));
    assert (server_canonical_step_rel st0 st1);
    RTC.closure_step server_canonical_step_rel st0 st1
  ) else (
    if st1 = st0 then
      assert (server_progress_preorder st0 st1)
    else (
      assert (buffer_resp.ST.response.ST.status <> ST.StepOk);
      lemma_server_network_nonstep_canonical_step
        st0 st1 buffer_resp input_contents network_out app_out;
      RTC.closure_step server_canonical_step_rel st0 st1
    )
  )

// Prove server_progress_preorder st0 st1 from server_local_common_witness.
// Mirrors lemma_client_local_progress in TLS13.Impl.Client.CanonicalProtocol.fst.
let lemma_server_local_progress
  (initial:CS.connection_state)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (local_ev:CTypes.server_local_event)
  (api:CTypes.server_api_event)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (base:tls_server_local_frame)
  (st1:CS.connection_state)
  (app_out:B.bytes)
  (resp:ST.server_response)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  : Lemma
      (requires
        server_local_common_witness
          initial received0 sent0 st0 local_ev api old_network_out
          network_out out_len base st1 app_out resp wire_outputs local_outputs)
      (ensures server_progress_preorder st0 st1)
  =
  let result = CTypes.server_local_process_result resp in
  let received1 = st1.CS.cs_wire_log.CL.raw_received in
  let sent1 = st1.CS.cs_wire_log.CL.raw_sent in
  if result.CPI.process_status = CPI.StepOk then (
    CPI.lemma_local_process_ok_refines_transition
      (server_system initial)
      local_ev
      old_network_out
      network_out
      out_len
      received0
      sent0
      st0
      result
      received1
      sent1
      st1
      wire_outputs
      local_outputs;
    assert (server_step
      st0
      (SM.LocalEvent local_ev)
      st1
      (CPI.step_output wire_outputs local_outputs));
    assert (server_canonical_step_rel st0 st1);
    RTC.closure_step server_canonical_step_rel st0 st1
  ) else (
    // result.process_status != StepOk → resp.status != StepOk.
    // From server_local_event_end_to_end_correct → legal_handled_local_response.
    // legal_local_response requires resp.status == StepOk → contradiction.
    // So unexpected_message_response holds.
    assert (resp.ST.status <> ST.StepOk);
    assert (ST.unexpected_message_response st0 st1 resp network_out app_out);
    let err : T.tls_error = T.AlertError T.UnexpectedMessage in
    let conn_ev = CS.ConnLocalEvent (CS.LocalFail err) in
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    } st1);
    if st0 = st1 then
      assert (server_progress_preorder st0 st1)
    else (
      CW.lemma_wire_outputs_of_empty ();
      Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format []) B.empty;
      let api_fail : CTypes.server_api_event = {
        CTypes.server_local_kind = ST.LocalFail;
        CTypes.server_local_payload = B.empty;
      } in
      assert (server_api_event_matches api_fail conn_ev);
      assert (server_wire_outputs_match B.empty []);
      assert (server_local_outputs_match conn_ev []);
      assert (CS.legal_connection_delta st0 {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format [];
        CS.delta_raw_received = B.empty;
      } st1);
      assert (server_step st0 (SM.LocalEvent (CTypes.ServerAPI api_fail)) st1 (CPI.step_output [] []));
      assert (server_canonical_step_rel st0 st1);
      RTC.closure_step server_canonical_step_rel st0 st1
    )
  )

fn server_process_network
  (srv:canonical_server)
  (frame:tls_server_network_bridge_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased B.bytes)
  (sent0:erased B.bytes)
  (st0:erased CS.connection_state)
  (input_contents:erased B.bytes)
  (old_out:erased B.bytes)
requires
  server_invariant
    srv
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0) **
  server_network_bridge_frame_pre
    frame
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out) **
  pts_to input (Ghost.reveal input_contents) **
  pts_to out (Ghost.reveal old_out) **
  pure (CPI.buffers_wf (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len)
returns result:CPI.process_result
ensures server_process_network_post
  srv
  frame
  input
  input_len
  out
  out_len
  received0
  sent0
  st0
  input_contents
  old_out
  result
{
  unfold (server_invariant
    srv
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0));
  with certificate_chain credential_identity. _;
  unfold (server_network_bridge_frame_pre
    frame
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out));
  unfold (server_network_frame_pre
    frame.tls_server_network_bridge_base
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out));
  let buffer_resp =
    S.process_network_bytes
      srv.canonical_server_state
      input
      input_len
      out
      out_len
      frame.tls_server_network_bridge_base.tls_server_network_app_out
      frame.tls_server_network_bridge_base.tls_server_network_app_out_len;
  with st1 network_out_bytes app_out_bytes. _;
  assert (pure (server_invariant_pure
    (Ghost.reveal srv.canonical_server_initial)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)));
  assert (pure (B.length network_out_bytes == SZ.v out_len));
  assert (pure (B.length app_out_bytes ==
    SZ.v frame.tls_server_network_bridge_base.tls_server_network_app_out_len));
  assert (pure (CPI.buffers_wf
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    out_len));
  assert (pure (B.length network_out_bytes == B.length (Ghost.reveal old_out)));
  assert (pure (B.length (Ghost.reveal input_contents) == SZ.v input_len));
  assert (pure (ST.server_network_bytes_end_to_end_correct
    (Ghost.reveal st0)
    st1
    buffer_resp
    (Ghost.reveal input_contents)
    network_out_bytes
    app_out_bytes));
  assert (pure (ST.server_network_consumed_input_projection
    (Ghost.reveal st0)
    st1
    buffer_resp
    (Ghost.reveal input_contents)
    network_out_bytes
    app_out_bytes));
  assert (pure (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
    WS.parse_record_wire (Ghost.reveal input_contents) == None));
  lemma_server_network_bridge_frame_obligation frame;
  assert (pure (server_network_bridge_obligation
    frame.tls_server_network_bridge_base));
  assert (pure (server_network_bridge_result
    (Ghost.reveal srv.canonical_server_initial)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    network_out_bytes
    out_len
    frame.tls_server_network_bridge_base
    st1
    app_out_bytes
    buffer_resp));
  let consumede : Ghost.erased (consumed:B.bytes{
    exists (wire_outputs:list CW.wire_message).
    exists (local_outputs:list CTypes.local_output).
      server_network_common_witness
        (Ghost.reveal srv.canonical_server_initial)
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)
        (Ghost.reveal input_contents)
        input_len
        (Ghost.reveal old_out)
        network_out_bytes
        out_len
        frame.tls_server_network_bridge_base
        st1
        app_out_bytes
        buffer_resp
        consumed
        wire_outputs
        local_outputs
  }) = Ghost.hide (
    FStar.IndefiniteDescription.indefinite_description_ghost
      B.bytes
      (fun consumed -> (
        exists (wire_outputs:list CW.wire_message).
        exists (local_outputs:list CTypes.local_output).
        server_network_common_witness
          (Ghost.reveal srv.canonical_server_initial)
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0)
          (Ghost.reveal input_contents)
          input_len
          (Ghost.reveal old_out)
          network_out_bytes
          out_len
          frame.tls_server_network_bridge_base
          st1
          app_out_bytes
          buffer_resp
          consumed
          wire_outputs
          local_outputs)));
  assert (pure (exists (wire_outputs:list CW.wire_message).
    exists (local_outputs:list CTypes.local_output).
      server_network_common_witness
        (Ghost.reveal srv.canonical_server_initial)
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)
        (Ghost.reveal input_contents)
        input_len
        (Ghost.reveal old_out)
        network_out_bytes
        out_len
        frame.tls_server_network_bridge_base
        st1
        app_out_bytes
        buffer_resp
        (Ghost.reveal consumede)
        wire_outputs
        local_outputs));
  let wire_outputse : Ghost.erased (wire_outputs:list CW.wire_message{
    exists (local_outputs:list CTypes.local_output).
      server_network_common_witness
        (Ghost.reveal srv.canonical_server_initial)
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)
        (Ghost.reveal input_contents)
        input_len
        (Ghost.reveal old_out)
        network_out_bytes
        out_len
        frame.tls_server_network_bridge_base
        st1
        app_out_bytes
        buffer_resp
        (Ghost.reveal consumede)
        wire_outputs
        local_outputs
  }) = Ghost.hide (
    FStar.IndefiniteDescription.indefinite_description_ghost
      (list CW.wire_message)
      (fun wire_outputs -> (
        exists (local_outputs:list CTypes.local_output).
        server_network_common_witness
          (Ghost.reveal srv.canonical_server_initial)
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0)
          (Ghost.reveal input_contents)
          input_len
          (Ghost.reveal old_out)
          network_out_bytes
          out_len
          frame.tls_server_network_bridge_base
          st1
          app_out_bytes
          buffer_resp
          (Ghost.reveal consumede)
          wire_outputs
          local_outputs)));
  assert (pure (exists (local_outputs:list CTypes.local_output).
    server_network_common_witness
      (Ghost.reveal srv.canonical_server_initial)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      (Ghost.reveal input_contents)
      input_len
      (Ghost.reveal old_out)
      network_out_bytes
      out_len
      frame.tls_server_network_bridge_base
      st1
      app_out_bytes
      buffer_resp
      (Ghost.reveal consumede)
      (Ghost.reveal wire_outputse)
      local_outputs));
  let local_outputse : Ghost.erased (local_outputs:list CTypes.local_output{
    server_network_common_witness
      (Ghost.reveal srv.canonical_server_initial)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      (Ghost.reveal input_contents)
      input_len
      (Ghost.reveal old_out)
      network_out_bytes
      out_len
      frame.tls_server_network_bridge_base
      st1
      app_out_bytes
      buffer_resp
      (Ghost.reveal consumede)
      (Ghost.reveal wire_outputse)
      local_outputs
  }) = Ghost.hide (
    FStar.IndefiniteDescription.indefinite_description_ghost
      (list CTypes.local_output)
      (fun local_outputs ->
        server_network_common_witness
          (Ghost.reveal srv.canonical_server_initial)
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0)
          (Ghost.reveal input_contents)
          input_len
          (Ghost.reveal old_out)
          network_out_bytes
          out_len
          frame.tls_server_network_bridge_base
          st1
          app_out_bytes
          buffer_resp
          (Ghost.reveal consumede)
          (Ghost.reveal wire_outputse)
          local_outputs));
  assert (pure (server_network_common_witness
    (Ghost.reveal srv.canonical_server_initial)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    network_out_bytes
    out_len
    frame.tls_server_network_bridge_base
    st1
    app_out_bytes
    buffer_resp
    (Ghost.reveal consumede)
    (Ghost.reveal wire_outputse)
    (Ghost.reveal local_outputse)));
  let received1e : Ghost.erased B.bytes =
    Ghost.hide st1.CS.cs_wire_log.CL.raw_received;
  let sent1e : Ghost.erased B.bytes =
    Ghost.hide st1.CS.cs_wire_log.CL.raw_sent;
  let st1e : Ghost.erased CS.connection_state = Ghost.hide st1;
  assert (pure ((Ghost.reveal received1e) == st1.CS.cs_wire_log.CL.raw_received));
  assert (pure ((Ghost.reveal sent1e) == st1.CS.cs_wire_log.CL.raw_sent));
  assert (pure ((Ghost.reveal st1e) == st1));
  assert (pure (server_invariant_pure
    (Ghost.reveal srv.canonical_server_initial)
    (Ghost.reveal received1e)
    (Ghost.reveal sent1e)
    (Ghost.reveal st1e)));
  rewrite (S.connection_exactly srv.canonical_server_state st1) as
    (S.connection_exactly srv.canonical_server_state (Ghost.reveal st1e));
  // Prove monotonicity of progress before folding the invariant.
  lemma_server_network_common_witness_progress
    (Ghost.reveal srv.canonical_server_initial)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    network_out_bytes
    out_len
    frame.tls_server_network_bridge_base
    (Ghost.reveal st1e)
    app_out_bytes
    buffer_resp
    (Ghost.reveal consumede)
    (Ghost.reveal wire_outputse)
    (Ghost.reveal local_outputse);
  MR.update srv.canonical_server_progress (Ghost.reveal st1e);
  with app_out_bytes.
  fold (server_network_bridge_frame_post
    frame
    (CTypes.server_process_result buffer_resp)
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    network_out_bytes
    (Ghost.reveal st0)
    (Ghost.reveal st1e)
    (Ghost.reveal consumede)
    (Ghost.reveal wire_outputse)
    (Ghost.reveal local_outputse));
  with certificate_chain credential_identity.
  fold (server_invariant
    srv
    (Ghost.reveal received1e)
    (Ghost.reveal sent1e)
    (Ghost.reveal st1e));
  assert (pure (CPI.network_process_correct
    (server_system (Ghost.reveal srv.canonical_server_initial))
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    network_out_bytes
    out_len
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    (CTypes.server_process_result buffer_resp)
    (Ghost.reveal received1e)
    (Ghost.reveal sent1e)
    (Ghost.reveal st1e)
    (Ghost.reveal consumede)
    (Ghost.reveal wire_outputse)
    (Ghost.reveal local_outputse)));
  with received1e sent1e st1e network_out_bytes consumede wire_outputse local_outputse.
  fold (server_process_network_post
    srv
    frame
    input
    input_len
    out
    out_len
    received0
    sent0
    st0
    input_contents
    old_out
    (CTypes.server_process_result buffer_resp));
  CTypes.server_process_result buffer_resp
}

let server_process_local_post
  (srv:canonical_server)
  (ev:CTypes.server_local_event)
  (frame:tls_server_local_bridge_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased B.bytes)
  (sent0:erased B.bytes)
  (st0:erased CS.connection_state)
  (old_out:erased B.bytes)
  (result:CPI.process_result)
  : slprop =
  exists* (received1:Ghost.erased B.bytes)
          (sent1:Ghost.erased B.bytes)
          (st1:Ghost.erased CS.connection_state)
          (out_contents:B.bytes)
          (wire_outputs:list CW.wire_message)
          (local_outputs:list CTypes.local_output).
    server_invariant
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    server_local_bridge_frame_post
      ev
      frame
      result
      (Ghost.reveal old_out)
      out_contents
      (Ghost.reveal st0)
      (Ghost.reveal st1)
      wire_outputs
      local_outputs **
    pts_to out out_contents **
    pure (
      CPI.local_process_correct
        (server_system (Ghost.reveal srv.canonical_server_initial))
        ev
        (Ghost.reveal old_out)
        out_contents
        out_len
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)
        result
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1)
        wire_outputs
        local_outputs)

fn server_process_local
  (srv:canonical_server)
  (ev:CTypes.server_local_event)
  (frame:tls_server_local_bridge_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased B.bytes)
  (sent0:erased B.bytes)
  (st0:erased CS.connection_state)
  (old_out:erased B.bytes)
requires
  server_invariant
    srv
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0) **
  server_local_bridge_frame_pre
    ev
    frame
    (Ghost.reveal st0)
    out
    out_len
    (Ghost.reveal old_out) **
  pts_to out (Ghost.reveal old_out) **
  pure (SZ.v out_len == Seq.length (Ghost.reveal old_out))
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased B.bytes)
                (sent1:Ghost.erased B.bytes)
                (st1:Ghost.erased CS.connection_state)
                (out_contents:B.bytes)
                (wire_outputs:list CW.wire_message)
                (local_outputs:list CTypes.local_output).
  server_invariant
    srv
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1) **
  server_local_bridge_frame_post
    ev
    frame
    result
    (Ghost.reveal old_out)
    out_contents
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    wire_outputs
    local_outputs **
  pts_to out out_contents **
  pure (
    CPI.local_process_correct
      (server_system (Ghost.reveal srv.canonical_server_initial))
      ev
      (Ghost.reveal old_out)
      out_contents
      out_len
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      wire_outputs
      local_outputs)
{
  unfold (server_invariant
    srv
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0));
  with certificate_chain credential_identity. _;
  unfold (server_local_bridge_frame_pre
    ev
    frame
    (Ghost.reveal st0)
    out
    out_len
    (Ghost.reveal old_out));
  unfold (server_local_frame_pre
    ev
    frame.tls_server_local_bridge_base
    (Ghost.reveal st0)
    out
    out_len
    (Ghost.reveal old_out));
  let kind = CTypes.server_local_event_kind ev;
  let api:Ghost.erased CTypes.server_api_event =
    Ghost.hide (CTypes.server_local_event_api ev);
  assert (pure ((Ghost.reveal api) == CTypes.server_local_event_api ev));
  assert (pure (kind == (Ghost.reveal api).CTypes.server_local_kind));
  assert (pure (server_config_matches_credentials
    (Ghost.reveal srv.canonical_server_initial)
    certificate_chain
    credential_identity));
  assert (pure (
    (Ghost.reveal st0).CS.cs_model.CS.model_config ==
      (Ghost.reveal srv.canonical_server_initial).CS.cs_model.CS.model_config));
  assert (pure (Some?
    (Ghost.reveal st0).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (
    (Some?.v (Ghost.reveal st0).CS.cs_model.CS.model_config.CS.config_server)
      .CS.server_certificate_chain == certificate_chain /\
    (Some?.v (Ghost.reveal st0).CS.cs_model.CS.model_config.CS.config_server)
      .CS.server_credential_identity == credential_identity));
  ST.server_local_event_input_ready_with_state_credentials
    (Ghost.reveal st0)
    kind
    (Ghost.reveal api).CTypes.server_local_payload
    certificate_chain
    credential_identity;
  assert (pure (ST.server_local_event_input_ready_with_credentials
    (Ghost.reveal st0)
    kind
    (Ghost.reveal api).CTypes.server_local_payload
    certificate_chain
    credential_identity));
  let resp =
    S.process_local_event_with_credentials
      srv.canonical_server_state
      srv.canonical_server_credentials
      kind
      frame.tls_server_local_bridge_base.tls_server_local_payload
      frame.tls_server_local_bridge_base.tls_server_local_payload_len
      out
      out_len
      frame.tls_server_local_bridge_base.tls_server_local_app_out
      frame.tls_server_local_bridge_base.tls_server_local_app_out_len;
      with st1 network_out_bytes app_out_bytes. _;
      assert (pure (server_invariant_pure
        (Ghost.reveal srv.canonical_server_initial)
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)));
      assert (pure (B.length network_out_bytes == SZ.v out_len));
      assert (pure (B.length app_out_bytes ==
        SZ.v frame.tls_server_local_bridge_base.tls_server_local_app_out_len));
      assert (pure (B.length network_out_bytes == B.length (Ghost.reveal old_out)));
      assert (pure (B.length (Ghost.reveal api).CTypes.server_local_payload ==
        SZ.v frame.tls_server_local_bridge_base.tls_server_local_payload_len));
      assert (pure (ST.server_local_event_input_ready
        (Ghost.reveal st0)
        (Ghost.reveal api).CTypes.server_local_kind
        (Ghost.reveal api).CTypes.server_local_payload));
      assert (pure (ST.server_local_event_end_to_end_correct
        (Ghost.reveal st0)
        st1
        resp
        (Ghost.reveal api).CTypes.server_local_kind
        (Ghost.reveal api).CTypes.server_local_payload
        network_out_bytes
        app_out_bytes));
      lemma_server_local_bridge_frame_obligation frame;
      assert (pure (server_local_bridge_obligation
        frame.tls_server_local_bridge_base));
      assert (pure (server_local_bridge_result
        (Ghost.reveal srv.canonical_server_initial)
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)
        ev
        (Ghost.reveal api)
        (Ghost.reveal old_out)
        network_out_bytes
        out_len
        frame.tls_server_local_bridge_base
        st1
        app_out_bytes
        resp));
      let wire_outputse : Ghost.erased (wire_outputs:list CW.wire_message{
        exists (local_outputs:list CTypes.local_output).
          server_local_common_witness
            (Ghost.reveal srv.canonical_server_initial)
            (Ghost.reveal received0)
            (Ghost.reveal sent0)
            (Ghost.reveal st0)
            ev
            (Ghost.reveal api)
            (Ghost.reveal old_out)
            network_out_bytes
            out_len
            frame.tls_server_local_bridge_base
            st1
            app_out_bytes
            resp
            wire_outputs
            local_outputs
      }) = Ghost.hide (
        FStar.IndefiniteDescription.indefinite_description_ghost
          (list CW.wire_message)
          (fun wire_outputs -> (
            exists (local_outputs:list CTypes.local_output).
            server_local_common_witness
              (Ghost.reveal srv.canonical_server_initial)
              (Ghost.reveal received0)
              (Ghost.reveal sent0)
              (Ghost.reveal st0)
              ev
              (Ghost.reveal api)
              (Ghost.reveal old_out)
              network_out_bytes
              out_len
              frame.tls_server_local_bridge_base
              st1
              app_out_bytes
              resp
              wire_outputs
              local_outputs)));
      assert (pure (exists (local_outputs:list CTypes.local_output).
        server_local_common_witness
          (Ghost.reveal srv.canonical_server_initial)
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0)
          ev
          (Ghost.reveal api)
          (Ghost.reveal old_out)
          network_out_bytes
          out_len
          frame.tls_server_local_bridge_base
          st1
          app_out_bytes
          resp
          (Ghost.reveal wire_outputse)
          local_outputs));
      let local_outputse : Ghost.erased (local_outputs:list CTypes.local_output{
        server_local_common_witness
          (Ghost.reveal srv.canonical_server_initial)
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0)
          ev
          (Ghost.reveal api)
          (Ghost.reveal old_out)
          network_out_bytes
          out_len
          frame.tls_server_local_bridge_base
          st1
          app_out_bytes
          resp
          (Ghost.reveal wire_outputse)
          local_outputs
      }) = Ghost.hide (
        FStar.IndefiniteDescription.indefinite_description_ghost
          (list CTypes.local_output)
          (fun local_outputs ->
            server_local_common_witness
              (Ghost.reveal srv.canonical_server_initial)
              (Ghost.reveal received0)
              (Ghost.reveal sent0)
              (Ghost.reveal st0)
              ev
              (Ghost.reveal api)
              (Ghost.reveal old_out)
              network_out_bytes
              out_len
              frame.tls_server_local_bridge_base
              st1
              app_out_bytes
              resp
              (Ghost.reveal wire_outputse)
              local_outputs));
      assert (pure (server_local_common_witness
        (Ghost.reveal srv.canonical_server_initial)
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)
        ev
        (Ghost.reveal api)
        (Ghost.reveal old_out)
        network_out_bytes
        out_len
        frame.tls_server_local_bridge_base
        st1
        app_out_bytes
        resp
        (Ghost.reveal wire_outputse)
        (Ghost.reveal local_outputse)));
      let received1e : Ghost.erased B.bytes =
        Ghost.hide st1.CS.cs_wire_log.CL.raw_received;
      let sent1e : Ghost.erased B.bytes =
        Ghost.hide st1.CS.cs_wire_log.CL.raw_sent;
      let st1e : Ghost.erased CS.connection_state = Ghost.hide st1;
      assert (pure ((Ghost.reveal received1e) == st1.CS.cs_wire_log.CL.raw_received));
      assert (pure ((Ghost.reveal sent1e) == st1.CS.cs_wire_log.CL.raw_sent));
      assert (pure ((Ghost.reveal st1e) == st1));
      assert (pure (server_invariant_pure
        (Ghost.reveal srv.canonical_server_initial)
        (Ghost.reveal received1e)
        (Ghost.reveal sent1e)
        (Ghost.reveal st1e)));
      rewrite (S.connection_exactly srv.canonical_server_state st1) as
        (S.connection_exactly srv.canonical_server_state (Ghost.reveal st1e));
      // Prove monotonicity of progress before folding the invariant.
      lemma_server_local_progress
        (Ghost.reveal srv.canonical_server_initial)
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)
        ev
        (Ghost.reveal api)
        (Ghost.reveal old_out)
        network_out_bytes
        out_len
        frame.tls_server_local_bridge_base
        (Ghost.reveal st1e)
        app_out_bytes
        resp
        (Ghost.reveal wire_outputse)
        (Ghost.reveal local_outputse);
      MR.update srv.canonical_server_progress (Ghost.reveal st1e);
      with app_out_bytes.
      fold (server_local_bridge_frame_post
        ev
        frame
        (CTypes.server_local_process_result resp)
        (Ghost.reveal old_out)
        network_out_bytes
        (Ghost.reveal st0)
        (Ghost.reveal st1e)
        (Ghost.reveal wire_outputse)
        (Ghost.reveal local_outputse));
      rewrite
        (server_local_bridge_frame_post
          ev
          frame
          (CTypes.server_local_process_result resp)
          (Ghost.reveal old_out)
          network_out_bytes
          (Ghost.reveal st0)
          (Ghost.reveal st1e)
          (Ghost.reveal wire_outputse)
          (Ghost.reveal local_outputse))
        as
        (server_local_bridge_frame_post
          ev
          frame
          (CTypes.server_local_process_result resp)
          (Ghost.reveal old_out)
          network_out_bytes
          (Ghost.reveal st0)
          (Ghost.reveal st1e)
          (Ghost.reveal wire_outputse)
          (Ghost.reveal local_outputse));
      with certificate_chain credential_identity.
      fold (server_invariant
        srv
        (Ghost.reveal received1e)
        (Ghost.reveal sent1e)
        (Ghost.reveal st1e));
      assert (pure (CPI.local_process_correct
        (server_system (Ghost.reveal srv.canonical_server_initial))
        ev
        (Ghost.reveal old_out)
        network_out_bytes
        out_len
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)
        (CTypes.server_local_process_result resp)
        (Ghost.reveal received1e)
        (Ghost.reveal sent1e)
        (Ghost.reveal st1e)
        (Ghost.reveal wire_outputse)
        (Ghost.reveal local_outputse)));
      CTypes.server_local_process_result resp
}

noextract
let server_protocol_implementation
  : CPI.protocol_implementation
      canonical_server
      CS.connection_state
      CW.wire_message
      CTypes.server_local_event
      CTypes.local_output
  =
  {
    CPI.pi_system =
      (fun srv -> server_system (Ghost.reveal srv.canonical_server_initial));
    CPI.pi_invariant = server_invariant;
    CPI.pi_snapshot = server_snapshot;
    CPI.pi_network_frame = tls_server_network_bridge_frame;
    CPI.pi_network_frame_pre = server_network_bridge_frame_pre;
    CPI.pi_network_frame_post = server_network_bridge_frame_post;
    CPI.pi_local_frame = tls_server_local_bridge_frame;
    CPI.pi_local_frame_pre = server_local_bridge_frame_pre;
    CPI.pi_local_frame_post = server_local_bridge_frame_post;
    CPI.pi_invariant_valid = server_invariant_valid;
    CPI.pi_take_snapshot = take_server_snapshot;
    CPI.pi_recall_snapshot = recall_server_snapshot;
    CPI.pi_process_network = server_process_network;
    CPI.pi_process_local = server_process_local;
  }
