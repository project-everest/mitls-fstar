module TLS13.Impl.Server.CanonicalProtocol

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CPI = Common.ProtocolImplementation
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CryptoSpec = TLS13.Crypto.Spec
module SMRep = TLS13.Spec.StateMachine.Replay
module SMLog = TLS13.Spec.StateMachine.Log
module SMCan = TLS13.Spec.StateMachine.Canonical
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module CW = TLS13.Spec.Endpoint.Wire
module CTypes = TLS13.Impl.CanonicalTypes
module EAPI = TLS13.Spec.Endpoint.API
module ES = TLS13.Spec.Endpoint.Server
module ID = FStar.IndefiniteDescription
module M = TLS13.Messages
module Sem = TLS13.Wire.Semantics
module GSH = TLS13.Wire.Generated.ServerHello
module MR = Pulse.Lib.MonotonicGhostRef
module O = TLS13.OpenSSL
module RVD = TLS13.Wire.Spec.RevealDecode
module RTC = FStar.ReflexiveTransitiveClosure
module S = TLS13.Impl.Server
module SS = TLS13.Impl.Server.Send
module Seq = FStar.Seq
module SM = Common.StateMachine
module ST = TLS13.Impl.Server.Types
module TChannel = TLS13.Impl.Channel
module SZ = FStar.SizeT
module TCP = Common.TCP
module T = TLS13.Types
module U8 = FStar.UInt8
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module WS = TLS13.Wire.Spec
module V = Pulse.Lib.Vec

open TLS13.Spec.Endpoint.Server

(**
  Canonical Common.ProtocolImplementation boundary for the low-level server.

  Credential-dependent local APIs ([process_local_event_with_credentials] and
  the certificate/certificate-verify helpers) are deliberately outside this
  first plain boundary.
 **)

let server_api_event_matches
  (api:CTypes.server_api_event)
  (ev:CS.conn_event)
  : prop =
  ST.local_event_kind_matches
    api.CTypes.server_local_kind
    api.CTypes.server_local_payload
    ev

let server_invariant_pure
  (initial:server_initial_state)
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
  (initial:server_initial_state)
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
    (CryptoSpec.credential_signature_scheme credential_identity) /\
  (match st.CS.cs_model.CS.model_config.CS.config_server with
   | Some cfg ->
     CS.cipher_suite_offered
       cfg.CS.server_supported_cipher_suites
       T.TLS_CHACHA20_POLY1305_SHA256 /\
     (* Cipher-suite agility (gap G1): the server negotiates ChaCha20-Poly1305
        when offered and falls back to AES-128-GCM otherwise, so its profile
        must support both.  The default server config offers exactly these two. *)
     CS.cipher_suite_offered
       cfg.CS.server_supported_cipher_suites
       T.TLS_AES_128_GCM_SHA256 /\
     CS.named_group_offered
       cfg.CS.server_supported_groups
       T.X25519 /\
     (* G2: the selected group follows the peer's accepted key_share offer,
        so the profile must offer both groups the gate can pick. *)
     CS.named_group_offered
       cfg.CS.server_supported_groups
       T.Secp256r1 /\
     CS.signature_scheme_offered
       cfg.CS.server_allowed_signature_schemes
       (CryptoSpec.credential_signature_scheme credential_identity) /\
     (match st.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
      | Some ch ->
        CS.sni_policy_accepts cfg.CS.server_sni_policy (Sem.clientHello_server_name ch)
      | None ->
        True)
   | None ->
     False) /\
  server_selection_present_when_required st /\
  (match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
   | Some selection ->
     selection.CS.server_selected_signature_scheme ==
       CryptoSpec.credential_signature_scheme credential_identity /\
     selection.CS.server_selected_credential == credential_identity
   | None ->
     True)

type server_supported_profile_proof
  (initial:server_initial_state)
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
  initial:server_initial_state -> server_supported_profile_proof initial

noeq
type canonical_server = {
  canonical_server_state: S.server;
  canonical_server_credentials: O.server_credentials;
  canonical_server_progress:
    MR.mref (server_progress_preorder #CTypes.server_local_event);
  canonical_server_initial: Ghost.erased server_initial_state;
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
  : GTot (list EAPI.local_output) =
  EAPI.local_outputs_of_app_bytes (ST.response_app_out resp app_out)

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
  EAPI.lemma_local_outputs_of_app_bytes_exact app_bytes;
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
      (requires CT.received_tls_raw_delta_legal st0 msg raw_received /\
                (match msg with
                 | M.TlsHandshake (M.ServerHello sh) ->
                   B.length (WS.serialize_handshake (M.ServerHello sh)) <= 16640
                 | _ -> True))
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
      let outer_ct = T.Change_cipher_spec in
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
      T.Application_data
      (CS.protected_record_count CL.Received msg));
    assert (CS.protected_record_count CL.Received msg == 1);
    CSL.lemma_raw_records_exactly_one_parse_record raw_received T.Application_data;
    assert (exists fragment.
      WS.parse_record raw_received == Some (T.Application_data, fragment, B.length raw_received));
    let fragment =
      ID.indefinite_description_ghost
        B.bytes
        (fun fragment ->
          WS.parse_record raw_received == Some (T.Application_data, fragment, B.length raw_received)) in
    WS.lemma_parse_record_implies_parse_record_wire raw_received;
    assert (WS.parse_record_wire raw_received ==
      Some (T.Application_data, fragment, B.length raw_received));
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

#push-options "--fuel 2 --ifuel 4 --z3rlimit 60"
(* A well-formed server (server_end_to_end_invariant ==> config_role ==
   ServerEndpoint) never legally receives a ServerHello: legal_handshake_message
   only permits a Received ServerHello for a ClientEndpoint.  Hence for any msg
   admitted by legal_response_for_event on a server, the ServerHello case is
   vacuous, discharging the serialize-length bound of
   [lemma_received_tls_raw_delta_legal_raw_record_parse_success]. *)
let lemma_server_received_msg_bound_server_hello
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (msg:M.tls_message)
  (consumed:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        ST.server_end_to_end_invariant st0 /\
        ST.legal_response_for_event
          st0 st1 resp (ST.received_message_event msg)
          B.empty consumed network_out app_out)
      (ensures
        (match msg with
         | M.TlsHandshake (M.ServerHello sh) ->
           B.length (WS.serialize_handshake (M.ServerHello sh)) <= 16640
         | _ -> True))
=
  match msg with
  | M.TlsHandshake (M.ServerHello sh) ->
    assert_norm (ST.server_end_to_end_invariant st0 ==
      (ST.server_state_correct st0 /\ ST.server_raw_to_message_replay_consistent st0));
    assert_norm (ST.server_state_correct st0 ==
      (ST.server_state_core_correct st0 /\
       SMRep.connection_state_sent_seal_replay_consistent st0 /\
       SMRep.connection_state_received_decode_replay_consistent st0));
    assert (ST.server_state_core_correct st0);
    assert (st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
    assert (CS.legal_connection_delta st0
      { CS.delta_event = ST.received_message_event msg;
        CS.delta_raw_sent = B.empty;
        CS.delta_raw_received = consumed } st1);
    assert (CS.legal_event st0.CS.cs_model (ST.received_message_event msg));
    assert (CS.legal_tls_message st0.CS.cs_model CL.Received msg);
    assert (CS.legal_handshake_message st0.CS.cs_model CL.Received (M.ServerHello sh));
    assert (st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
    assert False
  | _ -> ()
#pop-options

let lemma_server_network_step_ok_process_correct
  (initial:server_initial_state)
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
          (server_system #CTypes.server_local_event initial)
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
  assert (ST.server_end_to_end_invariant st0);
  lemma_server_received_msg_bound_server_hello
    st0 st1 resp msg consumed network_out app_out;
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
  assert (SMRep.sent_event_nonempty_seal_projection
    st0.CS.cs_model
    (ST.received_message_event msg)
    (WF.serialize_all CW.tls_record_wire_format wire_outputs));
  ST.lemma_server_received_message_event_decode_projection
    st0
    msg
    consumed;
  assert (SMRep.received_event_nonempty_decode_projection
    st0.CS.cs_model
    (ST.received_message_event msg)
    consumed);
  assert (server_step #CTypes.server_local_event
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
    (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
    (CPI.input_bytes input input_len)
    wire
    consumed
    residual);
  assert (Seq.equal
    produced
    (WF.serialize_all
      (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
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
    (server_system #CTypes.server_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
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
        (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
        (CPI.input_bytes input input_len)
        msg'
        consumed
        residual' /\
      SZ.v (CTypes.server_process_result buffer_resp).CPI.process_consumed_len ==
        B.length consumed /\
      (server_system #CTypes.server_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.WireEvent msg')
        st1
        (CPI.step_output wire_outputs local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all
          (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
          wire_outputs) /\
      CPI.output_written
        network_out
        (CTypes.server_process_result buffer_resp).CPI.process_produced_len
        produced /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_received (Seq.append received0 consumed) /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced));
    assert (CPI.network_process_correct
      (server_system #CTypes.server_local_event initial)
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

#restart-solver
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
  (local_outputs:list EAPI.local_output)
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
  (local_outputs:list EAPI.local_output)
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
  (initial:server_initial_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : prop =
  CPI.state_ahead (server_system #CTypes.server_local_event initial) st0 st1

let lemma_server_canonical_step_rel_state_ahead
  (initial:server_initial_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires server_canonical_step_rel #CTypes.server_local_event st0 st1)
      (ensures server_state_ahead initial st0 st1)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event CW.wire_message CTypes.server_local_event)
      (fun ev -> exists out. server_step st0 ev st1 out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output CW.wire_message EAPI.local_output)
      (fun out -> server_step st0 ev st1 out) in
  let tr = {
    SM.tr_event = ev;
    SM.tr_next_state = st1;
    SM.tr_output = out;
  } in
  assert (SM.trace_reaches
    (server_system #CTypes.server_local_event initial).WFSM.wfsm_state_machine
    st0
    [tr]
    st1);
  assert (exists trace.
    SM.trace_reaches
      (server_system #CTypes.server_local_event initial).WFSM.wfsm_state_machine
      st0
      trace
      st1)

let lemma_server_progress_state_ahead
  (initial:server_initial_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires server_progress_preorder #CTypes.server_local_event st0 st1)
      (ensures server_state_ahead initial st0 st1)
=
  RTC.induct
    (server_canonical_step_rel #CTypes.server_local_event)
    (fun x y -> server_state_ahead initial x y)
    (fun x ->
      SM.lemma_state_evolves_refl
        (server_system #CTypes.server_local_event initial).WFSM.wfsm_state_machine
        x)
    (fun x y ->
      lemma_server_canonical_step_rel_state_ahead initial x y)
    (fun x y z ->
      SM.lemma_state_evolves_trans
        (server_system #CTypes.server_local_event initial).WFSM.wfsm_state_machine
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
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
    with
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
    with
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
  (initial:server_initial_state)
  (st0:CS.connection_state)
  (trace:list
    (SM.transition
      CS.connection_state
      CW.wire_message
      CTypes.server_local_event
      EAPI.local_output))
  (st1:CS.connection_state)
  : Lemma
      (requires
        SM.trace_reaches
          (server_state_machine #CTypes.server_local_event initial)
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
  (initial:server_initial_state)
  (received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  : Lemma
      (requires
        server_invariant_pure initial received sent st /\
        server_state_ahead initial initial st)
      (ensures
        WFSM.valid_byte_trace
          (server_system #CTypes.server_local_event initial)
          received
          st
          sent
          Seq.empty)
=
  eliminate exists trace.
    SM.trace_reaches
      (server_system #CTypes.server_local_event initial).WFSM.wfsm_state_machine
      initial
      trace
      st
  with
  (
    assert ((server_system #CTypes.server_local_event initial).WFSM.wfsm_state_machine ==
      server_state_machine #CTypes.server_local_event initial);
    assert ((server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format ==
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
        (server_system #CTypes.server_local_event initial).WFSM.wfsm_state_machine
        (server_system #CTypes.server_local_event initial).WFSM.wfsm_state_machine.SM.sm_initial_state
        trace'
        st /\
      WF.parses_as
        (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
        received
        (WFSM.trace_input_messages trace')
        Seq.empty /\
      Seq.equal
        sent
        (WF.serialize_all
          (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
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
          st1.CS.cs_wire_log.CL.raw_sent /\
        TChannel.event_log_extends
          st0.CS.cs_event_log
          st1.CS.cs_event_log)
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
    delta.CS.delta_raw_sent;
  assert (st1.CS.cs_event_log ==
    st0.CS.cs_event_log @ [delta.CS.delta_event]);
  TChannel.lemma_event_log_extends_snoc
    st0.CS.cs_event_log
    delta.CS.delta_event

let lemma_server_step_histories_ahead
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires server_step st0 ev st1 out)
      (ensures
        TCP.bytes_extends
          st0.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_received /\
        TCP.bytes_extends
          st0.CS.cs_wire_log.CL.raw_sent
          st1.CS.cs_wire_log.CL.raw_sent /\
        TChannel.event_log_extends
          st0.CS.cs_event_log
          st1.CS.cs_event_log)
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
      (requires server_canonical_step_rel #CTypes.server_local_event st0 st1)
      (ensures
        TCP.bytes_extends
          st0.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_received /\
        TCP.bytes_extends
          st0.CS.cs_wire_log.CL.raw_sent
          st1.CS.cs_wire_log.CL.raw_sent /\
        TChannel.event_log_extends
          st0.CS.cs_event_log
          st1.CS.cs_event_log)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event CW.wire_message CTypes.server_local_event)
      (fun ev -> exists out. server_step st0 ev st1 out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output CW.wire_message EAPI.local_output)
      (fun out -> server_step st0 ev st1 out) in
  lemma_server_step_histories_ahead st0 ev st1 out

let lemma_server_progress_histories_ahead
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires server_progress_preorder #CTypes.server_local_event st0 st1)
      (ensures
        TCP.bytes_extends
          st0.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_received /\
        TCP.bytes_extends
          st0.CS.cs_wire_log.CL.raw_sent
          st1.CS.cs_wire_log.CL.raw_sent /\
        TChannel.event_log_extends
          st0.CS.cs_event_log
          st1.CS.cs_event_log)
=
  RTC.induct
    (server_canonical_step_rel #CTypes.server_local_event)
    (fun x y ->
      TCP.bytes_extends
        x.CS.cs_wire_log.CL.raw_received
        y.CS.cs_wire_log.CL.raw_received /\
      TCP.bytes_extends
        x.CS.cs_wire_log.CL.raw_sent
        y.CS.cs_wire_log.CL.raw_sent /\
      TChannel.event_log_extends
        x.CS.cs_event_log
        y.CS.cs_event_log)
    (fun x ->
      CPI.lemma_bytes_extends_refl x.CS.cs_wire_log.CL.raw_received;
      CPI.lemma_bytes_extends_refl x.CS.cs_wire_log.CL.raw_sent;
      TChannel.lemma_event_log_extends_refl x.CS.cs_event_log)
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
        z.CS.cs_wire_log.CL.raw_sent;
      TChannel.lemma_event_log_extends_trans
        x.CS.cs_event_log
        y.CS.cs_event_log
        z.CS.cs_event_log)
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
      (server_system
        #CTypes.server_local_event
        (Ghost.reveal srv.canonical_server_initial))
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
    (server_system
      #CTypes.server_local_event
      (Ghost.reveal srv.canonical_server_initial))
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
    let progress =
      MR.alloc #_ #(server_progress_preorder #CTypes.server_local_event)
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

#restart-solver
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
      (server_system
        #CTypes.server_local_event
        (Ghost.reveal srv.canonical_server_initial))
      (Ghost.reveal snapshot_state)
      (Ghost.reveal current_state) /\
    CPI.histories_ahead
      (Ghost.reveal snapshot_received)
      (Ghost.reveal snapshot_sent)
      (Ghost.reveal current_received)
      (Ghost.reveal current_sent) /\
    TChannel.event_log_extends
      (Ghost.reveal snapshot_state).CS.cs_event_log
      (Ghost.reveal current_state).CS.cs_event_log)
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
    (server_system
      #CTypes.server_local_event
      (Ghost.reveal srv.canonical_server_initial))
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

ghost fn recall_server_snapshot_for_protocol
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
      (server_system
        #CTypes.server_local_event
        (Ghost.reveal srv.canonical_server_initial))
      (Ghost.reveal snapshot_state)
      (Ghost.reveal current_state) /\
    CPI.histories_ahead
      (Ghost.reveal snapshot_received)
      (Ghost.reveal snapshot_sent)
      (Ghost.reveal current_received)
      (Ghost.reveal current_sent))
{
  recall_server_snapshot
    srv
    snapshot_received
    snapshot_sent
    snapshot_state
    current_received
    current_sent
    current_state
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
  (local_outputs:list EAPI.local_output)
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
  (initial:server_initial_state)
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
  (local_outputs:list EAPI.local_output)
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
    (server_system #CTypes.server_local_event initial)
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

let lemma_server_network_common_witness_from_parts
  (initial:server_initial_state)
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
  (local_outputs:list EAPI.local_output)
  : Lemma
      (requires
        server_invariant_pure
          initial
          st1.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_sent
          st1 /\
        server_network_frame_post_fact
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
          buffer_resp /\
        CPI.network_process_correct
          (server_system #CTypes.server_local_event initial)
          input_contents
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
      (ensures
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
          local_outputs)
= ()

let server_network_bridge_result
  (initial:server_initial_state)
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

let lemma_server_network_bridge_result_from_common_witness
  (initial:server_initial_state)
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
  (local_outputs:list EAPI.local_output)
  : Lemma
      (requires
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
          local_outputs)
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
  FStar.Classical.exists_intro
    (fun local_outputs' ->
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
        local_outputs')
    local_outputs;
  FStar.Classical.exists_intro
    (fun wire_outputs' -> exists local_outputs'.
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
        wire_outputs'
        local_outputs')
    wire_outputs;
  FStar.Classical.exists_intro
    (fun consumed' -> exists wire_outputs' local_outputs'.
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
    consumed

let lemma_server_network_step_ok_bridge_result
  (initial:server_initial_state)
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
  lemma_server_network_common_witness_from_parts
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
    local_outputs;
  FStar.Classical.exists_intro
    (fun local_outputs' ->
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
        local_outputs')
    local_outputs;
  FStar.Classical.exists_intro
    (fun wire_outputs' -> exists local_outputs'.
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
        wire_outputs'
        local_outputs')
    wire_outputs;
  FStar.Classical.exists_intro
    (fun consumed' -> exists wire_outputs' local_outputs'.
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
    consumed;
  assert (server_network_bridge_result
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

// Non-StepOk bridge lemmas for stuttering and rejected network results.  The
// DecodeError branch uses the zero-consume semantics exposed by Server.Network,
// so these helpers now feed the global server_network_bridge_obligation proof.
let lemma_server_network_need_more_input_bridge_result
  (initial:server_initial_state)
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
        Seq.equal network_out old_network_out)
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
    (server_system #CTypes.server_local_event initial)
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
  lemma_server_network_common_witness_from_parts
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
    local_outputs;
  lemma_server_network_bridge_result_from_common_witness
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

#restart-solver
let lemma_server_network_illegal_transition_bridge_result
  (initial:server_initial_state)
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
        buffer_resp.ST.response.ST.status == ST.IllegalTransition)
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
    (server_system #CTypes.server_local_event initial)
    (CPI.input_bytes input_contents input_len)
    st0
    st1
    consumed
    wire_outputs
    local_outputs);
  assert (Seq.equal
    B.empty
    (WF.serialize_all (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format wire_outputs));
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
      (server_system #CTypes.server_local_event initial)
      (CPI.input_bytes input_contents input_len)
      st0
      st1
      consumed
      wire_outputs
      local_outputs /\
    Seq.equal
      produced
      (WF.serialize_all (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format wire_outputs) /\
    CPI.output_written network_out result.CPI.process_produced_len produced /\
    Seq.equal
      st1.CS.cs_wire_log.CL.raw_received
      (Seq.append received0 consumed) /\
    Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced));
  assert (CPI.network_process_correct
    (server_system #CTypes.server_local_event initial)
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
  lemma_server_network_common_witness_from_parts
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
    local_outputs;
  lemma_server_network_bridge_result_from_common_witness
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

let lemma_server_local_fail_empty_step
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (err:T.tls_error)
  : Lemma
      (requires
        CS.legal_connection_delta
          st0
          {
            CS.delta_event = CS.ConnLocalEvent (CS.LocalFail err);
            CS.delta_raw_sent = B.empty;
            CS.delta_raw_received = B.empty;
          }
          st1)
      (ensures
        server_step
          st0
          (SM.LocalEvent (CTypes.ServerAPI {
            CTypes.server_local_kind = ST.LocalFail;
            CTypes.server_local_payload = B.empty;
          }))
          st1
          (CPI.step_output [] []))
=
  let conn_ev = CS.ConnLocalEvent (CS.LocalFail err) in
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
  assert (SMRep.sent_event_nonempty_seal_projection
    st0.CS.cs_model
    conn_ev
    (WF.serialize_all CW.tls_record_wire_format []));
  assert (B.length B.empty == 0);
  assert (SMRep.received_event_nonempty_decode_projection
    st0.CS.cs_model
    conn_ev
    B.empty);
  assert (server_step
    st0
    (SM.LocalEvent (CTypes.ServerAPI api))
    st1
    (CPI.step_output [] []))

let lemma_server_decode_error_network_process_correct
  (initial:server_initial_state)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (result:CPI.process_result)
  (received1:B.bytes)
  (sent1:B.bytes)
  (st1:CS.connection_state)
  (consumed:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list EAPI.local_output)
  (produced:B.bytes)
  : Lemma
      (requires
        CPI.buffers_wf input_contents input_len old_network_out out_len /\
        Seq.length network_out == Seq.length old_network_out /\
        result.CPI.process_status == CPI.DecodeError /\
        SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
        CPI.network_error_refines_state_machine
          (server_system #CTypes.server_local_event initial)
          (CPI.input_bytes input_contents input_len)
          st0
          st1
          consumed
          wire_outputs
          local_outputs /\
        Seq.equal
          produced
          (WF.serialize_all
            (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
            wire_outputs) /\
        CPI.output_written network_out result.CPI.process_produced_len produced /\
        Seq.equal received1 (Seq.append received0 consumed) /\
        Seq.equal sent1 (Seq.append sent0 produced))
      (ensures
        CPI.network_process_correct
          (server_system #CTypes.server_local_event initial)
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
          local_outputs)
=
  match result.CPI.process_status with
  | CPI.DecodeError ->
    FStar.Classical.exists_intro
      (fun produced' ->
        SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
        CPI.network_error_refines_state_machine
          (server_system #CTypes.server_local_event initial)
          (CPI.input_bytes input_contents input_len)
          st0
          st1
          consumed
          wire_outputs
          local_outputs /\
        Seq.equal
          produced'
          (WF.serialize_all
            (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
            wire_outputs) /\
        CPI.output_written network_out result.CPI.process_produced_len produced' /\
        Seq.equal received1 (Seq.append received0 consumed) /\
        Seq.equal sent1 (Seq.append sent0 produced'))
      produced
  | _ ->
    assert False

let lemma_server_wire_network_error_refines_state_machine
  (initial:server_initial_state)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (consumed:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list EAPI.local_output)
  (wire:CW.wire_message)
  (residual:B.bytes)
  : Lemma
      (requires
        B.length input_contents == SZ.v input_len /\
        CPI.consumed_by_parse
          CW.tls_record_wire_format
          input_contents
          wire
          consumed
          residual /\
        server_step #CTypes.server_local_event
          st0
          (SM.WireEvent wire)
          st1
          (CPI.step_output wire_outputs local_outputs))
      (ensures
        CPI.network_error_refines_state_machine
          (server_system #CTypes.server_local_event initial)
          (CPI.input_bytes input_contents input_len)
          st0
          st1
          consumed
          wire_outputs
          local_outputs)
=
  assert (CPI.bounded_len input_contents input_len == B.length input_contents);
  assert (CPI.input_bytes input_contents input_len ==
    Seq.slice input_contents 0 (B.length input_contents));
  Seq.lemma_len_slice input_contents 0 (B.length input_contents);
  Seq.lemma_eq_intro (CPI.input_bytes input_contents input_len) input_contents;
  assert (Seq.equal (CPI.input_bytes input_contents input_len) input_contents);
  Seq.lemma_eq_elim (CPI.input_bytes input_contents input_len) input_contents;
  assert (CPI.consumed_by_parse
    (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
    (CPI.input_bytes input_contents input_len)
    wire
    consumed
    residual);
  assert (exists residual'.
    CPI.consumed_by_parse
      (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
      (CPI.input_bytes input_contents input_len)
      wire
      consumed
      residual' /\
    server_step #CTypes.server_local_event
      st0
      (SM.WireEvent wire)
      st1
      (CPI.step_output wire_outputs local_outputs));
  assert (exists msg residual'.
    CPI.consumed_by_parse
      (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
      (CPI.input_bytes input_contents input_len)
      msg
      consumed
      residual' /\
    server_step #CTypes.server_local_event
      st0
      (SM.WireEvent msg)
      st1
      (CPI.step_output wire_outputs local_outputs));
  assert (CPI.network_error_refines_state_machine
    (server_system #CTypes.server_local_event initial)
    (CPI.input_bytes input_contents input_len)
    st0
    st1
    consumed
    wire_outputs
    local_outputs)

let lemma_server_connection_failed_network_process_correct
  (initial:server_initial_state)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (result:CPI.process_result)
  (received1:B.bytes)
  (sent1:B.bytes)
  (st1:CS.connection_state)
  (consumed:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list EAPI.local_output)
  (produced:B.bytes)
  : Lemma
      (requires
        CPI.buffers_wf input_contents input_len old_network_out out_len /\
        Seq.length network_out == Seq.length old_network_out /\
        result.CPI.process_status == CPI.ConnectionFailed /\
        SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
        CPI.network_error_refines_state_machine
          (server_system #CTypes.server_local_event initial)
          (CPI.input_bytes input_contents input_len)
          st0
          st1
          consumed
          wire_outputs
          local_outputs /\
        Seq.equal
          produced
          (WF.serialize_all
            (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
            wire_outputs) /\
        CPI.output_written network_out result.CPI.process_produced_len produced /\
        Seq.equal received1 (Seq.append received0 consumed) /\
        Seq.equal sent1 (Seq.append sent0 produced))
      (ensures
        CPI.network_process_correct
          (server_system #CTypes.server_local_event initial)
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
          local_outputs)
=
  match result.CPI.process_status with
  | CPI.ConnectionFailed ->
    FStar.Classical.exists_intro
      (fun produced' ->
        SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
        CPI.network_error_refines_state_machine
          (server_system #CTypes.server_local_event initial)
          (CPI.input_bytes input_contents input_len)
          st0
          st1
          consumed
          wire_outputs
          local_outputs /\
        Seq.equal
          produced'
          (WF.serialize_all
            (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
            wire_outputs) /\
        CPI.output_written network_out result.CPI.process_produced_len produced' /\
        Seq.equal received1 (Seq.append received0 consumed) /\
        Seq.equal sent1 (Seq.append sent0 produced'))
      produced
  | _ ->
    assert False

let lemma_server_network_decode_error_bridge_result
  (initial:server_initial_state)
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
        buffer_resp.ST.response.ST.status == ST.DecodeError)
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
  let decode_err = T.AlertError T.Decode_error in
  let conn_ev = CS.ConnLocalEvent (CS.LocalFail decode_err) in
  assert (resp.ST.status == ST.DecodeError);
  assert (ST.decode_error_response st0 st1 resp network_out app_out);
  assert (buffer_resp.ST.consumed_len == 0sz);
  assert (resp.ST.network_out_len == 0sz);
  assert (resp.ST.app_out_len == 0sz);
  assert (result.CPI.process_status == CPI.DecodeError);
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
  assert (ST.legal_response_for_event
    st0
    st1
    resp
    conn_ev
    B.empty
    B.empty
    network_out
    app_out);
  assert (CS.legal_connection_delta st0 {
    CS.delta_event = conn_ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } st1);
  lemma_server_local_fail_empty_step st0 st1 decode_err;
  assert (server_step
    st0
    (SM.LocalEvent (CTypes.ServerAPI {
      CTypes.server_local_kind = ST.LocalFail;
      CTypes.server_local_payload = B.empty;
    }))
    st1
    (CPI.step_output wire_outputs local_outputs));
  assert (CPI.network_error_refines_state_machine
    (server_system #CTypes.server_local_event initial)
    (CPI.input_bytes input_contents input_len)
    st0
    st1
    consumed
    wire_outputs
    local_outputs);
  assert (Seq.equal
    B.empty
    (WF.serialize_all (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format wire_outputs));
  CPI.lemma_output_prefix_empty network_out;
  assert (CPI.output_written network_out result.CPI.process_produced_len B.empty);
  Seq.lemma_eq_elim received0 st0.CS.cs_wire_log.CL.raw_received;
  Seq.lemma_eq_elim sent0 st0.CS.cs_wire_log.CL.raw_sent;
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  assert (Seq.equal st1.CS.cs_wire_log.CL.raw_received received0);
  assert (Seq.equal st1.CS.cs_wire_log.CL.raw_sent sent0);
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    (Seq.append received0 consumed));
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (Seq.append sent0 B.empty));
  assert (CPI.buffers_wf input_contents input_len old_network_out out_len);
  assert (Seq.length network_out == Seq.length old_network_out);
  let produced = B.empty in
  assert (Seq.equal
    produced
    (WF.serialize_all (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format wire_outputs));
  assert (CPI.output_written network_out result.CPI.process_produced_len produced);
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (Seq.append sent0 produced));
  assert (Seq.length consumed == 0);
  assert (SZ.v result.CPI.process_consumed_len == Seq.length consumed);
  lemma_server_decode_error_network_process_correct
    initial
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
    local_outputs
    produced;
  ST.lemma_server_network_bytes_preserves_config
    st0
    st1
    buffer_resp
    input_contents
    network_out
    app_out;
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
  lemma_server_network_common_witness_from_parts
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
    local_outputs;
  lemma_server_network_bridge_result_from_common_witness
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

let lemma_server_network_connection_failed_bridge_result
  (initial:server_initial_state)
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
        buffer_resp.ST.response.ST.status == ST.ConnectionFailed)
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
  assert (resp.ST.status == ST.ConnectionFailed);
  assert (ST.server_network_connection_failed_consumed_prefix
    st0 st1 buffer_resp input_contents network_out app_out);
  let alert =
    ID.indefinite_description_ghost
      T.alert_description
      (fun alert -> exists raw_received.
        Seq.equal raw_received consumed /\
        ST.legal_network_response st0 st1 resp (M.TlsAlert alert) raw_received network_out app_out /\
        SMRep.received_event_nonempty_decode_projection
          st0.CS.cs_model
          (ST.received_message_event (M.TlsAlert alert))
          raw_received) in
  let raw_received =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_received ->
        Seq.equal raw_received consumed /\
        ST.legal_network_response st0 st1 resp (M.TlsAlert alert) raw_received network_out app_out /\
        SMRep.received_event_nonempty_decode_projection
          st0.CS.cs_model
          (ST.received_message_event (M.TlsAlert alert))
          raw_received) in
  assert (Seq.equal raw_received consumed);
  assert (ST.legal_network_response
    st0
    st1
    resp
    (M.TlsAlert alert)
    raw_received
    network_out
    app_out);
  assert (ST.legal_response_for_event
    st0
    st1
    resp
    (ST.received_message_event (M.TlsAlert alert))
    B.empty
    raw_received
    network_out
    app_out);
  assert (CS.legal_connection_delta st0 {
    CS.delta_event = ST.received_message_event (M.TlsAlert alert);
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } st1);
  assert (CT.received_tls_raw_delta_legal st0 (M.TlsAlert alert) raw_received);
  lemma_received_tls_raw_delta_legal_raw_record_parse_success
    st0
    (M.TlsAlert alert)
    raw_received;
  Seq.lemma_eq_elim raw_received consumed;
  assert (CT.raw_record_parse_success consumed);
  lemma_server_consumed_prefix_parse input_contents buffer_resp;
  let wire =
    ID.indefinite_description_ghost
      CW.wire_message
      (fun wire -> exists residual.
        CPI.consumed_by_parse
          CW.tls_record_wire_format
          input_contents
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
          input_contents
          wire
          consumed
          residual /\
        Seq.equal (CW.wire_serialize wire) consumed) in
  assert (CPI.consumed_by_parse
    CW.tls_record_wire_format
    input_contents
    wire
    consumed
    residual);
  assert (Seq.equal (CW.wire_serialize wire) consumed);
  assert (resp.ST.network_out_len == 0sz);
  assert (ST.response_network_out resp network_out == Seq.slice network_out 0 0);
  Seq.lemma_len_slice network_out 0 0;
  Seq.lemma_eq_intro (ST.response_network_out resp network_out) B.empty;
  assert (Seq.equal (ST.response_network_out resp network_out) B.empty);
  Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
  CW.lemma_wire_outputs_of_empty ();
  assert (wire_outputs == []);
  lemma_server_response_local_outputs_match
    resp
    (ST.received_message_event (M.TlsAlert alert))
    app_out;
  assert (server_local_outputs_match
    (ST.received_message_event (M.TlsAlert alert))
    local_outputs);
  assert (SMRep.sent_event_nonempty_seal_projection
    st0.CS.cs_model
    (ST.received_message_event (M.TlsAlert alert))
    (WF.serialize_all CW.tls_record_wire_format []));
  assert (SMRep.received_event_nonempty_decode_projection
    st0.CS.cs_model
    (ST.received_message_event (M.TlsAlert alert))
    raw_received);
  Seq.lemma_eq_elim raw_received (CW.wire_serialize wire);
  assert (SMRep.received_event_nonempty_decode_projection
    st0.CS.cs_model
    (ST.received_message_event (M.TlsAlert alert))
    (CW.wire_serialize wire));
  assert (CS.legal_connection_delta st0 {
    CS.delta_event = ST.received_message_event (M.TlsAlert alert);
    CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format [];
    CS.delta_raw_received = CW.wire_serialize wire;
  } st1);
  assert (server_step #CTypes.server_local_event
    st0
    (SM.WireEvent wire)
    st1
    (CPI.step_output wire_outputs local_outputs));
  lemma_server_wire_network_error_refines_state_machine
    initial
    input_contents
    input_len
    st0
    st1
    consumed
    wire_outputs
    local_outputs
    wire
    residual;
  assert (Seq.equal
    B.empty
    (WF.serialize_all (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format wire_outputs));
  CPI.lemma_output_prefix_empty network_out;
  assert (CPI.output_written network_out result.CPI.process_produced_len B.empty);
  Seq.lemma_eq_elim received0 st0.CS.cs_wire_log.CL.raw_received;
  Seq.lemma_eq_elim sent0 st0.CS.cs_wire_log.CL.raw_sent;
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    (Seq.append received0 consumed));
  Seq.append_empty_r sent0;
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (Seq.append sent0 B.empty));
  let produced = B.empty in
  assert (result.CPI.process_status == CPI.ConnectionFailed);
  assert (SZ.v buffer_resp.ST.consumed_len <= B.length input_contents);
  assert (consumed ==
    Seq.slice input_contents 0 (SZ.v buffer_resp.ST.consumed_len));
  Seq.lemma_len_slice input_contents 0 (SZ.v buffer_resp.ST.consumed_len);
  assert (Seq.length consumed == SZ.v buffer_resp.ST.consumed_len);
  assert (SZ.v result.CPI.process_consumed_len == Seq.length consumed);
  assert (Seq.equal
    produced
    (WF.serialize_all (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format wire_outputs));
  assert (CPI.output_written network_out result.CPI.process_produced_len produced);
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (Seq.append sent0 produced));
  lemma_server_connection_failed_network_process_correct
    initial
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
    local_outputs
    produced;
  ST.lemma_server_network_bytes_preserves_config
    st0
    st1
    buffer_resp
    input_contents
    network_out
    app_out;
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
  lemma_server_network_common_witness_from_parts
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
    local_outputs;
  lemma_server_network_bridge_result_from_common_witness
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

#restart-solver
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
    /\
    (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
      Seq.equal network_out old_network_out)
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

let lemma_server_network_bridge_obligation
  (base:tls_server_network_frame)
  : Lemma
      (ensures server_network_bridge_obligation base)
=
  introduce forall initial received0 sent0 st0 input_contents input_len
    old_network_out network_out out_len st1 app_out buffer_resp.
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
      WS.parse_record_wire input_contents == None) /\
    (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
      Seq.equal network_out old_network_out)
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
  with
    introduce _ ==> _ with
    match buffer_resp.ST.response.ST.status with
    | ST.StepOk ->
      lemma_server_network_step_ok_bridge_result
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
    | ST.NeedMoreInput ->
      lemma_server_network_need_more_input_bridge_result
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
    | ST.DecodeError ->
      lemma_server_network_decode_error_bridge_result
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
    | ST.IllegalTransition ->
      lemma_server_network_illegal_transition_bridge_result
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
    | ST.OutputBufferTooSmall ->
      assert False
    | ST.ConnectionFailed ->
      lemma_server_network_connection_failed_bridge_result
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
}

let lemma_server_network_bridge_frame_obligation
  (frame:tls_server_network_bridge_frame)
  : Lemma
      (ensures
        server_network_bridge_obligation frame.tls_server_network_bridge_base)
=
  lemma_server_network_bridge_obligation frame.tls_server_network_bridge_base

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
  (local_outputs:list EAPI.local_output)
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
  (local_outputs:list EAPI.local_output)
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
  (initial:server_initial_state)
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
  (local_outputs:list EAPI.local_output)
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
    (server_system #CTypes.server_local_event initial)
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
  (initial:server_initial_state)
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

let lemma_server_local_bridge_result_from_common_witness
  (initial:server_initial_state)
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
  (local_outputs:list EAPI.local_output)
  : Lemma
      (requires
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
          local_outputs)
      (ensures
        server_local_bridge_result
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
          resp)
=
  FStar.Classical.exists_intro
    (fun local_outputs' ->
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
        local_outputs')
    local_outputs;
  FStar.Classical.exists_intro
    (fun wire_outputs' -> exists local_outputs'.
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
        wire_outputs'
        local_outputs')
    wire_outputs

let lemma_server_step_from_local_witness
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (local_ev:CTypes.server_local_event)
  (conn_ev:CS.conn_event)
  (raw_sent:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list EAPI.local_output)
  : Lemma
      (requires
        server_api_event_matches
          (CTypes.server_local_event_api local_ev)
          conn_ev /\
        server_wire_outputs_match raw_sent wire_outputs /\
        server_local_outputs_match conn_ev local_outputs /\
        CS.legal_connection_delta st0 {
          CS.delta_event = conn_ev;
          CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty;
        } st1 /\
        SMRep.sent_event_nonempty_seal_projection
          st0.CS.cs_model
          conn_ev
          raw_sent)
      (ensures
        server_step
          st0
          (SM.LocalEvent local_ev)
          st1
          (CPI.step_output wire_outputs local_outputs))
=
  assert ((CPI.step_output wire_outputs local_outputs).SM.so_wire_outputs ==
    wire_outputs);
  assert ((CPI.step_output wire_outputs local_outputs).SM.so_local_outputs ==
    local_outputs);
  assert (B.length B.empty == 0);
  assert (SMRep.received_event_nonempty_decode_projection
    st0.CS.cs_model
    conn_ev
    B.empty);
  assert (exists conn_ev' raw_sent'.
    server_api_event_matches
      (CTypes.server_local_event_api local_ev)
      conn_ev' /\
    server_wire_outputs_match
      raw_sent'
      (CPI.step_output wire_outputs local_outputs).SM.so_wire_outputs /\
    server_local_outputs_match
      conn_ev'
      (CPI.step_output wire_outputs local_outputs).SM.so_local_outputs /\
    CS.legal_connection_delta st0 {
      CS.delta_event = conn_ev';
      CS.delta_raw_sent = raw_sent';
      CS.delta_raw_received = B.empty;
    } st1 /\
    SMRep.sent_event_nonempty_seal_projection
      st0.CS.cs_model
      conn_ev'
      raw_sent' /\
    SMRep.received_event_nonempty_decode_projection
      st0.CS.cs_model
      conn_ev'
      B.empty);
  assert (server_step
    st0
    (SM.LocalEvent local_ev)
    st1
    (CPI.step_output wire_outputs local_outputs))

let lemma_server_local_raw_sent_parse_success
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        ST.legal_local_response
          st0
          st1
          resp
          kind
          payload
          ev
          raw_sent
          raw_received
          network_out
          app_out)
      (ensures
        B.length raw_sent == 0 \/
        exists content_type fragment.
          WS.parse_record_wire raw_sent ==
            Some (content_type, fragment, B.length raw_sent))
=
  assert (ST.local_event_kind_matches kind payload ev);
  assert (ST.local_event_supported_profile kind payload ev);
  assert (ST.legal_response_for_event
    st0
    st1
    resp
    ev
    raw_sent
    raw_received
    network_out
    app_out);
  assert (CS.legal_connection_delta st0 {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = raw_received;
  } st1);
  assert (CS.event_raw_delta_legal
    st0.CS.cs_model
    ev
    raw_sent
    raw_received);
  match ev with
  | CS.ConnLocalEvent _ ->
    assert (Seq.equal raw_sent B.empty);
    Seq.lemma_eq_elim raw_sent B.empty
  | CS.ConnNetworkEvent msg ->
    assert (msg.CL.message_direction == CL.Sent);
    if CS.network_message_is_cleartext
        msg.CL.message_direction
        msg.CL.message_value
    then (
      assert (CS.cleartext_tls_message_raw msg.CL.message_value raw_sent);
      match msg.CL.message_value with
      | M.TlsHandshake M.HelloRetryRequest ->
        assert (CS.raw_records_exactly raw_sent T.Handshake 1);
        CSL.lemma_raw_records_exactly_one_parse_record raw_sent T.Handshake;
        let fragment =
          ID.indefinite_description_ghost
            B.bytes
            (fun fragment ->
              WS.parse_record raw_sent ==
                Some (T.Handshake, fragment, B.length raw_sent)) in
        assert (WS.parse_record raw_sent ==
          Some (T.Handshake, fragment, B.length raw_sent));
        WS.lemma_parse_record_implies_parse_record_wire raw_sent;
        assert (exists content_type fragment'.
          WS.parse_record_wire raw_sent ==
            Some (content_type, fragment', B.length raw_sent))
      | M.TlsHandshake (M.ServerHello sh) ->
        let (content_type, fragment) =
          WS.serialize_tls_message msg.CL.message_value in
        WS.lemma_serialize_tls_message_handshake (M.ServerHello sh);
        // The record-size bound on a sent ServerHello now comes from message
        // legality: legal_handshake_message only admits a Sent ServerHello in the
        // HsClientHelloReceived stage via [server_hello_matches_selection], whose
        // final conjunct is exactly [B.length (serialize_handshake (ServerHello sh)) <= 16640].
        // (Previously supplied by the now-removed WS.lemma_serialize_server_hello_len,
        // which relied on the fixed-layout hand-written ServerHello serializer.)
        assert (CS.legal_event st0.CS.cs_model ev);
        assert (CS.legal_tls_message st0.CS.cs_model CL.Sent
          (M.TlsHandshake (M.ServerHello sh)));
        assert (CS.legal_handshake_message st0.CS.cs_model CL.Sent (M.ServerHello sh));
        assert (B.length (WS.serialize_handshake (M.ServerHello sh)) <= 16640);
        assert (Seq.equal
          raw_sent
          (CS.serialized_cleartext_tls_message msg.CL.message_value));
        assert (B.length fragment <= 16640);
        WS.lemma_parse_record_serialize_record content_type fragment;
        Seq.lemma_eq_elim
          raw_sent
          (CS.serialized_cleartext_tls_message msg.CL.message_value);
        WS.lemma_parse_record_implies_parse_record_wire raw_sent;
        assert (WS.parse_record_wire raw_sent ==
          Some (content_type, fragment, B.length raw_sent));
        assert (exists content_type' fragment'.
          WS.parse_record_wire raw_sent ==
            Some (content_type', fragment', B.length raw_sent))
      | M.TlsChangeCipherSpec ->
        let (content_type, fragment) =
          WS.serialize_tls_message msg.CL.message_value in
        WS.lemma_serialize_tls_message_change_cipher_spec ();
        assert (Seq.equal
          raw_sent
          (CS.serialized_cleartext_tls_message msg.CL.message_value));
        assert (B.length fragment <= 16640);
        WS.lemma_parse_record_serialize_record content_type fragment;
        Seq.lemma_eq_elim
          raw_sent
          (CS.serialized_cleartext_tls_message msg.CL.message_value);
        WS.lemma_parse_record_implies_parse_record_wire raw_sent;
        assert (WS.parse_record_wire raw_sent ==
          Some (content_type, fragment, B.length raw_sent));
        assert (exists content_type' fragment'.
          WS.parse_record_wire raw_sent ==
            Some (content_type', fragment', B.length raw_sent))
      | _ ->
        assert False
    ) else (
      assert (CS.network_message_raw_delta_legal st0.CS.cs_model msg raw_sent);
      assert (CS.raw_records_exactly
        raw_sent
        T.Application_data
        (CS.protected_record_count
          msg.CL.message_direction
          msg.CL.message_value));
      assert (CS.protected_record_count
        msg.CL.message_direction
        msg.CL.message_value == 1);
      CSL.lemma_raw_records_exactly_one_parse_record raw_sent T.Application_data;
      let fragment =
        ID.indefinite_description_ghost
          B.bytes
          (fun fragment ->
            WS.parse_record raw_sent ==
              Some (T.Application_data, fragment, B.length raw_sent)) in
      assert (WS.parse_record raw_sent ==
        Some (T.Application_data, fragment, B.length raw_sent));
      WS.lemma_parse_record_implies_parse_record_wire raw_sent;
      assert (exists content_type fragment'.
        WS.parse_record_wire raw_sent ==
          Some (content_type, fragment', B.length raw_sent))
    )

let lemma_server_api_event_raw_received_empty
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (api:CTypes.server_api_event)
  (resp:ST.server_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        ST.legal_local_response
          st0
          st1
          resp
          api.CTypes.server_local_kind
          api.CTypes.server_local_payload
          ev
          raw_sent
          raw_received
          network_out
          app_out)
      (ensures Seq.equal raw_received B.empty)
=
  assert (ST.local_event_kind_matches
    api.CTypes.server_local_kind
    api.CTypes.server_local_payload
    ev);
  assert (ST.legal_response_for_event
    st0 st1 resp ev raw_sent raw_received network_out app_out);
  assert (CS.legal_connection_delta
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1);
  assert (CS.event_raw_delta_legal
    st0.CS.cs_model
    ev
    raw_sent
    raw_received);
  match ev with
  | CS.ConnLocalEvent _ ->
    ()
  | CS.ConnNetworkEvent msg ->
    match api.CTypes.server_local_kind with
    | ST.LocalSendApplicationData
    | ST.LocalSendServerHello
    | ST.LocalSendEncryptedExtensions
    | ST.LocalSendCertificate
    | ST.LocalSendCertificateVerify
    | ST.LocalSendServerFinished
    | ST.LocalSendCloseNotify
    | ST.LocalSendKeyUpdate
    | ST.LocalSendKeyUpdateRequested ->
      assert (msg.CL.message_direction == CL.Sent)
    | _ ->
      assert False

let lemma_server_wire_outputs_match_response
  (resp:ST.server_response)
  (network_out:B.bytes)
  (raw_sent:B.bytes)
  : Lemma
      (requires
        Seq.equal raw_sent (ST.response_network_out resp network_out) /\
        (B.length raw_sent == 0 \/
         exists content_type fragment.
           WS.parse_record_wire raw_sent ==
             Some (content_type, fragment, B.length raw_sent)))
      (ensures
        server_wire_outputs_match
          raw_sent
          (server_response_wire_outputs resp network_out))
=
  let raw = ST.response_network_out resp network_out in
  if B.length raw_sent == 0 then (
    Seq.lemma_eq_elim raw_sent B.empty;
    Seq.lemma_eq_elim raw raw_sent;
    CW.lemma_wire_outputs_of_empty ();
    assert (server_response_wire_outputs resp network_out ==
      CW.wire_outputs_of_full_record B.empty);
    assert (server_wire_outputs_match
      raw_sent
      (server_response_wire_outputs resp network_out))
  ) else (
    let content_type =
      ID.indefinite_description_ghost
        T.content_type
        (fun content_type -> exists fragment.
          WS.parse_record_wire raw_sent ==
            Some (content_type, fragment, B.length raw_sent)) in
    let fragment =
      ID.indefinite_description_ghost
        M.sealed_record
        (fun fragment ->
          WS.parse_record_wire raw_sent ==
            Some (content_type, fragment, B.length raw_sent)) in
    assert (WS.parse_record_wire raw_sent ==
      Some (content_type, fragment, B.length raw_sent));
    Seq.lemma_eq_elim raw raw_sent;
    assert (WS.parse_record_wire raw ==
      Some (content_type, fragment, B.length raw));
    CW.lemma_wire_outputs_of_full_record_serializes
      raw
      content_type
      fragment;
    assert (server_wire_outputs_match
      raw_sent
      (server_response_wire_outputs resp network_out))
  )

let lemma_server_local_process_correct
  (initial:server_initial_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (local_ev:CTypes.server_local_event)
  (api:CTypes.server_api_event)
  (resp:ST.server_response)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (app_out:B.bytes)
  (received0:B.bytes)
  (sent0:B.bytes)
  : Lemma
      (requires
        ST.server_local_event_end_to_end_correct
          st0
          st1
          resp
          api.CTypes.server_local_kind
          api.CTypes.server_local_payload
          network_out
          app_out /\
        api == CTypes.server_local_event_api local_ev /\
        ST.server_local_event_input_ready
          st0
          api.CTypes.server_local_kind
          api.CTypes.server_local_payload /\
        SZ.v out_len == B.length old_network_out /\
        B.length network_out == B.length old_network_out /\
        Seq.equal received0 st0.CS.cs_wire_log.CL.raw_received /\
        Seq.equal sent0 st0.CS.cs_wire_log.CL.raw_sent)
      (ensures
        CPI.local_process_correct
          (server_system #CTypes.server_local_event initial)
          local_ev
          old_network_out
          network_out
          out_len
          received0
          sent0
          st0
          (CTypes.server_local_process_result resp)
          st1.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_sent
          st1
          (server_response_wire_outputs resp network_out)
          (server_response_local_outputs resp app_out))
=
  let wire_outputs = server_response_wire_outputs resp network_out in
  let local_outputs = server_response_local_outputs resp app_out in
  let result = CTypes.server_local_process_result resp in
  assert (ST.legal_handled_local_response
    st0
    st1
    resp
    api.CTypes.server_local_kind
    api.CTypes.server_local_payload
    network_out
    app_out);
  assert (result.CPI.process_consumed_len == 0sz);
  if resp.ST.status == ST.StepOk then (
    assert (exists ev raw_sent raw_received.
      ST.legal_local_response
        st0
        st1
        resp
        api.CTypes.server_local_kind
        api.CTypes.server_local_payload
        ev
        raw_sent
        raw_received
        network_out
        app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          ST.legal_local_response
            st0
            st1
            resp
            api.CTypes.server_local_kind
            api.CTypes.server_local_payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          ST.legal_local_response
            st0
            st1
            resp
            api.CTypes.server_local_kind
            api.CTypes.server_local_payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          ST.legal_local_response
            st0
            st1
            resp
            api.CTypes.server_local_kind
            api.CTypes.server_local_payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    assert (ST.legal_local_response
      st0
      st1
      resp
      api.CTypes.server_local_kind
      api.CTypes.server_local_payload
      ev
      raw_sent
      raw_received
      network_out
      app_out);
    assert (ST.legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    assert (server_api_event_matches api ev);
    assert (ST.local_event_kind_matches
      api.CTypes.server_local_kind
      api.CTypes.server_local_payload
      ev);
    assert (Seq.equal raw_sent (ST.response_network_out resp network_out));
    lemma_server_local_raw_sent_parse_success
      st0
      st1
      resp
      api.CTypes.server_local_kind
      api.CTypes.server_local_payload
      ev
      raw_sent
      raw_received
      network_out
      app_out;
    lemma_server_wire_outputs_match_response resp network_out raw_sent;
    assert (server_wire_outputs_match raw_sent wire_outputs);
    lemma_server_response_local_outputs_match resp ev app_out;
    assert (server_local_outputs_match ev local_outputs);
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    } st1);
    lemma_server_api_event_raw_received_empty
      st0
      st1
      api
      resp
      ev
      raw_sent
      raw_received
      network_out
      app_out;
    assert (Seq.equal raw_received B.empty);
    Seq.lemma_eq_elim raw_received B.empty;
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = B.empty;
    } st1);
    assert (SMRep.sent_event_nonempty_seal_projection
      st0.CS.cs_model
      ev
      raw_sent);
    lemma_server_step_from_local_witness
      st0
      st1
      local_ev
      ev
      raw_sent
      wire_outputs
      local_outputs;
    let produced = WF.serialize_all CW.tls_record_wire_format wire_outputs in
    assert (Seq.equal produced raw_sent);
    assert (Seq.equal produced (ST.response_network_out resp network_out));
    assert (SZ.v resp.ST.network_out_len <= B.length network_out);
    assert (B.length raw_sent == SZ.v resp.ST.network_out_len);
    assert (B.length produced == SZ.v resp.ST.network_out_len);
    assert (CPI.output_written
      network_out
      result.CPI.process_produced_len
      produced);
    Seq.lemma_eq_elim received0 st0.CS.cs_wire_log.CL.raw_received;
    Seq.lemma_eq_elim sent0 st0.CS.cs_wire_log.CL.raw_sent;
    CL.lemma_append_empty_right st0.CS.cs_wire_log.CL.raw_received;
    assert (Seq.equal st1.CS.cs_wire_log.CL.raw_received received0);
    assert (Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 raw_sent));
    Seq.lemma_eq_elim raw_sent produced;
    assert (Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced));
    assert (result.CPI.process_status == CPI.StepOk);
    assert (exists produced'.
      (server_system #CTypes.server_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.LocalEvent local_ev)
        st1
        (CPI.step_output wire_outputs local_outputs) /\
      Seq.equal produced'
        (WF.serialize_all
          (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
          wire_outputs) /\
      CPI.output_written network_out result.CPI.process_produced_len produced' /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_received received0 /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced'));
    assert (CPI.local_process_correct
      (server_system #CTypes.server_local_event initial)
      local_ev
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
      wire_outputs
      local_outputs)
  ) else (
    assert (ST.unexpected_message_response st0 st1 resp network_out app_out);
    let err : T.tls_error = T.AlertError T.Unexpected_message in
    let conn_ev = CS.ConnLocalEvent (CS.LocalFail err) in
    let api_fail : CTypes.server_api_event = {
      CTypes.server_local_kind = ST.LocalFail;
      CTypes.server_local_payload = B.empty;
    } in
    assert (ST.legal_response_for_event
      st0 st1 resp conn_ev B.empty B.empty network_out app_out);
    assert (resp.ST.status == ST.IllegalTransition);
    assert (result.CPI.process_status == CPI.IllegalTransition);
    assert (result.CPI.process_produced_len == 0sz);
    assert (Seq.equal (ST.response_network_out resp network_out) B.empty);
    CW.lemma_wire_outputs_of_empty ();
    assert (wire_outputs == []);
    assert (server_wire_outputs_match B.empty wire_outputs);
    lemma_server_response_local_outputs_match resp conn_ev app_out;
    assert (server_local_outputs_match conn_ev local_outputs);
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    } st1);
    assert (server_api_event_matches api_fail conn_ev);
    assert_norm (CTypes.server_local_event_api (CTypes.ServerAPI api_fail) == api_fail);
    assert (SMRep.sent_event_nonempty_seal_projection
      st0.CS.cs_model
      conn_ev
      B.empty);
    lemma_server_step_from_local_witness
      st0
      st1
      (CTypes.ServerAPI api_fail)
      conn_ev
      B.empty
      wire_outputs
      local_outputs;
    let produced = B.empty in
    assert (Seq.equal
      produced
      (WF.serialize_all CW.tls_record_wire_format wire_outputs));
    CPI.lemma_output_prefix_empty network_out;
    assert (CPI.output_written network_out result.CPI.process_produced_len produced);
    Seq.lemma_eq_elim received0 st0.CS.cs_wire_log.CL.raw_received;
    Seq.lemma_eq_elim sent0 st0.CS.cs_wire_log.CL.raw_sent;
    CL.lemma_append_empty_right st0.CS.cs_wire_log.CL.raw_received;
    CL.lemma_append_empty_right st0.CS.cs_wire_log.CL.raw_sent;
    assert (Seq.equal st1.CS.cs_wire_log.CL.raw_received received0);
    assert (Seq.equal st1.CS.cs_wire_log.CL.raw_sent sent0);
    assert (Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced));
    CPI.lemma_local_process_error_refines_step
      (server_system #CTypes.server_local_event initial)
      local_ev
      (CTypes.ServerAPI api_fail)
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
      wire_outputs
      local_outputs
      produced
  )

#restart-solver
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

let lemma_server_local_bridge_obligation
  (base:tls_server_local_frame)
  : Lemma
      (ensures server_local_bridge_obligation base)
=
  introduce forall initial received0 sent0 st0 local_ev api old_network_out
    network_out out_len st1 app_out resp.
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
  with
    introduce _ ==> _ with
    let wire_outputs = server_response_wire_outputs resp network_out in
    let local_outputs = server_response_local_outputs resp app_out in
    lemma_server_local_process_correct
      initial
      st0
      st1
      local_ev
      api
      resp
      old_network_out
      network_out
      out_len
      app_out
      received0
      sent0;
    ST.lemma_server_local_event_preserves_config
      st0
      st1
      resp
      api.CTypes.server_local_kind
      api.CTypes.server_local_payload
      network_out
      app_out;
    assert (server_invariant_pure
      initial
      st1.CS.cs_wire_log.CL.raw_received
      st1.CS.cs_wire_log.CL.raw_sent
      st1);
    assert (server_local_api_frame_post_fact
      api
      base
      (CTypes.server_local_process_result resp)
      old_network_out
      network_out
      st0
      st1
      wire_outputs
      local_outputs
      app_out
      resp);
    assert (server_local_common_witness
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
      local_outputs);
    lemma_server_local_bridge_result_from_common_witness
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

noeq
type tls_server_local_bridge_frame = {
  tls_server_local_bridge_base: tls_server_local_frame;
}

let lemma_server_local_bridge_frame_obligation
  (frame:tls_server_local_bridge_frame)
  : Lemma
      (ensures
        server_local_bridge_obligation frame.tls_server_local_bridge_base)
=
  lemma_server_local_bridge_obligation frame.tls_server_local_bridge_base

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
  (local_outputs:list EAPI.local_output)
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

(* Internal processing reuses the local bridge frame.  It takes no event,
   so the payload buffer contents are existentially quantified. *)
[@@pulse_unfold]
let server_internal_frame_pre
  (frame:tls_server_local_bridge_frame)
  (_st0:CS.connection_state)
  (_out:array U8.t)
  (out_len:SZ.t)
  (old_network_out:B.bytes)
  : slprop =
  let base = frame.tls_server_local_bridge_base in
  exists* (payload:B.bytes).
    pts_to base.tls_server_local_payload payload **
    pts_to
      base.tls_server_local_app_out
      (Ghost.reveal base.tls_server_local_old_app_out) **
    pure (
      B.length payload == SZ.v base.tls_server_local_payload_len /\
      B.length old_network_out == SZ.v out_len /\
      B.length (Ghost.reveal base.tls_server_local_old_app_out) ==
        SZ.v base.tls_server_local_app_out_len)

let server_internal_frame_post
  (frame:tls_server_local_bridge_frame)
  (_result:CPI.internal_result)
  (_old_network_out:B.bytes)
  (_network_out:B.bytes)
  (_st0:CS.connection_state)
  (_st1:CS.connection_state)
  (_wire_outputs:list CW.wire_message)
  (_local_outputs:list EAPI.local_output)
  : slprop =
  let base = frame.tls_server_local_bridge_base in
  exists* (payload:B.bytes) (app_out:B.bytes).
    pts_to base.tls_server_local_payload payload **
    pts_to base.tls_server_local_app_out app_out **
    pure (
      B.length payload == SZ.v base.tls_server_local_payload_len /\
      B.length app_out == SZ.v base.tls_server_local_app_out_len)

let server_process_network_post  (srv:canonical_server)
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
          (local_outputs:list EAPI.local_output).
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
        (server_system #CTypes.server_local_event (Ghost.reveal srv.canonical_server_initial))
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
#push-options "--z3rlimit 200"
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
      (ensures
        server_canonical_step_rel #CTypes.server_local_event st0 st1)
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
        (ensures
          server_canonical_step_rel #CTypes.server_local_event st0 st1)
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
    assert (SMRep.sent_event_nonempty_seal_projection
      st0.CS.cs_model
      conn_ev
      (WF.serialize_all CW.tls_record_wire_format []));
    assert (B.length B.empty == 0);
    assert (SMRep.received_event_nonempty_decode_projection
      st0.CS.cs_model
      conn_ev
      B.empty);
    assert (server_step st0 (SM.LocalEvent (CTypes.ServerAPI api)) st1 (CPI.step_output [] []))
  in
  if resp.ST.status = ST.DecodeError then (
    // DecodeError → LocalFail (tls_decode_error)
    assert (ST.decode_error_response st0 st1 resp network_out app_out);
    let decode_err : T.tls_error = T.AlertError T.Decode_error in
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
          SMRep.received_event_nonempty_decode_projection
            st0.CS.cs_model
            (ST.received_message_event (M.TlsAlert alert))
            raw_received) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          Seq.equal raw_received (ST.server_network_consumed_prefix buffer_resp input_contents) /\
          ST.legal_network_response st0 st1 resp (M.TlsAlert alert) raw_received network_out app_out /\
          SMRep.received_event_nonempty_decode_projection
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
    assert (SMRep.sent_event_nonempty_seal_projection
      st0.CS.cs_model
      conn_ev
      (WF.serialize_all CW.tls_record_wire_format []));
    assert (SMRep.received_event_nonempty_decode_projection
      st0.CS.cs_model
      conn_ev
      raw_received);
    assert (SMRep.received_event_nonempty_decode_projection
      st0.CS.cs_model
      conn_ev
      (CW.wire_serialize wire));
    assert (server_step #CTypes.server_local_event
      st0 (SM.WireEvent wire) st1 (CPI.step_output [] local_outputs));
    assert (server_canonical_step_rel #CTypes.server_local_event st0 st1)
  )

#pop-options
let lemma_server_network_event_progress
  (initial:server_initial_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:ST.server_buffer_response)
  (input:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (app_out:B.bytes)
  : Lemma
      (requires
        CPI.buffers_wf input input_len old_network_out out_len /\
        B.length input == SZ.v input_len /\
        B.length network_out == B.length old_network_out /\
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
          app_out)
      (ensures
        server_progress_preorder #CTypes.server_local_event st0 st1 /\
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config)
=
  ST.lemma_server_network_bytes_preserves_config
    st0
    st1
    buffer_resp
    input
    network_out
    app_out;
  let result = CTypes.server_process_result buffer_resp in
  let consumed = ST.server_network_consumed_prefix buffer_resp input in
  let wire_outputs =
    server_response_wire_outputs buffer_resp.ST.response network_out in
  let local_outputs =
    server_response_local_outputs buffer_resp.ST.response app_out in
  if result.CPI.process_status = CPI.StepOk then (
    lemma_server_network_step_ok_process_correct
      initial
      st0
      st1
      buffer_resp
      input
      input_len
      old_network_out
      network_out
      out_len
      app_out
      st0.CS.cs_wire_log.CL.raw_received
      st0.CS.cs_wire_log.CL.raw_sent;
    CPI.lemma_network_process_ok_refines_transition
      (server_system #CTypes.server_local_event initial)
      input
      input_len
      old_network_out
      network_out
      out_len
      st0.CS.cs_wire_log.CL.raw_received
      st0.CS.cs_wire_log.CL.raw_sent
      st0
      result
      st1.CS.cs_wire_log.CL.raw_received
      st1.CS.cs_wire_log.CL.raw_sent
      st1
      consumed
      wire_outputs
      local_outputs;
    assert (server_step #CTypes.server_local_event
      st0
      (SM.WireEvent
        (ID.indefinite_description_ghost
          CW.wire_message
          (fun msg -> exists residual produced.
            CPI.consumed_by_parse
              (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
              (CPI.input_bytes input input_len)
              msg
              consumed
              residual /\
            SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
            server_step #CTypes.server_local_event
              st0
              (SM.WireEvent msg)
              st1
              (CPI.step_output wire_outputs local_outputs) /\
            Seq.equal
              produced
              (WF.serialize_all
                (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
                wire_outputs) /\
            CPI.output_written
              network_out
              result.CPI.process_produced_len
              produced)))
      st1
      (CPI.step_output wire_outputs local_outputs));
    assert (server_canonical_step_rel #CTypes.server_local_event st0 st1);
    RTC.closure_step
      (server_canonical_step_rel #CTypes.server_local_event)
      st0
      st1
  ) else if st1 = st0 then
    assert (server_progress_preorder #CTypes.server_local_event st0 st1)
  else (
    assert (buffer_resp.ST.response.ST.status <> ST.StepOk);
    lemma_server_network_nonstep_canonical_step
      st0 st1 buffer_resp input network_out app_out;
    RTC.closure_step
      (server_canonical_step_rel #CTypes.server_local_event)
      st0
      st1
  )

// Prove server_progress_preorder st0 st1 from server_network_common_witness.
// Mirrors lemma_client_network_common_witness_progress.
#push-options "--z3rlimit 100"
let lemma_server_network_common_witness_progress
  (initial:server_initial_state)
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
  (local_outputs:list EAPI.local_output)
  : Lemma
      (requires
        server_network_common_witness
          initial received0 sent0 st0 input_contents input_len
          old_network_out network_out out_len base st1 app_out buffer_resp
          consumed wire_outputs local_outputs)
      (ensures
        server_progress_preorder #CTypes.server_local_event st0 st1)
  =
  let result = CTypes.server_process_result buffer_resp in
  if result.CPI.process_status = CPI.StepOk then (
    CPI.lemma_network_process_ok_refines_transition
      (server_system #CTypes.server_local_event initial)
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
        (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
        (CPI.input_bytes input_contents input_len)
        msg
        consumed
        residual /\
      SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
      (server_system #CTypes.server_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.WireEvent msg)
        st1
        (CPI.step_output wire_outputs local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format wire_outputs) /\
      CPI.output_written network_out result.CPI.process_produced_len produced /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_received (Seq.append received0 consumed) /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced));
    let msg =
      ID.indefinite_description_ghost
        CW.wire_message
        (fun msg -> exists residual produced.
          CPI.consumed_by_parse
            (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format
            (CPI.input_bytes input_contents input_len)
            msg
            consumed
            residual /\
          SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
          (server_system #CTypes.server_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
            st0
            (SM.WireEvent msg)
            st1
            (CPI.step_output wire_outputs local_outputs) /\
          Seq.equal
            produced
            (WF.serialize_all (server_system #CTypes.server_local_event initial).WFSM.wfsm_wire_format wire_outputs) /\
          CPI.output_written network_out result.CPI.process_produced_len produced /\
          Seq.equal st1.CS.cs_wire_log.CL.raw_received (Seq.append received0 consumed) /\
          Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced)) in
    assert (server_step #CTypes.server_local_event
      st0
      (SM.WireEvent msg)
      st1
      (CPI.step_output wire_outputs local_outputs));
    assert (server_canonical_step_rel #CTypes.server_local_event st0 st1);
    RTC.closure_step
      (server_canonical_step_rel #CTypes.server_local_event)
      st0
      st1
  ) else (
    if st1 = st0 then
      assert (server_progress_preorder #CTypes.server_local_event st0 st1)
    else (
      assert (buffer_resp.ST.response.ST.status <> ST.StepOk);
      lemma_server_network_nonstep_canonical_step
        st0 st1 buffer_resp input_contents network_out app_out;
      RTC.closure_step
        (server_canonical_step_rel #CTypes.server_local_event)
        st0
        st1
    )
  )

#pop-options
let lemma_server_local_event_progress
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        ST.server_local_event_end_to_end_correct
          st0
          st1
          resp
          kind
          payload
          network_out
          app_out)
      (ensures
        server_progress_preorder #CTypes.server_local_event st0 st1 /\
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config)
=
  ST.lemma_server_local_event_preserves_config
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  let api : CTypes.server_api_event = {
    CTypes.server_local_kind = kind;
    CTypes.server_local_payload = payload;
  } in
  let local_ev = CTypes.ServerAPI api in
  let result = CTypes.server_local_process_result resp in
  let wire_outputs = server_response_wire_outputs resp network_out in
  let local_outputs = server_response_local_outputs resp app_out in
  if result.CPI.process_status = CPI.StepOk then (
    assert (resp.ST.status == ST.StepOk);
    assert (exists ev raw_sent raw_received.
      ST.legal_local_response
        st0
        st1
        resp
        kind
        payload
        ev
        raw_sent
        raw_received
        network_out
        app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          ST.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          ST.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          ST.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    assert (ST.legal_local_response
      st0 st1 resp kind payload ev raw_sent raw_received network_out app_out);
    assert (server_api_event_matches api ev);
    assert (Seq.equal raw_sent (ST.response_network_out resp network_out));
    lemma_server_local_raw_sent_parse_success
      st0 st1 resp kind payload ev raw_sent raw_received network_out app_out;
    lemma_server_wire_outputs_match_response resp network_out raw_sent;
    assert (server_wire_outputs_match raw_sent wire_outputs);
    lemma_server_response_local_outputs_match resp ev app_out;
    assert (server_local_outputs_match ev local_outputs);
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    } st1);
    lemma_server_api_event_raw_received_empty
      st0 st1 api resp ev raw_sent raw_received network_out app_out;
    assert (Seq.equal raw_received B.empty);
    Seq.lemma_eq_elim raw_received B.empty;
    assert (SMRep.sent_event_nonempty_seal_projection
      st0.CS.cs_model ev raw_sent);
    lemma_server_step_from_local_witness
      st0 st1 local_ev ev raw_sent wire_outputs local_outputs;
    assert (server_canonical_step_rel #CTypes.server_local_event st0 st1);
    RTC.closure_step
      (server_canonical_step_rel #CTypes.server_local_event)
      st0
      st1
  ) else (
    assert (resp.ST.status <> ST.StepOk);
    assert (ST.unexpected_message_response st0 st1 resp network_out app_out);
    let err : T.tls_error = T.AlertError T.Unexpected_message in
    let conn_ev = CS.ConnLocalEvent (CS.LocalFail err) in
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    } st1);
    if st0 = st1 then
      assert (server_progress_preorder #CTypes.server_local_event st0 st1)
    else (
      CW.lemma_wire_outputs_of_empty ();
      Seq.lemma_eq_elim
        (WF.serialize_all CW.tls_record_wire_format [])
        B.empty;
      let api_fail : CTypes.server_api_event = {
        CTypes.server_local_kind = ST.LocalFail;
        CTypes.server_local_payload = B.empty;
      } in
      assert (server_api_event_matches api_fail conn_ev);
      assert (server_wire_outputs_match B.empty []);
      assert (server_local_outputs_match conn_ev []);
      assert (server_step
        st0
        (SM.LocalEvent (CTypes.ServerAPI api_fail))
        st1
        (CPI.step_output [] []));
      assert (server_canonical_step_rel #CTypes.server_local_event st0 st1);
      RTC.closure_step
        (server_canonical_step_rel #CTypes.server_local_event)
        st0
        st1
    )
  )

// Prove server_progress_preorder st0 st1 from server_local_common_witness.
// Mirrors lemma_client_local_progress in TLS13.Impl.Client.CanonicalProtocol.fst.
#restart-solver
let lemma_server_local_progress
  (initial:server_initial_state)
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
  (local_outputs:list EAPI.local_output)
  : Lemma
      (requires
        server_local_common_witness
          initial received0 sent0 st0 local_ev api old_network_out
          network_out out_len base st1 app_out resp wire_outputs local_outputs)
      (ensures
        server_progress_preorder #CTypes.server_local_event st0 st1)
  =
  let result = CTypes.server_local_process_result resp in
  let received1 = st1.CS.cs_wire_log.CL.raw_received in
  let sent1 = st1.CS.cs_wire_log.CL.raw_sent in
  if result.CPI.process_status = CPI.StepOk then (
    CPI.lemma_local_process_ok_refines_transition
      (server_system #CTypes.server_local_event initial)
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
    assert (server_canonical_step_rel #CTypes.server_local_event st0 st1);
    RTC.closure_step
      (server_canonical_step_rel #CTypes.server_local_event)
      st0
      st1
  ) else (
    // result.process_status != StepOk → resp.status != StepOk.
    // From server_local_event_end_to_end_correct → legal_handled_local_response.
    // legal_local_response requires resp.status == StepOk → contradiction.
    // So unexpected_message_response holds.
    assert (resp.ST.status <> ST.StepOk);
    assert (ST.unexpected_message_response st0 st1 resp network_out app_out);
    let err : T.tls_error = T.AlertError T.Unexpected_message in
    let conn_ev = CS.ConnLocalEvent (CS.LocalFail err) in
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    } st1);
    if st0 = st1 then
      assert (server_progress_preorder #CTypes.server_local_event st0 st1)
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
      assert (server_canonical_step_rel #CTypes.server_local_event st0 st1);
      RTC.closure_step
        (server_canonical_step_rel #CTypes.server_local_event)
        st0
        st1
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
    WS.parse_record_wire (Ghost.reveal input_contents) == None /\
    Seq.equal network_out_bytes (Ghost.reveal old_out)));
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
    exists (local_outputs:list EAPI.local_output).
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
        exists (local_outputs:list EAPI.local_output).
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
    exists (local_outputs:list EAPI.local_output).
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
    exists (local_outputs:list EAPI.local_output).
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
        exists (local_outputs:list EAPI.local_output).
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
  assert (pure (exists (local_outputs:list EAPI.local_output).
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
  let local_outputse : Ghost.erased (local_outputs:list EAPI.local_output{
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
      (list EAPI.local_output)
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
    (server_system #CTypes.server_local_event (Ghost.reveal srv.canonical_server_initial))
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
          (local_outputs:list EAPI.local_output).
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
        (server_system #CTypes.server_local_event (Ghost.reveal srv.canonical_server_initial))
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

// Runtime non-emptiness check for the configured certificate chain, used to
// discharge the [kind == LocalSendCertificate ==> 1 <= |chain|] obligation of
// [SS.lemma_server_process_local_obligations] / [process_local_event_with_
// credentials].  With the (un-weakened) plain [input_ready] carrying a reachable
// LocalSendCertificate case, this obligation is no longer vacuous, and no state
// invariant guarantees a non-empty chain; we establish it at runtime by copying
// the chain into a scratch buffer (O.copy_server_certificate_chain returns the
// exact chain length).  Mirrors Server.Driver.Local.check_certificate_chain_
// nonempty.  The None (buffer-too-small) case is impossible for a well-configured
// server (|chain| <= max_server_certificate_chain_len == 16610 < 32768) but is
// handled soundly by reporting ok = false.
fn canonical_check_certificate_chain_nonempty
  (creds:O.server_credentials)
  requires O.is_server_credentials creds 'certificate_chain 'credential_identity
  returns ok:bool
  ensures O.is_server_credentials creds 'certificate_chain 'credential_identity **
          pure (ok ==> 1 <= B.length 'certificate_chain)
{
  let chain_bytes = V.alloc 0uy 32768sz;
  with old_chain_bytes. assert (V.pts_to chain_bytes old_chain_bytes);
  assert (pure (V.is_full_vec chain_bytes));
  assert (pure (B.length old_chain_bytes == 32768));
  V.to_array_pts_to chain_bytes;
  let copy_result =
    O.copy_server_certificate_chain
      creds
      (V.vec_to_array chain_bytes)
      32768sz;
  V.to_vec_pts_to chain_bytes;
  V.free chain_bytes;
  match copy_result {
    None -> {
      false
    }
    Some written -> {
      SZ.gt written 0sz
    }
  }
}

// Credentialed local-event dispatch that first discharges the
// LocalSendCertificate [1 <= |chain|] obligation via the runtime chain-non-empty
// check above (routing the degenerate empty-chain case to the plain no-op
// process_local_event, which treats the Certificate send as an unexpected event
// and needs no chain bound).  All other kinds go straight through
// process_local_event_with_credentials after the obligations lemma.  The
// explicit postcondition lets Pulse push the goal into each branch, so the three
// leaves converge without an (unprovable) nested-match join.
fn server_dispatch_local
  (s:S.server)
  (creds:O.server_credentials)
  (kind:ST.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires S.connection_exactly s 'st0 **
           O.is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 ST.server_local_event_input_ready 'st0 kind 'payload_bytes /\
                 ST.server_local_event_input_ready_with_credentials
                   'st0 kind 'payload_bytes 'certificate_chain 'credential_identity)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          S.connection_exactly s st1 **
          O.is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0 st1 resp kind 'payload_bytes network_out_bytes app_out_bytes)
{
  if (kind = ST.LocalSendCertificate) {
    let nonempty = canonical_check_certificate_chain_nonempty creds;
    if nonempty {
      SS.lemma_server_process_local_obligations
        'st0 kind 'payload_bytes 'certificate_chain 'credential_identity
        (SZ.v network_out_len);
      S.process_local_event_with_credentials
        s creds kind
        payload payload_len
        network_out network_out_len
        app_out app_out_len
    } else {
      S.process_local_event
        s kind
        payload payload_len
        network_out network_out_len
        app_out app_out_len
    }
  } else {
    SS.lemma_server_process_local_obligations
      'st0 kind 'payload_bytes 'certificate_chain 'credential_identity
      (SZ.v network_out_len);
    S.process_local_event_with_credentials
      s creds kind
      payload payload_len
      network_out network_out_len
      app_out app_out_len
  }
}

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
  pure (
    SZ.v out_len == Seq.length (Ghost.reveal old_out) /\
    ~ (CPI.no_internal_events #CTypes.server_local_event ev))
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased B.bytes)
                (sent1:Ghost.erased B.bytes)
                (st1:Ghost.erased CS.connection_state)
                (out_contents:B.bytes)
                (wire_outputs:list CW.wire_message)
                (local_outputs:list EAPI.local_output).
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
      (server_system #CTypes.server_local_event (Ghost.reveal srv.canonical_server_initial))
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
  // Discharge the conditional obligations threaded through
  // process_local_event_with_credentials from the (un-weakened) input_ready
  // facts.  The LocalSendCertificate case additionally needs [1 <= |chain|]
  // (the new mk_cert_witness bytesize is conditional and plain input_ready no
  // longer rules the case out); no state invariant provides it, so
  // server_dispatch_local branches on a runtime chain-non-emptiness check,
  // routing the degenerate empty-chain case to the plain no-op
  // process_local_event.
  let resp =
    server_dispatch_local
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
        exists (local_outputs:list EAPI.local_output).
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
            exists (local_outputs:list EAPI.local_output).
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
      assert (pure (exists (local_outputs:list EAPI.local_output).
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
      let local_outputse : Ghost.erased (local_outputs:list EAPI.local_output{
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
          (list EAPI.local_output)
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
        (server_system #CTypes.server_local_event (Ghost.reveal srv.canonical_server_initial))
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

(* Phase 1: the TLS server has no internal events, so internal processing
   is unconditionally quiescent. *)
#restart-solver
fn server_process_internal
  (srv:canonical_server)
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
  server_internal_frame_pre
    frame
    (Ghost.reveal st0)
    out
    out_len
    (Ghost.reveal old_out) **
  pts_to out (Ghost.reveal old_out) **
  pure (SZ.v out_len == Seq.length (Ghost.reveal old_out))
returns result:CPI.internal_result
ensures exists* (received1:Ghost.erased B.bytes)
                (sent1:Ghost.erased B.bytes)
                (st1:Ghost.erased CS.connection_state)
                (out_contents:B.bytes)
                (wire_outputs:list CW.wire_message)
                (local_outputs:list EAPI.local_output).
  server_invariant
    srv
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1) **
  server_internal_frame_post
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
    CPI.internal_process_correct
      (server_system
        #CTypes.server_local_event
        (Ghost.reveal srv.canonical_server_initial))
      (CPI.no_internal_events #CTypes.server_local_event)
      (CPI.nothing_pending #CS.connection_state)
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
  let result : CPI.internal_result = {
    CPI.internal_status = CPI.InternalQuiescent;
    CPI.internal_process = {
      CPI.process_status = CPI.StepOk;
      CPI.process_consumed_len = 0sz;
      CPI.process_produced_len = 0sz;
      CPI.process_app_len = 0sz;
    };
  };
  with payload.
    assert (pts_to
      frame.tls_server_local_bridge_base.tls_server_local_payload
      payload);
  fold (server_internal_frame_post
    frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal old_out)
    (Ghost.reveal st0)
    (Ghost.reveal st0)
    ([] <: list CW.wire_message)
    ([] <: list EAPI.local_output));
  result
}

noextract
let server_protocol_implementation
  : CPI.protocol_implementation
      canonical_server
      CS.connection_state
      CW.wire_message
      CTypes.server_local_event
      EAPI.local_output
  =
  {
    CPI.pi_system =
      (fun srv -> server_system #CTypes.server_local_event (Ghost.reveal srv.canonical_server_initial));
    CPI.pi_internal = CPI.no_internal_events #CTypes.server_local_event;
    CPI.pi_internal_pending = CPI.nothing_pending #CS.connection_state;
    CPI.pi_invariant = server_invariant;
    CPI.pi_snapshot = server_snapshot;
    CPI.pi_network_frame = tls_server_network_bridge_frame;
    CPI.pi_network_frame_pre = server_network_bridge_frame_pre;
    CPI.pi_network_frame_post = server_network_bridge_frame_post;
    CPI.pi_local_frame = tls_server_local_bridge_frame;
    CPI.pi_local_frame_pre = server_local_bridge_frame_pre;
    CPI.pi_local_frame_post = server_local_bridge_frame_post;
    CPI.pi_internal_frame_pre = server_internal_frame_pre;
    CPI.pi_internal_frame_post = server_internal_frame_post;
    CPI.pi_invariant_valid = server_invariant_valid;
    CPI.pi_take_snapshot = take_server_snapshot;
    CPI.pi_recall_snapshot = recall_server_snapshot_for_protocol;
    CPI.pi_process_network = server_process_network;
    CPI.pi_process_local = server_process_local;
    CPI.pi_process_internal = server_process_internal;
  }
