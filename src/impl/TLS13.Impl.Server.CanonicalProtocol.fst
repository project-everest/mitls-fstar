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
module RVD = TLS13.Wire.Spec.RevealDecode
module RTC = FStar.ReflexiveTransitiveClosure
module S = TLS13.Impl.Server
module Seq = FStar.Seq
module SM = Common.StateMachine
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
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
      server_local_outputs_match conn_ev out.SM.so_local_outputs
  | SM.LocalEvent local ->
    (match local with
    | CTypes.ServerAPI api ->
      exists conn_ev raw_sent raw_received.
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
          st1
    | CTypes.ServerGhostStep ->
      exists delta.
        CS.legal_connection_delta st0 delta st1)

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

noeq
type canonical_server = {
  canonical_server_state: S.server;
  canonical_server_initial: Ghost.erased CS.connection_state;
  canonical_server_valid_trace:
    received:B.bytes ->
    sent:B.bytes ->
    st:CS.connection_state ->
      Lemma
        (requires
          ST.server_end_to_end_invariant st /\
          st.CS.cs_model.CS.model_config ==
            (Ghost.reveal canonical_server_initial).CS.cs_model.CS.model_config /\
          Seq.equal received st.CS.cs_wire_log.CL.raw_received /\
          Seq.equal sent st.CS.cs_wire_log.CL.raw_sent)
        (ensures
          WFSM.valid_byte_trace
            (server_system (Ghost.reveal canonical_server_initial))
            received
            st
            sent
            Seq.empty);
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
    assert (CW.wire_equal msg msg);
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
  lemma_server_network_step_ok_legal_response
    st0
    st1
    buffer_resp
    input
    network_out
    app_out;
  let msg =
    ID.indefinite_description_ghost
      M.tls_message
      (fun msg ->
        ST.legal_network_response
          st0
          st1
          resp
          msg
          consumed
          network_out
          app_out) in
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
  match ev with
  | CTypes.ServerAPI api ->
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
  | CTypes.ServerGhostStep ->
    pure False

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
  match ev with
  | CTypes.ServerAPI api ->
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
  | CTypes.ServerGhostStep ->
    pure (
      result == CTypes.server_local_process_result {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.NeedMoreInput;
      } /\
      network_out == old_network_out /\
      st1 == st0 /\
      wire_outputs == [] /\
      local_outputs == [])

let server_state_ahead
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : prop =
  CPI.state_ahead (server_system initial) st0 st1

let server_ghost_transition
  (st1:CS.connection_state)
  : SM.transition
      CS.connection_state
      CW.wire_message
      CTypes.server_local_event
      CTypes.local_output
  =
  {
    SM.tr_event = SM.LocalEvent CTypes.ServerGhostStep;
    SM.tr_next_state = st1;
    SM.tr_output = CPI.step_output [] [];
  }

let lemma_server_connection_step_state_ahead
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires CS.connection_state_single_step st0 st1)
      (ensures server_state_ahead initial st0 st1)
=
  let delta =
    ID.indefinite_description_ghost
      CS.connection_delta
      (fun delta -> CS.legal_connection_delta st0 delta st1) in
  let tr = server_ghost_transition st1 in
  assert (server_step
    st0
    (SM.LocalEvent CTypes.ServerGhostStep)
    st1
    tr.SM.tr_output);
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

let lemma_server_connection_state_evolves_state_ahead
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires CS.connection_state_evolves st0 st1)
      (ensures server_state_ahead initial st0 st1)
=
  RTC.induct
    CS.connection_state_single_step
    (fun x y -> server_state_ahead initial x y)
    (fun x ->
      SM.lemma_state_evolves_refl
        (server_system initial).WFSM.wfsm_state_machine
        x)
    (fun x y ->
      lemma_server_connection_step_state_ahead initial x y)
    (fun x y z ->
      SM.lemma_state_evolves_trans
        (server_system initial).WFSM.wfsm_state_machine
        x
        y
        z)
    st0
    st1
    ()

let server_invariant_pure
  (initial:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  : prop =
  ST.server_end_to_end_invariant st /\
  st.CS.cs_model.CS.model_config == initial.CS.cs_model.CS.model_config /\
  Seq.equal received st.CS.cs_wire_log.CL.raw_received /\
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent

let server_invariant
  (srv:canonical_server)
  (received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  : slprop =
  S.connection_exactly srv.canonical_server_state st **
  pure (server_invariant_pure
    (Ghost.reveal srv.canonical_server_initial)
    received
    sent
    st)

[@@pulse_unfold]
let server_snapshot
  (srv:canonical_server)
  (_received:B.bytes)
  (_sent:B.bytes)
  (st:CS.connection_state)
  : slprop =
  MR.snapshot (S.server_state_ref srv.canonical_server_state) st

fn server_invariant_valid
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
  srv.canonical_server_valid_trace
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
  fold (server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st))
}

fn take_server_snapshot
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
  unfold (S.connection_exactly
    srv.canonical_server_state
    (Ghost.reveal st));
  MR.take_snapshot
    (S.server_state_ref srv.canonical_server_state)
    (Ghost.reveal st);
  fold (S.connection_exactly
    srv.canonical_server_state
    (Ghost.reveal st));
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

fn recall_server_snapshot
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
      (Ghost.reveal current_state))
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
  unfold (S.connection_exactly
    srv.canonical_server_state
    (Ghost.reveal current_state));
  MR.recall_snapshot
    (S.server_state_ref srv.canonical_server_state);
  lemma_server_connection_state_evolves_state_ahead
    (Ghost.reveal srv.canonical_server_initial)
    (Ghost.reveal snapshot_state)
    (Ghost.reveal current_state);
  assert (pure (CPI.state_ahead
    (server_system (Ghost.reveal srv.canonical_server_initial))
    (Ghost.reveal snapshot_state)
    (Ghost.reveal current_state)));
  fold (S.connection_exactly
    srv.canonical_server_state
    (Ghost.reveal current_state));
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
      app_out
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
    (CTypes.ServerAPI api)
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
  forall initial received0 sent0 st0 api old_network_out network_out out_len
         st1 app_out resp.
    server_invariant_pure initial received0 sent0 st0 /\
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
  match ev with
  | CTypes.ServerAPI api ->
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
  | CTypes.ServerGhostStep ->
    emp

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
  match ev {
    CTypes.ServerAPI api -> {
      let resp =
        S.process_local_event
          srv.canonical_server_state
          api.CTypes.server_local_kind
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
      assert (pure (B.length api.CTypes.server_local_payload ==
        SZ.v frame.tls_server_local_bridge_base.tls_server_local_payload_len));
      assert (pure (ST.server_local_event_input_ready
        (Ghost.reveal st0)
        api.CTypes.server_local_kind
        api.CTypes.server_local_payload));
      assert (pure (ST.server_local_event_end_to_end_correct
        (Ghost.reveal st0)
        st1
        resp
        api.CTypes.server_local_kind
        api.CTypes.server_local_payload
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
        api
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
            api
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
              api
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
          api
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
          api
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
              api
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
        api
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
      with app_out_bytes.
      fold (server_local_bridge_frame_post
        (CTypes.ServerAPI api)
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
          (CTypes.ServerAPI api)
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
    CTypes.ServerGhostStep -> {
      assert (pure False);
      let dummy_result = CTypes.server_local_process_result {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.NeedMoreInput;
      };
      fold (server_invariant
        srv
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0));
      fold (server_local_bridge_frame_post
        CTypes.ServerGhostStep
        frame
        dummy_result
        (Ghost.reveal old_out)
        (Ghost.reveal old_out)
        (Ghost.reveal st0)
        (Ghost.reveal st0)
        []
        []);
      rewrite
        (server_local_bridge_frame_post
          CTypes.ServerGhostStep
          frame
          dummy_result
          (Ghost.reveal old_out)
          (Ghost.reveal old_out)
          (Ghost.reveal st0)
          (Ghost.reveal st0)
          []
          [])
        as
        (server_local_bridge_frame_post
          ev
          frame
          dummy_result
          (Ghost.reveal old_out)
          (Ghost.reveal old_out)
          (Ghost.reveal st0)
          (Ghost.reveal st0)
          []
          []);
      assert (pure (CPI.local_process_correct
        (server_system (Ghost.reveal srv.canonical_server_initial))
        ev
        (Ghost.reveal old_out)
        (Ghost.reveal old_out)
        out_len
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)
        dummy_result
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)
        []
        []));
      dummy_result
    }
  }
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
