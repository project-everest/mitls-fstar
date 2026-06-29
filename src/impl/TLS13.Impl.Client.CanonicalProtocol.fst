module TLS13.Impl.Client.CanonicalProtocol

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Impl.Client
module CL = TLS13.ConnectionLog
module CPI = Common.ProtocolImplementation
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.ConnectionState
module CT = TLS13.Impl.Client.Types
module CW = TLS13.Impl.CanonicalWire
module CTypes = TLS13.Impl.CanonicalTypes
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Pre = FStar.Preorder
module RVD = TLS13.Wire.Spec.RevealDecode
module RTC = FStar.ReflexiveTransitiveClosure
module Seq = FStar.Seq
module SM = Common.StateMachine
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module WS = TLS13.Wire.Spec

(**
  Canonical Common.ProtocolImplementation boundary for the low-level client.

  This file contains the auditable state-machine/invariant/snapshot boundary
  and the low-level Pulse operations packaged as a [CPI.protocol_implementation].
  The remaining endpoint-spec-to-common network proof is carried explicitly by
  [tls_client_network_bridge_frame], keeping the proof obligation local to each
  operation frame instead of weakening the common class.
 **)

let client_local_outputs_match
  (ev:CS.conn_event)
  (outs:list CTypes.local_output)
  : prop =
  Seq.equal
    (CTypes.local_outputs_app_bytes outs)
    (CL.concat_bytes (CS.conn_event_app_received_delta ev))

let client_wire_outputs_match
  (raw_sent:B.bytes)
  (outs:list CW.wire_message)
  : prop =
  Seq.equal
    (WF.serialize_all CW.tls_record_wire_format outs)
    raw_sent

let client_api_event_matches
  (st0:CS.connection_state)
  (api:CTypes.client_api_event)
  (ev:CS.conn_event)
  : prop =
  CT.local_event_kind_matches
    st0
    api.CTypes.client_local_kind
    api.CTypes.client_local_payload
    ev

let client_step
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.client_local_event)
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
      client_local_outputs_match conn_ev out.SM.so_local_outputs
  | SM.LocalEvent local ->
    let api = CTypes.client_local_event_api local in
      exists conn_ev raw_sent raw_received.
        client_api_event_matches st0 api conn_ev /\
        client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
        client_local_outputs_match conn_ev out.SM.so_local_outputs /\
        CS.legal_connection_delta
          st0
          {
            CS.delta_event = conn_ev;
            CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = raw_received;
          }
           st1

noextract
let client_state_machine
  (initial:CS.connection_state)
  : SM.state_machine
      CS.connection_state
      CW.wire_message
      CTypes.client_local_event
      CTypes.local_output
  =
  {
    SM.sm_initial_state = initial;
    SM.sm_step = client_step;
  }

noextract
let client_system
  (initial:CS.connection_state)
  : WFSM.wire_format_state_machine
      CS.connection_state
      CW.wire_message
      CTypes.client_local_event
      CTypes.local_output
  =
  {
    WFSM.wfsm_state_machine = client_state_machine initial;
    WFSM.wfsm_wire_format = CW.tls_record_wire_format;
  }

let client_canonical_step_rel
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : prop =
  exists ev out. client_step st0 ev st1 out

let client_progress_preorder =
  RTC.closure client_canonical_step_rel

noeq
type canonical_client = {
  canonical_client_state: C.client;
  canonical_client_progress: MR.mref client_progress_preorder;
  canonical_client_initial: Ghost.erased CS.connection_state;
  canonical_client_valid_trace:
    received:B.bytes ->
    sent:B.bytes ->
    st:CS.connection_state ->
      Lemma
        (requires
          CT.client_end_to_end_invariant st /\
          st.CS.cs_model.CS.model_config ==
            (Ghost.reveal canonical_client_initial).CS.cs_model.CS.model_config /\
          Seq.equal received st.CS.cs_wire_log.CL.raw_received /\
          Seq.equal sent st.CS.cs_wire_log.CL.raw_sent)
        (ensures
          WFSM.valid_byte_trace
            (client_system (Ghost.reveal canonical_client_initial))
            received
            st
            sent
            Seq.empty);
}

noeq
type tls_client_network_frame = {
  tls_client_network_app_out: array U8.t;
  tls_client_network_app_out_len: SZ.t;
  tls_client_network_old_app_out: Ghost.erased B.bytes;
}

noeq
type tls_client_local_frame = {
  tls_client_local_payload: array U8.t;
  tls_client_local_payload_len: SZ.t;
  tls_client_local_app_out: array U8.t;
  tls_client_local_app_out_len: SZ.t;
  tls_client_local_old_app_out: Ghost.erased B.bytes;
}

let client_response_wire_outputs
  (resp:CT.client_response)
  (network_out:B.bytes)
  : GTot (list CW.wire_message) =
  CW.wire_outputs_of_full_record (CT.response_network_out resp network_out)

let client_response_local_outputs
  (resp:CT.client_response)
  (app_out:B.bytes)
  : GTot (list CTypes.local_output) =
  CTypes.local_outputs_of_app_bytes (CT.response_app_out resp app_out)

let lemma_client_response_wire_outputs_serializes
  (resp:CT.client_response)
  (network_out:B.bytes)
  : Lemma
      (requires
        SZ.v resp.CT.network_out_len <= B.length network_out /\
        CT.response_network_out_parse_success resp network_out)
      (ensures
        Seq.equal
          (WF.serialize_all
            CW.tls_record_wire_format
            (client_response_wire_outputs resp network_out))
          (CT.response_network_out resp network_out))
=
  let raw = CT.response_network_out resp network_out in
  if resp.CT.network_out_len = 0sz then (
    Seq.lemma_len_slice network_out 0 0;
    Seq.lemma_eq_intro raw B.empty;
    CW.lemma_wire_outputs_of_empty ()
  ) else (
    assert (exists outer_ct outer_fragment.
      WS.parse_record raw ==
        Some (outer_ct, outer_fragment, SZ.v resp.CT.network_out_len));
    let outer_ct =
      FStar.IndefiniteDescription.indefinite_description_ghost
        T.content_type
        (fun outer_ct -> exists outer_fragment.
          WS.parse_record raw ==
            Some (outer_ct, outer_fragment, SZ.v resp.CT.network_out_len)) in
    let outer_fragment =
      FStar.IndefiniteDescription.indefinite_description_ghost
        M.sealed_record
        (fun outer_fragment ->
          WS.parse_record raw ==
            Some (outer_ct, outer_fragment, SZ.v resp.CT.network_out_len)) in
    assert (SZ.v resp.CT.network_out_len <= B.length network_out);
    Seq.lemma_len_slice network_out 0 (SZ.v resp.CT.network_out_len);
    assert (B.length raw == SZ.v resp.CT.network_out_len);
    WS.lemma_parse_record_implies_parse_record_wire raw;
    assert (WS.parse_record_wire raw ==
      Some (outer_ct, outer_fragment, B.length raw));
    CW.lemma_wire_outputs_of_full_record_serializes
      raw
      outer_ct
      outer_fragment
  )

let lemma_client_consumed_prefix_parse
  (input:B.bytes)
  (consumed_len:SZ.t)
  : Lemma
      (requires
        SZ.v consumed_len <= B.length input /\
        CT.raw_record_parse_success
          (CT.network_consumed_prefix input consumed_len))
      (ensures
        exists msg residual.
          CPI.consumed_by_parse
            CW.tls_record_wire_format
            input
            msg
            (CT.network_consumed_prefix input consumed_len)
            residual)
=
  let consumed = CT.network_consumed_prefix input consumed_len in
  assert (consumed == Seq.slice input 0 (SZ.v consumed_len));
  assert (exists outer_ct outer_fragment.
    WS.parse_record_wire consumed ==
      Some (outer_ct, outer_fragment, B.length consumed));
  let outer_ct =
    FStar.IndefiniteDescription.indefinite_description_ghost
      T.content_type
      (fun outer_ct -> exists outer_fragment.
        WS.parse_record_wire consumed ==
          Some (outer_ct, outer_fragment, B.length consumed)) in
  let outer_fragment =
    FStar.IndefiniteDescription.indefinite_description_ghost
      M.sealed_record
      (fun outer_fragment ->
        WS.parse_record_wire consumed ==
          Some (outer_ct, outer_fragment, B.length consumed)) in
  Seq.lemma_len_slice input 0 (SZ.v consumed_len);
  assert (B.length consumed == SZ.v consumed_len);
  RVD.lemma_parse_record_wire_from_prefix
    input
    outer_ct
    outer_fragment
    (SZ.v consumed_len);
  let residual = Seq.slice input (SZ.v consumed_len) (B.length input) in
  Seq.lemma_split input (SZ.v consumed_len);
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
    assert (exists msg' residual'.
      CPI.consumed_by_parse
        CW.tls_record_wire_format
        input
        msg'
        consumed
        residual')
  | None ->
    assert False

let lemma_client_response_local_outputs_match
  (resp:CT.client_response)
  (ev:CS.conn_event)
  (app_out:B.bytes)
  : Lemma
      (requires CT.response_app_out_matches_event resp ev app_out)
      (ensures
        client_local_outputs_match
          ev
          (client_response_local_outputs resp app_out))
=
  let app_bytes = CT.response_app_out resp app_out in
  CTypes.lemma_local_outputs_of_app_bytes_exact app_bytes;
  Seq.lemma_eq_elim
    app_bytes
    (CT.event_api_app_out ev)

let lemma_client_response_output_written
  (resp:CT.client_response)
  (network_out:B.bytes)
  : Lemma
      (requires
        SZ.v resp.CT.network_out_len <= B.length network_out /\
        CT.response_network_out_parse_success resp network_out)
      (ensures
        CPI.output_written
          network_out
          resp.CT.network_out_len
          (WF.serialize_all
            CW.tls_record_wire_format
            (client_response_wire_outputs resp network_out)))
=
  lemma_client_response_wire_outputs_serializes resp network_out;
  let produced =
    WF.serialize_all
      CW.tls_record_wire_format
      (client_response_wire_outputs resp network_out) in
  let raw = CT.response_network_out resp network_out in
  assert (Seq.equal produced raw);
  Seq.lemma_len_slice network_out 0 (SZ.v resp.CT.network_out_len);
  assert (B.length raw == SZ.v resp.CT.network_out_len);
  assert (Seq.equal
    (CPI.output_prefix network_out resp.CT.network_out_len)
    raw);
  Seq.lemma_eq_elim produced raw;
  assert (CPI.output_written network_out resp.CT.network_out_len produced)

let lemma_client_api_event_raw_received_empty
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (api:CTypes.client_api_event)
  (resp:CT.client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        CT.legal_local_response
          st0
          st1
          resp
          api.CTypes.client_local_kind
          api.CTypes.client_local_payload
          ev
          raw_sent
          raw_received
          network_out
          app_out)
      (ensures Seq.equal raw_received B.empty)
=
  assert (CT.local_event_kind_matches
    st0
    api.CTypes.client_local_kind
    api.CTypes.client_local_payload
    ev);
  assert (CT.legal_response_for_event
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
    match api.CTypes.client_local_kind with
    | CT.LocalSendApplicationData
    | CT.LocalSendClientHello
    | CT.LocalSendClientFinished
    | CT.LocalSendCloseNotify
    | CT.LocalSendKeyUpdate ->
      assert (msg.CL.message_direction == CL.Sent)
    | _ ->
      assert False

let lemma_client_local_handled_response_raw_progress
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (api:CTypes.client_api_event)
  (resp:CT.client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        CT.legal_handled_local_response
          st0
          st1
          resp
          api.CTypes.client_local_kind
          api.CTypes.client_local_payload
          network_out
          app_out)
      (ensures
        exists ev raw_sent.
          CT.legal_response_for_event
            st0
            st1
            resp
            ev
            raw_sent
            B.empty
            network_out
            app_out /\
          Seq.equal raw_sent (CT.response_network_out resp network_out))
=
  if (exists ev raw_sent raw_received.
      CT.legal_local_response
        st0
        st1
        resp
        api.CTypes.client_local_kind
        api.CTypes.client_local_payload
        ev
        raw_sent
        raw_received
        network_out
        app_out)
  then (
    let ev =
      FStar.IndefiniteDescription.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          CT.legal_local_response
            st0
            st1
            resp
            api.CTypes.client_local_kind
            api.CTypes.client_local_payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    let raw_sent =
      FStar.IndefiniteDescription.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          CT.legal_local_response
            st0
            st1
            resp
            api.CTypes.client_local_kind
            api.CTypes.client_local_payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    let raw_received =
      FStar.IndefiniteDescription.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          CT.legal_local_response
            st0
            st1
            resp
            api.CTypes.client_local_kind
            api.CTypes.client_local_payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    assert (CT.legal_local_response
      st0
      st1
      resp
      api.CTypes.client_local_kind
      api.CTypes.client_local_payload
      ev
      raw_sent
      raw_received
      network_out
      app_out);
    lemma_client_api_event_raw_received_empty
      st0
      st1
      api
      resp
      ev
      raw_sent
      raw_received
      network_out
      app_out;
    assert (CT.legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    Seq.lemma_eq_elim raw_received B.empty;
    assert (Seq.equal raw_sent (CT.response_network_out resp network_out));
    assert (exists ev' raw_sent'.
      CT.legal_response_for_event
        st0
        st1
        resp
        ev'
        raw_sent'
        B.empty
        network_out
        app_out /\
      Seq.equal raw_sent' (CT.response_network_out resp network_out))
  ) else if CT.unexpected_message_response st0 st1 resp network_out app_out then (
    assert (CT.legal_response_for_event
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error))
      B.empty
      B.empty
      network_out
      app_out);
    assert (Seq.equal B.empty (CT.response_network_out resp network_out));
    assert (exists ev' raw_sent'.
      CT.legal_response_for_event
        st0
        st1
        resp
        ev'
        raw_sent'
        B.empty
        network_out
        app_out /\
      Seq.equal raw_sent' (CT.response_network_out resp network_out))
  ) else (
    assert (CT.bad_finished_response st0 st1 resp network_out app_out);
    assert (CT.legal_response_for_event
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_bad_finished_error))
      B.empty
      B.empty
      network_out
      app_out);
    assert (Seq.equal B.empty (CT.response_network_out resp network_out));
    assert (exists ev' raw_sent'.
      CT.legal_response_for_event
        st0
        st1
        resp
        ev'
        raw_sent'
        B.empty
        network_out
        app_out /\
      Seq.equal raw_sent' (CT.response_network_out resp network_out))
  )

// Prove client_canonical_step_rel from a local event step where the state changed.
// Covers three sub-cases from legal_handled_local_response:
//   Case 1 – legal_local_response    → regular LocalEvent step with the original api
//   Case 2 – unexpected_message_response → LocalFail (tls_unexpected_message_error)
//   Case 3 – bad_finished_response   → LocalFail (tls_bad_finished_error)
let lemma_client_local_canonical_step
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (api:CTypes.client_api_event)
  (resp:CT.client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        CT.local_event_step_correct
          st0 st1 resp
          api.CTypes.client_local_kind
          api.CTypes.client_local_payload
          network_out
          app_out /\
        st0 <> st1)
      (ensures client_canonical_step_rel st0 st1)
  =
  let kind = api.CTypes.client_local_kind in
  let payload = api.CTypes.client_local_payload in
  assert (CT.legal_handled_local_response st0 st1 resp kind payload network_out app_out);
  assert (CT.response_network_out_parse_success resp network_out);
  // Inner helper: construct a LocalFail canonical step from a legal_delta
  let lemma_localfail_step
    (err:T.tls_error)
    : Lemma
        (requires CT.legal_delta st0 st1 (CS.ConnLocalEvent (CS.LocalFail err)) B.empty B.empty)
        (ensures client_canonical_step_rel st0 st1)
    =
    CW.lemma_wire_outputs_of_empty ();
    Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format []) B.empty;
    let api_fail : CTypes.client_api_event = {
      CTypes.client_local_kind = CT.LocalFail;
      CTypes.client_local_payload = B.empty;
    } in
    let conn_ev = CS.ConnLocalEvent (CS.LocalFail err) in
    assert (client_api_event_matches st0 api_fail conn_ev);
    assert (client_wire_outputs_match B.empty []);
    assert (client_local_outputs_match conn_ev []);
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    } st1);
    assert (client_step st0 (SM.LocalEvent (CTypes.ClientAPI api_fail)) st1 (CPI.step_output [] []))
  in
  if (exists ev raw_sent raw_received.
      CT.legal_local_response st0 st1 resp kind payload ev raw_sent raw_received network_out app_out)
  then (
    // Case 1: there exists a regular local event matching the api
    let ev =
      FStar.IndefiniteDescription.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          CT.legal_local_response st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_sent =
      FStar.IndefiniteDescription.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          CT.legal_local_response st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_received =
      FStar.IndefiniteDescription.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          CT.legal_local_response st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    assert (CT.legal_local_response st0 st1 resp kind payload ev raw_sent raw_received network_out app_out);
    assert (CT.local_event_kind_matches st0 kind payload ev);
    assert (client_api_event_matches st0 api ev);
    assert (CT.legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out);
    lemma_client_api_event_raw_received_empty st0 st1 api resp ev raw_sent raw_received network_out app_out;
    Seq.lemma_eq_elim raw_received B.empty;
    // Establish response_wf for lemma_client_response_wire_outputs_serializes
    assert (CT.response_wf resp network_out app_out);
    assert (SZ.v resp.CT.network_out_len <= B.length network_out);
    let wire_outputs = client_response_wire_outputs resp network_out in
    let local_outputs = client_response_local_outputs resp app_out in
    lemma_client_response_wire_outputs_serializes resp network_out;
    assert (Seq.equal (WF.serialize_all CW.tls_record_wire_format wire_outputs)
              (CT.response_network_out resp network_out));
    assert (Seq.equal raw_sent (CT.response_network_out resp network_out));
    // Make raw_sent propositionally equal to response_network_out so that
    // Z3 can substitute in client_wire_outputs_match
    Seq.lemma_eq_elim raw_sent (CT.response_network_out resp network_out);
    Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format wire_outputs) raw_sent;
    assert (client_wire_outputs_match raw_sent wire_outputs);
    assert (CT.response_app_out_matches_event resp ev app_out);
    lemma_client_response_local_outputs_match resp ev app_out;
    assert (client_local_outputs_match ev local_outputs);
    // From legal_response_for_event + raw_received == B.empty
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = B.empty;
    } st1);
    assert (client_step st0 (SM.LocalEvent (CTypes.ClientAPI api)) st1 (CPI.step_output wire_outputs local_outputs))
  ) else if CT.unexpected_message_response st0 st1 resp network_out app_out then (
    // Case 2: unexpected_message_response → LocalFail (tls_unexpected_message_error)
    assert (CT.legal_delta st0 st1
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error))
      B.empty B.empty);
    lemma_localfail_step CT.tls_unexpected_message_error
  ) else (
    // Case 3: bad_finished_response → LocalFail (tls_bad_finished_error)
    assert (CT.bad_finished_response st0 st1 resp network_out app_out);
    assert (CT.legal_delta st0 st1
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_bad_finished_error))
      B.empty B.empty);
    lemma_localfail_step CT.tls_bad_finished_error
  )

// Prove client_progress_preorder st0 st1 from local_event_end_to_end_correct.
// If st0 == st1 the preorder is reflexive; otherwise we construct a canonical step.
let lemma_client_local_progress
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (api:CTypes.client_api_event)
  (resp:CT.client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        CT.local_event_end_to_end_correct
          st0 st1 resp
          api.CTypes.client_local_kind
          api.CTypes.client_local_payload
          network_out
          app_out)
      (ensures client_progress_preorder st0 st1)
  =
  if st0 = st1 then
    assert (client_progress_preorder st0 st1)
  else (
    lemma_client_local_canonical_step st0 st1 api resp network_out app_out;
    RTC.closure_step client_canonical_step_rel st0 st1
  )

let lemma_client_local_step_ok_process_correct
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (local_ev:CTypes.client_local_event)
  (api:CTypes.client_api_event)
  (resp:CT.client_response)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (app_out:B.bytes)
  (received0:B.bytes)
  (sent0:B.bytes)
  : Lemma
      (requires
        CT.local_event_end_to_end_correct
          st0
          st1
          resp
          api.CTypes.client_local_kind
          api.CTypes.client_local_payload
          network_out
          app_out /\
        api == CTypes.client_local_event_api local_ev /\
        resp.CT.status == CT.StepOk /\
        SZ.v out_len == B.length old_network_out /\
        B.length network_out == B.length old_network_out /\
        Seq.equal received0 st0.CS.cs_wire_log.CL.raw_received /\
        Seq.equal sent0 st0.CS.cs_wire_log.CL.raw_sent)
      (ensures
        CPI.local_process_correct
          (client_system initial)
          local_ev
          old_network_out
          network_out
          out_len
          received0
          sent0
          st0
          (CTypes.client_local_process_result resp)
          st1.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_sent
          st1
          (client_response_wire_outputs resp network_out)
          (client_response_local_outputs resp app_out))
=
  let wire_outputs = client_response_wire_outputs resp network_out in
  let local_outputs = client_response_local_outputs resp app_out in
  assert (CT.local_event_step_correct
    st0
    st1
    resp
    api.CTypes.client_local_kind
    api.CTypes.client_local_payload
    network_out
    app_out);
  assert (CT.some_legal_response st0 st1 resp network_out app_out);
  assert (CT.legal_handled_local_response
    st0
    st1
    resp
    api.CTypes.client_local_kind
    api.CTypes.client_local_payload
    network_out
    app_out);
  assert (CT.response_network_out_parse_success resp network_out);
  assert (exists some_ev some_raw_sent some_raw_received.
    CT.legal_response_for_event
      st0
      st1
      resp
      some_ev
      some_raw_sent
      some_raw_received
      network_out
      app_out);
  let some_ev =
    FStar.IndefiniteDescription.indefinite_description_ghost
      CS.conn_event
      (fun ev -> exists raw_sent raw_received.
        CT.legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out) in
  let some_raw_sent =
    FStar.IndefiniteDescription.indefinite_description_ghost
      B.bytes
      (fun raw_sent -> exists raw_received.
        CT.legal_response_for_event
          st0 st1 resp some_ev raw_sent raw_received network_out app_out) in
  let some_raw_received =
    FStar.IndefiniteDescription.indefinite_description_ghost
      B.bytes
      (fun raw_received ->
        CT.legal_response_for_event
          st0 st1 resp some_ev some_raw_sent raw_received network_out app_out) in
  assert (CT.legal_response_for_event
    st0 st1 resp some_ev some_raw_sent some_raw_received network_out app_out);
  assert (CT.response_wf resp network_out app_out);
  lemma_client_response_wire_outputs_serializes resp network_out;
  lemma_client_response_local_outputs_match resp some_ev app_out;
  if (exists ev raw_sent raw_received.
      CT.legal_local_response
        st0
        st1
        resp
        api.CTypes.client_local_kind
        api.CTypes.client_local_payload
        ev
        raw_sent
        raw_received
        network_out
        app_out)
  then (
    let ev =
      FStar.IndefiniteDescription.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          CT.legal_local_response
            st0
            st1
            resp
            api.CTypes.client_local_kind
            api.CTypes.client_local_payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    let raw_sent =
      FStar.IndefiniteDescription.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          CT.legal_local_response
            st0
            st1
            resp
            api.CTypes.client_local_kind
            api.CTypes.client_local_payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    let raw_received =
      FStar.IndefiniteDescription.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          CT.legal_local_response
            st0
            st1
            resp
            api.CTypes.client_local_kind
            api.CTypes.client_local_payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    assert (CT.legal_local_response
      st0
      st1
      resp
      api.CTypes.client_local_kind
      api.CTypes.client_local_payload
      ev
      raw_sent
      raw_received
      network_out
      app_out);
    assert (client_api_event_matches st0 api ev);
    assert (CT.legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    assert (Seq.equal raw_sent (CT.response_network_out resp network_out));
    assert (CT.response_app_out_matches_event resp ev app_out);
    lemma_client_response_local_outputs_match resp ev app_out;
    Seq.lemma_eq_elim
      raw_sent
      (CT.response_network_out resp network_out);
    assert (client_wire_outputs_match raw_sent wire_outputs);
    assert (client_local_outputs_match ev local_outputs);
    assert (CS.legal_connection_delta
      st0
      {
        CS.delta_event = ev;
        CS.delta_raw_sent = raw_sent;
        CS.delta_raw_received = raw_received;
      }
      st1);
    lemma_client_api_event_raw_received_empty
      st0
      st1
      api
      resp
      ev
      raw_sent
      raw_received
      network_out
      app_out;
    CL.lemma_append_empty_right st0.CS.cs_wire_log.CL.raw_received;
    Seq.lemma_eq_elim received0 st0.CS.cs_wire_log.CL.raw_received;
    Seq.lemma_eq_elim sent0 st0.CS.cs_wire_log.CL.raw_sent;
    assert (Seq.equal
      st1.CS.cs_wire_log.CL.raw_received
      received0);
    assert (Seq.equal
      st1.CS.cs_wire_log.CL.raw_sent
      (Seq.append sent0 raw_sent));
    assert ((CPI.step_output wire_outputs local_outputs).SM.so_wire_outputs ==
      wire_outputs);
    assert ((CPI.step_output wire_outputs local_outputs).SM.so_local_outputs ==
      local_outputs);
    assert (
      client_api_event_matches st0 api ev /\
      client_wire_outputs_match raw_sent wire_outputs /\
      client_local_outputs_match ev local_outputs /\
      CS.legal_connection_delta
        st0
        {
          CS.delta_event = ev;
          CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = raw_received;
        }
        st1);
    assert (exists conn_ev raw_sent' raw_received'.
      client_api_event_matches st0 api conn_ev /\
      client_wire_outputs_match raw_sent' wire_outputs /\
      client_local_outputs_match conn_ev local_outputs /\
      CS.legal_connection_delta
        st0
        {
          CS.delta_event = conn_ev;
          CS.delta_raw_sent = raw_sent';
          CS.delta_raw_received = raw_received';
        }
        st1);
    assert (client_step
      st0
      (SM.LocalEvent local_ev)
      st1
      (CPI.step_output wire_outputs local_outputs));
    let produced =
      WF.serialize_all CW.tls_record_wire_format wire_outputs in
    assert (Seq.equal produced (CT.response_network_out resp network_out));
    assert (SZ.v resp.CT.network_out_len <= B.length network_out);
    assert (B.length produced == SZ.v resp.CT.network_out_len);
    assert (Seq.equal
      (CPI.output_prefix network_out resp.CT.network_out_len)
      produced);
    assert (CPI.output_written
      network_out
      resp.CT.network_out_len
      produced);
    Seq.lemma_eq_elim raw_sent produced;
    assert (Seq.equal
      st1.CS.cs_wire_log.CL.raw_sent
      (Seq.append sent0 produced));
    assert (CTypes.client_local_process_result resp).CPI.process_status == CPI.StepOk;
    assert (exists produced'.
      client_step
        st0
        (SM.LocalEvent local_ev)
        st1
        (CPI.step_output wire_outputs local_outputs) /\
      Seq.equal
        produced'
        (WF.serialize_all CW.tls_record_wire_format wire_outputs) /\
      CPI.output_written
        network_out
        (CTypes.client_local_process_result resp).CPI.process_produced_len
        produced' /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_received received0 /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced'));
    assert (CPI.local_process_correct
      (client_system initial)
      local_ev
      old_network_out
      network_out
      out_len
      received0
      sent0
      st0
      (CTypes.client_local_process_result resp)
      st1.CS.cs_wire_log.CL.raw_received
      st1.CS.cs_wire_log.CL.raw_sent
      st1
      wire_outputs
      local_outputs)
  ) else (
    if CT.unexpected_message_response st0 st1 resp network_out app_out then (
      assert (resp.CT.status == CT.IllegalTransition);
      assert False
    ) else (
      assert (CT.bad_finished_response st0 st1 resp network_out app_out);
      assert (resp.CT.status == CT.ConnectionFailed);
      assert False
    )
  )

let lemma_client_local_rejected_process_correct
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (local_ev:CTypes.client_local_event)
  (api:CTypes.client_api_event)
  (resp:CT.client_response)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (app_out:B.bytes)
  (received0:B.bytes)
  (sent0:B.bytes)
  : Lemma
      (requires
        CT.local_event_end_to_end_correct
          st0
          st1
          resp
          api.CTypes.client_local_kind
          api.CTypes.client_local_payload
          network_out
          app_out /\
        api == CTypes.client_local_event_api local_ev /\
        (resp.CT.status == CT.IllegalTransition \/
         resp.CT.status == CT.ConnectionFailed) /\
        SZ.v out_len == B.length old_network_out /\
        B.length network_out == B.length old_network_out /\
        Seq.equal received0 st0.CS.cs_wire_log.CL.raw_received /\
        Seq.equal sent0 st0.CS.cs_wire_log.CL.raw_sent)
      (ensures
        CPI.local_process_correct
          (client_system initial)
          local_ev
          old_network_out
          network_out
          out_len
          received0
          sent0
          st0
          (CTypes.client_local_process_result resp)
          st1.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_sent
          st1
          (client_response_wire_outputs resp network_out)
          (client_response_local_outputs resp app_out))
=
  let wire_outputs = client_response_wire_outputs resp network_out in
  let local_outputs = client_response_local_outputs resp app_out in
  assert (CT.local_event_step_correct
    st0
    st1
    resp
    api.CTypes.client_local_kind
    api.CTypes.client_local_payload
    network_out
    app_out);
  assert (CT.legal_handled_local_response
    st0
    st1
    resp
    api.CTypes.client_local_kind
    api.CTypes.client_local_payload
    network_out
    app_out);
  assert (CT.response_network_out_parse_success resp network_out);
  lemma_client_local_handled_response_raw_progress
    st0
    st1
    api
    resp
    network_out
    app_out;
  assert (exists ev raw_sent.
    CT.legal_response_for_event
      st0
      st1
      resp
      ev
      raw_sent
      B.empty
      network_out
      app_out /\
    Seq.equal raw_sent (CT.response_network_out resp network_out));
  let ev =
    FStar.IndefiniteDescription.indefinite_description_ghost
      CS.conn_event
      (fun ev -> exists raw_sent.
        CT.legal_response_for_event
          st0
          st1
          resp
          ev
          raw_sent
          B.empty
          network_out
          app_out /\
        Seq.equal raw_sent (CT.response_network_out resp network_out)) in
  let raw_sent =
    FStar.IndefiniteDescription.indefinite_description_ghost
      B.bytes
      (fun raw_sent ->
        CT.legal_response_for_event
          st0
          st1
          resp
          ev
          raw_sent
          B.empty
          network_out
          app_out /\
        Seq.equal raw_sent (CT.response_network_out resp network_out)) in
  assert (CT.legal_response_for_event
    st0 st1 resp ev raw_sent B.empty network_out app_out);
  assert (Seq.equal raw_sent (CT.response_network_out resp network_out));
  assert (CT.response_wf resp network_out app_out);
  lemma_client_response_output_written resp network_out;
  let produced = WF.serialize_all CW.tls_record_wire_format wire_outputs in
  assert (Seq.equal produced (CT.response_network_out resp network_out));
  assert (CS.legal_connection_delta
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = B.empty;
    }
    st1);
  CL.lemma_append_empty_right st0.CS.cs_wire_log.CL.raw_received;
  Seq.lemma_eq_elim received0 st0.CS.cs_wire_log.CL.raw_received;
  Seq.lemma_eq_elim sent0 st0.CS.cs_wire_log.CL.raw_sent;
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    received0);
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (Seq.append sent0 raw_sent));
  Seq.lemma_eq_elim raw_sent produced;
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (Seq.append sent0 produced));
  assert ((CTypes.client_local_process_result resp).CPI.process_consumed_len == 0sz);
  assert (exists produced'.
    Seq.equal
      produced'
      (WF.serialize_all CW.tls_record_wire_format wire_outputs) /\
    CPI.output_written
      network_out
      (CTypes.client_local_process_result resp).CPI.process_produced_len
      produced' /\
    Seq.equal st1.CS.cs_wire_log.CL.raw_received received0 /\
    Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced'));
  assert (CPI.local_process_correct
    (client_system initial)
    local_ev
    old_network_out
    network_out
    out_len
    received0
    sent0
    st0
    (CTypes.client_local_process_result resp)
    st1.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_sent
    st1
    wire_outputs
    local_outputs)

[@@pulse_unfold]
let client_network_frame_pre
  (frame:tls_client_network_frame)
  (_input:array U8.t)
  (input_len:SZ.t)
  (_out:array U8.t)
  (out_len:SZ.t)
  (input_contents:B.bytes)
  (old_network_out:B.bytes)
  : slprop =
  pts_to
    frame.tls_client_network_app_out
    (Ghost.reveal frame.tls_client_network_old_app_out) **
  pure (
    B.length input_contents == SZ.v input_len /\
    B.length old_network_out == SZ.v out_len /\
    B.length (Ghost.reveal frame.tls_client_network_old_app_out) ==
      SZ.v frame.tls_client_network_app_out_len /\
    L.max_record_fragment_len <=
      SZ.v frame.tls_client_network_app_out_len)

[@@pulse_unfold]
let client_network_frame_post
  (frame:tls_client_network_frame)
  (result:CPI.process_result)
  (input_contents:B.bytes)
  (_input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (consumed:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  : slprop =
  exists* (app_out:B.bytes) (buffer_resp:CT.client_buffer_response).
    pts_to frame.tls_client_network_app_out app_out **
    pure (
      result == CTypes.client_process_result buffer_resp /\
      CT.network_bytes_end_to_end_correct
        st0
        st1
        buffer_resp
        input_contents
        old_network_out
        network_out
        (Ghost.reveal frame.tls_client_network_old_app_out)
        app_out /\
      Seq.equal
        consumed
        (CT.network_consumed_prefix input_contents buffer_resp.CT.consumed_len) /\
      wire_outputs ==
        client_response_wire_outputs buffer_resp.CT.response network_out /\
      local_outputs ==
        client_response_local_outputs buffer_resp.CT.response app_out)

[@@pulse_unfold]
let client_local_frame_pre
  (ev:CTypes.client_local_event)
  (frame:tls_client_local_frame)
  (st0:CS.connection_state)
  (_out:array U8.t)
  (out_len:SZ.t)
  (old_network_out:B.bytes)
  : slprop =
  let api = CTypes.client_local_event_api ev in
  pts_to frame.tls_client_local_payload api.CTypes.client_local_payload **
  pts_to
    frame.tls_client_local_app_out
    (Ghost.reveal frame.tls_client_local_old_app_out) **
  pure (
    B.length api.CTypes.client_local_payload ==
      SZ.v frame.tls_client_local_payload_len /\
    B.length old_network_out == SZ.v out_len /\
    B.length (Ghost.reveal frame.tls_client_local_old_app_out) ==
      SZ.v frame.tls_client_local_app_out_len /\
    CT.local_input_wf
      st0
      api.CTypes.client_local_kind
      api.CTypes.client_local_payload)

let client_local_frame_post
  (ev:CTypes.client_local_event)
  (frame:tls_client_local_frame)
  (result:CPI.process_result)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  : slprop =
  let api = CTypes.client_local_event_api ev in
  exists* (app_out:B.bytes).
    pts_to frame.tls_client_local_payload api.CTypes.client_local_payload **
    pts_to frame.tls_client_local_app_out app_out **
    pure (
      B.length app_out == SZ.v frame.tls_client_local_app_out_len)

let client_state_ahead
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : prop =
  CPI.state_ahead (client_system initial) st0 st1

let client_invariant_pure
  (initial:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  : prop =
  CT.client_end_to_end_invariant st /\
  st.CS.cs_model.CS.model_config == initial.CS.cs_model.CS.model_config /\
  Seq.equal received st.CS.cs_wire_log.CL.raw_received /\
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent

let client_network_frame_post_fact
  (frame:tls_client_network_frame)
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
  (buffer_resp:CT.client_buffer_response)
  : prop =
  result == CTypes.client_process_result buffer_resp /\
  CT.network_bytes_end_to_end_correct
    st0
    st1
    buffer_resp
    input_contents
    old_network_out
    network_out
    (Ghost.reveal frame.tls_client_network_old_app_out)
    app_out /\
  Seq.equal
    consumed
    (CT.network_consumed_prefix input_contents buffer_resp.CT.consumed_len) /\
  wire_outputs ==
    client_response_wire_outputs buffer_resp.CT.response network_out /\
  local_outputs ==
    client_response_local_outputs buffer_resp.CT.response app_out

let client_network_common_witness
  (initial:CS.connection_state)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (frame:tls_client_network_frame)
  (st1:CS.connection_state)
  (app_out:B.bytes)
  (buffer_resp:CT.client_buffer_response)
  (consumed:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  : prop =
  let result = CTypes.client_process_result buffer_resp in
  let received1 = st1.CS.cs_wire_log.CL.raw_received in
  let sent1 = st1.CS.cs_wire_log.CL.raw_sent in
  client_invariant_pure initial received1 sent1 st1 /\
  client_network_frame_post_fact
    frame
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
    (client_system initial)
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

// Helper: prove a canonical step exists when the network response is a non-StepOk
// error and the state changed (st1 != st0).  Covers:
//   Case A – DecodeError  → LocalFail (tls_decode_error)
//   Case B1 – legal_received_tls_response → WireEvent
//   Case B2 – unexpected_message_response → LocalFail (tls_unexpected_message_error)
let lemma_client_network_nonstep_canonical_step
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:CT.client_buffer_response)
  (input_contents:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        buffer_resp.CT.response.CT.status <> CT.StepOk /\
        st1 <> st0 /\
        CT.network_bytes_end_to_end_correct
          st0
          st1
          buffer_resp
          input_contents
          old_network_out
          network_out
          old_app_out
          app_out)
      (ensures client_canonical_step_rel st0 st1)
  =
  let resp = buffer_resp.CT.response in
  let consumed_len = buffer_resp.CT.consumed_len in
  let raw_consumed = CT.network_consumed_prefix input_contents consumed_len in
  // Shared helper: prove the LocalFail canonical step for a given error and event.
  let lemma_localfail_step
    (err:T.tls_error)
    (conn_ev:CS.conn_event)
    : Lemma
        (requires
          conn_ev == CS.ConnLocalEvent (CS.LocalFail err) /\
          CT.legal_delta st0 st1 conn_ev B.empty B.empty)
        (ensures client_canonical_step_rel st0 st1)
    =
    CW.lemma_wire_outputs_of_empty ();
    Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format []) B.empty;
    let api : CTypes.client_api_event = {
      CTypes.client_local_kind = CT.LocalFail;
      CTypes.client_local_payload = B.empty;
    } in
    assert (client_api_event_matches st0 api conn_ev);
    assert (client_wire_outputs_match B.empty []);
    assert (client_local_outputs_match conn_ev []);
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format [];
      CS.delta_raw_received = B.empty;
    } st1);
    assert (exists conn_ev' raw_sent raw_received.
      client_api_event_matches st0 api conn_ev' /\
      client_wire_outputs_match raw_sent [] /\
      client_local_outputs_match conn_ev' [] /\
      CS.legal_connection_delta st0 {
        CS.delta_event = conn_ev';
        CS.delta_raw_sent = raw_sent;
        CS.delta_raw_received = raw_received;
      } st1);
    assert (client_step st0 (SM.LocalEvent (CTypes.ClientAPI api)) st1 (CPI.step_output [] []));
    assert (client_canonical_step_rel st0 st1)
  in
  if resp.CT.status = CT.DecodeError then (
    // Case A: DecodeError → LocalFail tls_decode_error
    assert (CT.network_bytes_decode_error_projection
      st0 st1 buffer_resp input_contents network_out app_out);
    assert (CT.decode_error_response st0 st1 resp network_out app_out);
    assert (CT.legal_response_for_event st0 st1 resp
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_decode_error))
      B.empty B.empty network_out app_out);
    assert (CT.legal_delta st0 st1
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_decode_error)) B.empty B.empty);
    lemma_localfail_step
      CT.tls_decode_error
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_decode_error))
  ) else (
    // Case B: non-DecodeError, non-StepOk, st1 != st0
    // Establish raw_record_parse_success raw_consumed.
    // From network_bytes_step_correct: first disjunct requires response_stuttered
    // which requires st1 == st0 – excluded.  In the second disjunct, since
    // resp.status != DecodeError the inner first option is excluded, giving
    // raw_record_parse_success raw_consumed.
    assert (CT.network_bytes_step_correct
      st0 st1 buffer_resp input_contents old_network_out network_out old_app_out app_out);
    assert (~ (CT.response_stuttered
      st0 st1 resp old_network_out network_out old_app_out app_out));
    assert (CT.raw_record_parse_success raw_consumed);
    CT.lemma_raw_record_parse_success_nonempty raw_consumed;
    assert (B.length raw_consumed > 0);
    // Therefore consumed_len != 0sz (network_consumed_prefix returns a slice of
    // length SZ.v consumed_len when that fits within the input).
    assert (SZ.v consumed_len <= B.length input_contents);
    assert (SZ.v consumed_len > 0);
    // From network_bytes_consumed_input_event_projection:
    // consumed_len != 0sz and resp.status != DecodeError eliminate the first two
    // options, leaving: exists msg. received_tls_raw_delta_legal /\ decoded_message_event_projection
    assert (CT.network_bytes_consumed_input_event_projection
      st0 st1 buffer_resp input_contents network_out app_out);
    assert (exists msg.
      CT.received_tls_raw_delta_legal st0 msg raw_consumed /\
      CT.decoded_message_event_projection st0 st1 resp msg raw_consumed network_out app_out);
    let msg =
      FStar.IndefiniteDescription.indefinite_description_ghost
        M.tls_message
        (fun msg ->
          CT.received_tls_raw_delta_legal st0 msg raw_consumed /\
          CT.decoded_message_event_projection st0 st1 resp msg raw_consumed network_out app_out) in
    if CT.legal_received_tls_response st0 st1 resp msg raw_consumed network_out app_out then (
      // Sub-case B1: legal_received_tls_response → WireEvent step
      assert (CT.legal_response_for_event st0 st1 resp
        (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = msg })
        B.empty raw_consumed network_out app_out);
      // Extract outer_ct, outer_fragment for the wire_message construction
      let outer_ct =
        FStar.IndefiniteDescription.indefinite_description_ghost
          T.content_type
          (fun outer_ct -> exists outer_fragment.
            WS.parse_record_wire raw_consumed ==
              Some (outer_ct, outer_fragment, B.length raw_consumed)) in
      let outer_fragment =
        FStar.IndefiniteDescription.indefinite_description_ghost
          M.sealed_record
          (fun outer_fragment ->
            WS.parse_record_wire raw_consumed ==
              Some (outer_ct, outer_fragment, B.length raw_consumed)) in
      let wire : CW.wire_message = {
        CW.wm_raw = raw_consumed;
        CW.wm_content_type = outer_ct;
        CW.wm_fragment = outer_fragment;
        CW.wm_parse_ok = ();
      } in
      // wire_serialize wire = raw_consumed by construction
      assert (CW.wire_serialize wire == raw_consumed);
      // response_network_out resp network_out = B.empty
      // (from legal_response_for_event: Seq.equal raw_sent (response_network_out ...) with raw_sent = B.empty)
      assert (Seq.equal B.empty (CT.response_network_out resp network_out));
      // serialize_all ... [] = B.empty
      CW.lemma_wire_outputs_of_empty ();
      Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format []) B.empty;
      let conn_ev = CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = msg;
      } in
      // local_outputs match
      assert (CT.response_app_out_matches_event resp conn_ev app_out);
      let local_outputs = client_response_local_outputs resp app_out in
      lemma_client_response_local_outputs_match resp conn_ev app_out;
      assert (client_local_outputs_match conn_ev local_outputs);
      // legal_connection_delta
      assert (CT.legal_delta st0 st1 conn_ev B.empty raw_consumed);
      assert (CS.legal_connection_delta st0 {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format [];
        CS.delta_raw_received = CW.wire_serialize wire;
      } st1);
      assert (exists msg'.
        let conn_ev' = CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = msg';
        } in
        CS.legal_connection_delta st0 {
          CS.delta_event = conn_ev';
          CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format [];
          CS.delta_raw_received = CW.wire_serialize wire;
        } st1 /\
        client_local_outputs_match conn_ev' local_outputs);
      assert (client_step st0 (SM.WireEvent wire) st1 (CPI.step_output [] local_outputs));
      assert (client_canonical_step_rel st0 st1)
    ) else (
      // Sub-case B2: unexpected_message_response → LocalFail tls_unexpected_message_error
      assert (CT.unexpected_message_response st0 st1 resp network_out app_out);
      assert (CT.legal_response_for_event st0 st1 resp
        (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error))
        B.empty B.empty network_out app_out);
      assert (CT.legal_delta st0 st1
        (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error)) B.empty B.empty);
      lemma_localfail_step
        CT.tls_unexpected_message_error
        (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error))
    )
  )

let lemma_client_network_common_witness_progress
  (initial:CS.connection_state)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (frame:tls_client_network_frame)
  (st1:CS.connection_state)
  (app_out:B.bytes)
  (buffer_resp:CT.client_buffer_response)
  (consumed:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  : Lemma
      (requires
        client_network_common_witness
          initial
          received0
          sent0
          st0
          input_contents
          input_len
          old_network_out
          network_out
          out_len
          frame
          st1
          app_out
          buffer_resp
          consumed
          wire_outputs
          local_outputs)
      (ensures client_progress_preorder st0 st1)
=
  let result = CTypes.client_process_result buffer_resp in
  if result.CPI.process_status == CPI.StepOk then (
    CPI.lemma_network_process_ok_refines_transition
      (client_system initial)
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
        (client_system initial).WFSM.wfsm_wire_format
        (CPI.input_bytes input_contents input_len)
        msg
        consumed
        residual /\
      SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
      (client_system initial).WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.WireEvent msg)
        st1
        (CPI.step_output wire_outputs local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all (client_system initial).WFSM.wfsm_wire_format wire_outputs) /\
      CPI.output_written network_out result.CPI.process_produced_len produced /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_received (Seq.append received0 consumed) /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced));
    let msg =
      FStar.IndefiniteDescription.indefinite_description_ghost
        CW.wire_message
        (fun msg -> exists residual produced.
          CPI.consumed_by_parse
            (client_system initial).WFSM.wfsm_wire_format
            (CPI.input_bytes input_contents input_len)
            msg
            consumed
            residual /\
          SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
          (client_system initial).WFSM.wfsm_state_machine.SM.sm_step
            st0
            (SM.WireEvent msg)
            st1
            (CPI.step_output wire_outputs local_outputs) /\
          Seq.equal
            produced
            (WF.serialize_all (client_system initial).WFSM.wfsm_wire_format wire_outputs) /\
          CPI.output_written network_out result.CPI.process_produced_len produced /\
          Seq.equal st1.CS.cs_wire_log.CL.raw_received (Seq.append received0 consumed) /\
          Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced)) in
    assert (client_step
      st0
      (SM.WireEvent msg)
      st1
      (CPI.step_output wire_outputs local_outputs));
    assert (client_canonical_step_rel st0 st1);
    RTC.closure_step client_canonical_step_rel st0 st1
  ) else (
    if st1 == st0 then
      assert (client_progress_preorder st0 st1)
    else (
      assert (buffer_resp.CT.response.CT.status <> CT.StepOk);
      lemma_client_network_nonstep_canonical_step
        st0
        st1
        buffer_resp
        input_contents
        old_network_out
        network_out
        (Ghost.reveal frame.tls_client_network_old_app_out)
        app_out;
      RTC.closure_step client_canonical_step_rel st0 st1
    )
  )

let lemma_client_canonical_step_rel_state_ahead
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires client_canonical_step_rel st0 st1)
      (ensures client_state_ahead initial st0 st1)
=
  let ev =
    FStar.IndefiniteDescription.indefinite_description_ghost
      (SM.event CW.wire_message CTypes.client_local_event)
      (fun ev -> exists out. client_step st0 ev st1 out) in
  let out =
    FStar.IndefiniteDescription.indefinite_description_ghost
      (SM.step_output CW.wire_message CTypes.local_output)
      (fun out -> client_step st0 ev st1 out) in
  let tr = {
    SM.tr_event = ev;
    SM.tr_next_state = st1;
    SM.tr_output = out;
  } in
  assert (SM.trace_reaches
    (client_system initial).WFSM.wfsm_state_machine
    st0
    [tr]
    st1);
  assert (exists trace.
    SM.trace_reaches
      (client_system initial).WFSM.wfsm_state_machine
      st0
      trace
      st1)

let lemma_client_progress_state_ahead
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires client_progress_preorder st0 st1)
      (ensures client_state_ahead initial st0 st1)
=
  RTC.induct
    client_canonical_step_rel
    (fun x y -> client_state_ahead initial x y)
    (fun x ->
      SM.lemma_state_evolves_refl
        (client_system initial).WFSM.wfsm_state_machine
        x)
    (fun x y ->
      lemma_client_canonical_step_rel_state_ahead initial x y)
    (fun x y z ->
      SM.lemma_state_evolves_trans
        (client_system initial).WFSM.wfsm_state_machine
        x
        y
        z)
    st0
    st1
    ()

let client_invariant
  (cc:canonical_client)
  (received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  : slprop =
  C.connection_exactly cc.canonical_client_state st **
  MR.pts_to cc.canonical_client_progress #1.0R st **
  pure (client_invariant_pure
    (Ghost.reveal cc.canonical_client_initial)
    received
    sent
    st)

[@@pulse_unfold]
let client_snapshot
  (cc:canonical_client)
  (_received:B.bytes)
  (_sent:B.bytes)
  (st:CS.connection_state)
  : slprop =
  MR.snapshot cc.canonical_client_progress st

fn client_invariant_valid
  (cc:canonical_client)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires client_invariant
  cc
  (Ghost.reveal received)
  (Ghost.reveal sent)
  (Ghost.reveal st)
ensures client_invariant
  cc
  (Ghost.reveal received)
  (Ghost.reveal sent)
  (Ghost.reveal st) **
  pure (
    WFSM.valid_byte_trace
      (client_system (Ghost.reveal cc.canonical_client_initial))
      (Ghost.reveal received)
      (Ghost.reveal st)
      (Ghost.reveal sent)
      Seq.empty)
{
  unfold (client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  cc.canonical_client_valid_trace
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st);
  assert (pure (client_invariant_pure
    (Ghost.reveal cc.canonical_client_initial)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)));
  assert (pure (WFSM.valid_byte_trace
    (client_system (Ghost.reveal cc.canonical_client_initial))
    (Ghost.reveal received)
    (Ghost.reveal st)
    (Ghost.reveal sent)
    Seq.empty));
  fold (client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st))
}

fn take_client_snapshot
  (cc:canonical_client)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires client_invariant
  cc
  (Ghost.reveal received)
  (Ghost.reveal sent)
  (Ghost.reveal st)
ensures client_invariant
  cc
  (Ghost.reveal received)
  (Ghost.reveal sent)
  (Ghost.reveal st) **
  client_snapshot
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)
{
  unfold (client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  MR.take_snapshot
    cc.canonical_client_progress
    (Ghost.reveal st);
  fold (client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  fold (client_snapshot
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st))
}

fn recall_client_snapshot
  (cc:canonical_client)
  (snapshot_received:Ghost.erased B.bytes)
  (snapshot_sent:Ghost.erased B.bytes)
  (snapshot_state:Ghost.erased CS.connection_state)
  (current_received:Ghost.erased B.bytes)
  (current_sent:Ghost.erased B.bytes)
  (current_state:Ghost.erased CS.connection_state)
requires client_snapshot
  cc
  (Ghost.reveal snapshot_received)
  (Ghost.reveal snapshot_sent)
  (Ghost.reveal snapshot_state) **
  client_invariant
    cc
    (Ghost.reveal current_received)
    (Ghost.reveal current_sent)
    (Ghost.reveal current_state)
ensures client_snapshot
  cc
  (Ghost.reveal snapshot_received)
  (Ghost.reveal snapshot_sent)
  (Ghost.reveal snapshot_state) **
  client_invariant
    cc
    (Ghost.reveal current_received)
    (Ghost.reveal current_sent)
    (Ghost.reveal current_state) **
  pure (
    CPI.state_ahead
      (client_system (Ghost.reveal cc.canonical_client_initial))
      (Ghost.reveal snapshot_state)
      (Ghost.reveal current_state))
{
  unfold (client_snapshot
    cc
    (Ghost.reveal snapshot_received)
    (Ghost.reveal snapshot_sent)
    (Ghost.reveal snapshot_state));
  unfold (client_invariant
    cc
    (Ghost.reveal current_received)
    (Ghost.reveal current_sent)
    (Ghost.reveal current_state));
  MR.recall_snapshot
    cc.canonical_client_progress;
  lemma_client_progress_state_ahead
    (Ghost.reveal cc.canonical_client_initial)
    (Ghost.reveal snapshot_state)
    (Ghost.reveal current_state);
  assert (pure (CPI.state_ahead
    (client_system (Ghost.reveal cc.canonical_client_initial))
    (Ghost.reveal snapshot_state)
    (Ghost.reveal current_state)));
  fold (client_invariant
    cc
    (Ghost.reveal current_received)
    (Ghost.reveal current_sent)
    (Ghost.reveal current_state));
  fold (client_snapshot
    cc
    (Ghost.reveal snapshot_received)
    (Ghost.reveal snapshot_sent)
    (Ghost.reveal snapshot_state))
}

let client_network_bridge_result
  (initial:CS.connection_state)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (out_len:SZ.t)
  (base:tls_client_network_frame)
  (st1:CS.connection_state)
  (app_out:B.bytes)
  (buffer_resp:CT.client_buffer_response)
  : prop =
  exists consumed wire_outputs local_outputs.
    client_network_common_witness
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

let client_network_bridge_obligation
  (base:tls_client_network_frame)
  : prop =
  forall initial received0 sent0 st0 input_contents input_len old_network_out
         network_out out_len st1 app_out buffer_resp.
    client_invariant_pure initial received0 sent0 st0 /\
    CPI.buffers_wf input_contents input_len old_network_out out_len /\
    B.length network_out == B.length old_network_out /\
    B.length app_out == SZ.v base.tls_client_network_app_out_len /\
    CT.network_bytes_end_to_end_correct
      st0
      st1
      buffer_resp
      input_contents
      old_network_out
      network_out
      (Ghost.reveal base.tls_client_network_old_app_out)
      app_out /\
    (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
      buffer_resp.CT.consumed_len == 0sz)
    ==> client_network_bridge_result
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
type tls_client_network_bridge_frame = {
  tls_client_network_bridge_base: tls_client_network_frame;
  tls_client_network_bridge_proof:
    Ghost.erased
      (client_network_bridge_obligation tls_client_network_bridge_base);
}

let lemma_client_network_bridge_frame_obligation
  (frame:tls_client_network_bridge_frame)
  : Lemma
      (ensures
        client_network_bridge_obligation frame.tls_client_network_bridge_base)
=
  let _ = Ghost.reveal frame.tls_client_network_bridge_proof in
  ()

[@@pulse_unfold]
let client_network_bridge_frame_pre
  (frame:tls_client_network_bridge_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (input_contents:B.bytes)
  (old_network_out:B.bytes)
  : slprop =
  client_network_frame_pre
    frame.tls_client_network_bridge_base
    input
    input_len
    out
    out_len
    input_contents
    old_network_out

let client_network_bridge_frame_post
  (frame:tls_client_network_bridge_frame)
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
    pts_to frame.tls_client_network_bridge_base.tls_client_network_app_out app_out **
    pure (
      B.length app_out ==
        SZ.v frame.tls_client_network_bridge_base.tls_client_network_app_out_len)

[@@pulse_unfold]
let client_process_network_post
  (cc:canonical_client)
  (frame:tls_client_network_bridge_frame)
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
    client_invariant
      cc
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1) **
    client_network_bridge_frame_post
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
        (client_system (Ghost.reveal cc.canonical_client_initial))
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

fn client_process_network
  (cc:canonical_client)
  (frame:tls_client_network_bridge_frame)
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
  client_invariant
    cc
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0) **
  client_network_bridge_frame_pre
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
ensures client_process_network_post
  cc
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
  unfold (client_invariant
    cc
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0));
  unfold (client_network_bridge_frame_pre
    frame
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out));
  unfold (client_network_frame_pre
    frame.tls_client_network_bridge_base
    input
    input_len
    out
    out_len
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out));
  rewrite
    (C.connection_exactly cc.canonical_client_state (Ghost.reveal st0))
    as
    (CR.connection_exactly cc.canonical_client_state (Ghost.reveal st0));
  let buffer_resp =
    C.process_network_bytes
      cc.canonical_client_state
      input
      input_len
      out
      out_len
      frame.tls_client_network_bridge_base.tls_client_network_app_out
      frame.tls_client_network_bridge_base.tls_client_network_app_out_len;
  with st1 network_out_bytes app_out_bytes. _;
  assert (pure (client_invariant_pure
    (Ghost.reveal cc.canonical_client_initial)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)));
  assert (pure (B.length network_out_bytes == SZ.v out_len));
  assert (pure (B.length app_out_bytes ==
    SZ.v frame.tls_client_network_bridge_base.tls_client_network_app_out_len));
  assert (pure (CPI.buffers_wf
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    out_len));
  assert (pure (B.length network_out_bytes == B.length (Ghost.reveal old_out)));
  assert (pure (B.length (Ghost.reveal input_contents) == SZ.v input_len));
  assert (pure (CT.network_bytes_end_to_end_correct
    (Ghost.reveal st0)
    st1
    buffer_resp
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out)
    network_out_bytes
    (Ghost.reveal frame.tls_client_network_bridge_base.tls_client_network_old_app_out)
    app_out_bytes));
  assert (pure (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
    buffer_resp.CT.consumed_len == 0sz));
  lemma_client_network_bridge_frame_obligation frame;
  assert (pure (client_network_bridge_obligation
    frame.tls_client_network_bridge_base));
  assert (pure (client_network_bridge_result
    (Ghost.reveal cc.canonical_client_initial)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    network_out_bytes
    out_len
    frame.tls_client_network_bridge_base
    st1
    app_out_bytes
    buffer_resp));
  let consumede : Ghost.erased (consumed:B.bytes{
    exists (wire_outputs:list CW.wire_message).
    exists (local_outputs:list CTypes.local_output).
      client_network_common_witness
        (Ghost.reveal cc.canonical_client_initial)
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)
        (Ghost.reveal input_contents)
        input_len
        (Ghost.reveal old_out)
        network_out_bytes
        out_len
        frame.tls_client_network_bridge_base
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
        client_network_common_witness
          (Ghost.reveal cc.canonical_client_initial)
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0)
          (Ghost.reveal input_contents)
          input_len
          (Ghost.reveal old_out)
          network_out_bytes
          out_len
          frame.tls_client_network_bridge_base
          st1
          app_out_bytes
          buffer_resp
          consumed
          wire_outputs
          local_outputs)));
  assert (pure (exists (wire_outputs:list CW.wire_message).
    exists (local_outputs:list CTypes.local_output).
      client_network_common_witness
        (Ghost.reveal cc.canonical_client_initial)
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)
        (Ghost.reveal input_contents)
        input_len
        (Ghost.reveal old_out)
        network_out_bytes
        out_len
        frame.tls_client_network_bridge_base
        st1
        app_out_bytes
        buffer_resp
        (Ghost.reveal consumede)
        wire_outputs
        local_outputs));
  let wire_outputse : Ghost.erased (wire_outputs:list CW.wire_message{
    exists (local_outputs:list CTypes.local_output).
      client_network_common_witness
        (Ghost.reveal cc.canonical_client_initial)
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0)
        (Ghost.reveal input_contents)
        input_len
        (Ghost.reveal old_out)
        network_out_bytes
        out_len
        frame.tls_client_network_bridge_base
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
        client_network_common_witness
          (Ghost.reveal cc.canonical_client_initial)
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0)
          (Ghost.reveal input_contents)
          input_len
          (Ghost.reveal old_out)
          network_out_bytes
          out_len
          frame.tls_client_network_bridge_base
          st1
          app_out_bytes
          buffer_resp
          (Ghost.reveal consumede)
          wire_outputs
          local_outputs)));
  assert (pure (exists (local_outputs:list CTypes.local_output).
    client_network_common_witness
      (Ghost.reveal cc.canonical_client_initial)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      (Ghost.reveal input_contents)
      input_len
      (Ghost.reveal old_out)
      network_out_bytes
      out_len
      frame.tls_client_network_bridge_base
      st1
      app_out_bytes
      buffer_resp
      (Ghost.reveal consumede)
      (Ghost.reveal wire_outputse)
      local_outputs));
  let local_outputse : Ghost.erased (local_outputs:list CTypes.local_output{
    client_network_common_witness
      (Ghost.reveal cc.canonical_client_initial)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      (Ghost.reveal input_contents)
      input_len
      (Ghost.reveal old_out)
      network_out_bytes
      out_len
      frame.tls_client_network_bridge_base
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
        client_network_common_witness
          (Ghost.reveal cc.canonical_client_initial)
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0)
          (Ghost.reveal input_contents)
          input_len
          (Ghost.reveal old_out)
          network_out_bytes
          out_len
          frame.tls_client_network_bridge_base
          st1
          app_out_bytes
          buffer_resp
          (Ghost.reveal consumede)
          (Ghost.reveal wire_outputse)
          local_outputs));
  assert (pure (client_network_common_witness
    (Ghost.reveal cc.canonical_client_initial)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    network_out_bytes
    out_len
    frame.tls_client_network_bridge_base
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
  assert (pure (client_invariant_pure
    (Ghost.reveal cc.canonical_client_initial)
    (Ghost.reveal received1e)
    (Ghost.reveal sent1e)
    (Ghost.reveal st1e)));
  rewrite (CR.connection_exactly cc.canonical_client_state st1) as
    (C.connection_exactly cc.canonical_client_state st1);
  rewrite (C.connection_exactly cc.canonical_client_state st1) as
    (C.connection_exactly cc.canonical_client_state (Ghost.reveal st1e));
  assert (pure (client_network_frame_post_fact
    frame.tls_client_network_bridge_base
    (CTypes.client_process_result buffer_resp)
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    network_out_bytes
    (Ghost.reveal st0)
    (Ghost.reveal st1e)
    (Ghost.reveal consumede)
    (Ghost.reveal wire_outputse)
    (Ghost.reveal local_outputse)
    app_out_bytes
    buffer_resp));
  assert (pure (
    (CTypes.client_process_result buffer_resp) ==
      CTypes.client_process_result buffer_resp));
  assert (pure (CT.network_bytes_end_to_end_correct
    (Ghost.reveal st0)
    (Ghost.reveal st1e)
    buffer_resp
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out)
    network_out_bytes
    (Ghost.reveal frame.tls_client_network_bridge_base.tls_client_network_old_app_out)
    app_out_bytes));
  assert (pure (Seq.equal
    (Ghost.reveal consumede)
    (CT.network_consumed_prefix
      (Ghost.reveal input_contents)
      buffer_resp.CT.consumed_len)));
  assert (pure ((Ghost.reveal wire_outputse) ==
    client_response_wire_outputs buffer_resp.CT.response network_out_bytes));
  assert (pure ((Ghost.reveal local_outputse) ==
    client_response_local_outputs buffer_resp.CT.response app_out_bytes));
  assert (pure (CPI.network_process_correct
    (client_system (Ghost.reveal cc.canonical_client_initial))
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    network_out_bytes
    out_len
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    (CTypes.client_process_result buffer_resp)
    (Ghost.reveal received1e)
    (Ghost.reveal sent1e)
    (Ghost.reveal st1e)
    (Ghost.reveal consumede)
    (Ghost.reveal wire_outputse)
    (Ghost.reveal local_outputse)));
  lemma_client_network_common_witness_progress
    (Ghost.reveal cc.canonical_client_initial)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    network_out_bytes
    out_len
    frame.tls_client_network_bridge_base
    (Ghost.reveal st1e)
    app_out_bytes
    buffer_resp
    (Ghost.reveal consumede)
    (Ghost.reveal wire_outputse)
    (Ghost.reveal local_outputse);
  MR.update cc.canonical_client_progress (Ghost.reveal st1e);
  with app_out_bytes.
  fold (client_network_bridge_frame_post
    frame
    (CTypes.client_process_result buffer_resp)
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    network_out_bytes
    (Ghost.reveal st0)
    (Ghost.reveal st1e)
    (Ghost.reveal consumede)
    (Ghost.reveal wire_outputse)
    (Ghost.reveal local_outputse));
  fold (client_invariant
    cc
    (Ghost.reveal received1e)
    (Ghost.reveal sent1e)
    (Ghost.reveal st1e));
  assert (pure (CPI.network_process_correct
    (client_system (Ghost.reveal cc.canonical_client_initial))
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    network_out_bytes
    out_len
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    (CTypes.client_process_result buffer_resp)
    (Ghost.reveal received1e)
    (Ghost.reveal sent1e)
    (Ghost.reveal st1e)
    (Ghost.reveal consumede)
    (Ghost.reveal wire_outputse)
    (Ghost.reveal local_outputse)));
  with received1e sent1e st1e network_out_bytes consumede wire_outputse local_outputse.
  fold (client_process_network_post
    cc
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
    (CTypes.client_process_result buffer_resp));
  CTypes.client_process_result buffer_resp
}

fn client_process_local
  (cc:canonical_client)
  (ev:CTypes.client_local_event)
  (frame:tls_client_local_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased B.bytes)
  (sent0:erased B.bytes)
  (st0:erased CS.connection_state)
  (old_out:erased B.bytes)
requires
  client_invariant
    cc
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0) **
  client_local_frame_pre
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
  client_invariant
    cc
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1) **
  client_local_frame_post
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
      (client_system (Ghost.reveal cc.canonical_client_initial))
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
  unfold (client_invariant
    cc
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0));
  unfold (client_local_frame_pre
    ev
    frame
    (Ghost.reveal st0)
    out
    out_len
    (Ghost.reveal old_out));
  let kind = CTypes.client_local_event_kind ev;
  let api:Ghost.erased CTypes.client_api_event =
    Ghost.hide (CTypes.client_local_event_api ev);
  assert (pure ((Ghost.reveal api) == CTypes.client_local_event_api ev));
  assert (pure (kind == (Ghost.reveal api).CTypes.client_local_kind));
    rewrite
      (C.connection_exactly cc.canonical_client_state (Ghost.reveal st0))
      as
      (CR.connection_exactly cc.canonical_client_state (Ghost.reveal st0));
    let resp =
      C.process_local_event
        cc.canonical_client_state
        kind
        frame.tls_client_local_payload
        frame.tls_client_local_payload_len
        out
        out_len
        frame.tls_client_local_app_out
        frame.tls_client_local_app_out_len;
    with st1 network_out_bytes app_out_bytes. _;
    assert (pure (client_invariant_pure
      (Ghost.reveal cc.canonical_client_initial)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)));
    assert (pure (B.length network_out_bytes == SZ.v out_len));
    assert (pure (B.length app_out_bytes == SZ.v frame.tls_client_local_app_out_len));
    assert (pure (B.length network_out_bytes == B.length (Ghost.reveal old_out)));
    assert (pure (CT.local_event_end_to_end_correct
      (Ghost.reveal st0)
      st1
      resp
      (Ghost.reveal api).CTypes.client_local_kind
      (Ghost.reveal api).CTypes.client_local_payload
      network_out_bytes
      app_out_bytes));
    CT.lemma_local_event_end_to_end_correct_preserves_config
      (Ghost.reveal st0)
      st1
      resp
      (Ghost.reveal api).CTypes.client_local_kind
      (Ghost.reveal api).CTypes.client_local_payload
      network_out_bytes
      app_out_bytes;
    CT.lemma_local_event_end_to_end_correct_client_end_to_end_invariant
      (Ghost.reveal st0)
      st1
      resp
      (Ghost.reveal api).CTypes.client_local_kind
      (Ghost.reveal api).CTypes.client_local_payload
      network_out_bytes
      app_out_bytes;
    let wire_outputse : Ghost.erased (wire_outputs:list CW.wire_message{
      wire_outputs == client_response_wire_outputs resp network_out_bytes
    }) = Ghost.hide (client_response_wire_outputs resp network_out_bytes);
    let local_outputse : Ghost.erased (local_outputs:list CTypes.local_output{
      local_outputs == client_response_local_outputs resp app_out_bytes
    }) = Ghost.hide (client_response_local_outputs resp app_out_bytes);
    let ok = resp.CT.status = CT.StepOk;
    if ok {
      assert (pure (resp.CT.status == CT.StepOk));
      lemma_client_local_step_ok_process_correct
        (Ghost.reveal cc.canonical_client_initial)
        (Ghost.reveal st0)
        st1
        ev
        (Ghost.reveal api)
        resp
        (Ghost.reveal old_out)
        network_out_bytes
        out_len
        app_out_bytes
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
    } else {
      assert (pure (resp.CT.status == CT.IllegalTransition \/
        resp.CT.status == CT.ConnectionFailed));
      lemma_client_local_rejected_process_correct
        (Ghost.reveal cc.canonical_client_initial)
        (Ghost.reveal st0)
        st1
        ev
        (Ghost.reveal api)
        resp
        (Ghost.reveal old_out)
        network_out_bytes
        out_len
        app_out_bytes
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
    };
    assert (pure (CPI.local_process_correct
      (client_system (Ghost.reveal cc.canonical_client_initial))
      ev
      (Ghost.reveal old_out)
      network_out_bytes
      out_len
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      (CTypes.client_local_process_result resp)
      st1.CS.cs_wire_log.CL.raw_received
      st1.CS.cs_wire_log.CL.raw_sent
      st1
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
    assert (pure (client_invariant_pure
      (Ghost.reveal cc.canonical_client_initial)
      (Ghost.reveal received1e)
      (Ghost.reveal sent1e)
      (Ghost.reveal st1e)));
    rewrite (CR.connection_exactly cc.canonical_client_state st1) as
      (C.connection_exactly cc.canonical_client_state st1);
    rewrite (C.connection_exactly cc.canonical_client_state st1) as
      (C.connection_exactly cc.canonical_client_state (Ghost.reveal st1e));
    assert (pure (
      (CTypes.client_local_process_result resp) ==
        CTypes.client_local_process_result resp));
    assert (pure ((Ghost.reveal wire_outputse) ==
      client_response_wire_outputs resp network_out_bytes));
    assert (pure ((Ghost.reveal local_outputse) ==
      client_response_local_outputs resp app_out_bytes));
    // Prove progress and update the monotonic reference before folding the invariant
    lemma_client_local_progress
      (Ghost.reveal st0)
      (Ghost.reveal st1e)
      (Ghost.reveal api)
      resp
      network_out_bytes
      app_out_bytes;
    MR.update cc.canonical_client_progress (Ghost.reveal st1e);
    with app_out_bytes.
    fold (client_local_frame_post
      ev
      frame
      (CTypes.client_local_process_result resp)
      (Ghost.reveal old_out)
      network_out_bytes
      (Ghost.reveal st0)
      (Ghost.reveal st1e)
      (Ghost.reveal wire_outputse)
      (Ghost.reveal local_outputse));
    fold (client_invariant
      cc
      (Ghost.reveal received1e)
      (Ghost.reveal sent1e)
      (Ghost.reveal st1e));
    CTypes.client_local_process_result resp
}

noextract
let client_protocol_implementation
  : CPI.protocol_implementation
    canonical_client
    CS.connection_state
    CW.wire_message
    CTypes.client_local_event
    CTypes.local_output
  =
  {
    CPI.pi_system =
    (fun cc -> client_system (Ghost.reveal cc.canonical_client_initial));
    CPI.pi_invariant = client_invariant;
    CPI.pi_snapshot = client_snapshot;
    CPI.pi_network_frame = tls_client_network_bridge_frame;
    CPI.pi_network_frame_pre = client_network_bridge_frame_pre;
    CPI.pi_network_frame_post = client_network_bridge_frame_post;
    CPI.pi_local_frame = tls_client_local_frame;
    CPI.pi_local_frame_pre = client_local_frame_pre;
    CPI.pi_local_frame_post = client_local_frame_post;
    CPI.pi_invariant_valid = client_invariant_valid;
    CPI.pi_take_snapshot = take_client_snapshot;
    CPI.pi_recall_snapshot = recall_client_snapshot;
    CPI.pi_process_network = client_process_network;
    CPI.pi_process_local = client_process_local;
  }
