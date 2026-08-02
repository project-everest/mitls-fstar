module TLS13.Impl.Client.CanonicalProtocol

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Impl.Client
module CL = TLS13.ConnectionLog
module CPI = Common.ProtocolImplementation
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module SMRep = TLS13.Spec.StateMachine.Replay
module SMLog = TLS13.Spec.StateMachine.Log
module SMCan = TLS13.Spec.StateMachine.Canonical
module CT = TLS13.Impl.Client.Types
module TChannel = TLS13.Impl.Channel
module CW = TLS13.Spec.Endpoint.Wire
module CTypes = TLS13.Impl.CanonicalTypes
module EC = TLS13.Spec.Endpoint.Client
module EAPI = TLS13.Spec.Endpoint.API
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Pre = FStar.Preorder
module RVD = TLS13.Wire.Spec.RevealDecode
module RTC = FStar.ReflexiveTransitiveClosure
module Seq = FStar.Seq
module SM = Common.StateMachine
module SZ = FStar.SizeT
module Tac = FStar.Tactics
module TCP = Common.TCP
module T = TLS13.Types
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module WS = TLS13.Wire.Spec

open TLS13.Spec.Endpoint.Client

(**
  Canonical Common.ProtocolImplementation boundary for the low-level client.

  This file contains the auditable state-machine/invariant/snapshot boundary
  and the low-level Pulse operations packaged as a [CPI.protocol_implementation].
  The remaining endpoint-spec-to-common network proof is carried explicitly by
  [tls_client_network_bridge_frame], keeping the proof obligation local to each
  operation frame instead of weakening the common class.
 **)

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

let lemma_client_network_input_projection_refines_core
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (wire:CW.wire_message)
  : Lemma
      (requires
        CT.network_input_message_projection
          st0
          content_type
          fragment
          msg
          (CW.wire_serialize wire))
      (ensures EC.network_input_message_projection st0 wire msg)
=
  assert (CT.network_input_decoder_payload_projection
    st0 content_type fragment msg (CW.wire_serialize wire));
  if CS.network_message_is_cleartext CL.Received msg
  then
    assert (CS.received_cleartext_tls_message_raw
      msg
      (CW.wire_serialize wire))
  else (
    assert (CT.protected_record_decodes_to_message
      st0
      (CW.wire_serialize wire)
      msg);
    CT.lemma_protected_record_decodes_to_received_single_decode
      st0
      (CW.wire_serialize wire)
      msg
  )

let lemma_received_event_nonempty_decode_projection_intro
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (raw_received:B.bytes)
  : Lemma
      (requires
        B.length raw_received == 0 \/
        SMRep.received_event_decode_projection model ev raw_received)
      (ensures
        SMRep.received_event_nonempty_decode_projection model ev raw_received)
=
  assert (SMRep.received_event_nonempty_decode_projection model ev raw_received)
  by (
    FStar.Tactics.norm
      [delta_only [`%SMRep.received_event_nonempty_decode_projection];
       iota; zeta; primops];
    FStar.Tactics.smt ())

let lemma_client_received_network_event_nonempty_decode_projection
  (st0:CS.connection_state)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  : Lemma
      (requires
        (if CS.network_message_is_cleartext CL.Received msg
         then True
         else CT.protected_record_decodes_to_message st0 raw_received msg))
      (ensures
        SMRep.received_event_nonempty_decode_projection
          st0.CS.cs_model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          })
          raw_received)
=
  let ev = CS.ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = msg;
  } in
  if CS.network_message_is_cleartext CL.Received msg
  then (
    assert (SMRep.received_event_decode_projection st0.CS.cs_model ev raw_received)
  )
  else (
    assert (CT.protected_record_decodes_to_message st0 raw_received msg);
    CT.lemma_protected_record_decodes_to_received_single_decode st0 raw_received msg;
    assert (SMRep.received_single_protected_message_decode
      st0.CS.cs_model
      msg
      raw_received);
    assert (CS.protected_record_count CL.Received msg == 1);
    assert (SMRep.received_event_decode_projection st0.CS.cs_model ev raw_received)
  );
  assert (B.length raw_received == 0 \/
    SMRep.received_event_decode_projection st0.CS.cs_model ev raw_received);
  lemma_received_event_nonempty_decode_projection_intro
    st0.CS.cs_model
    ev
    raw_received

noeq
type canonical_client = {
  canonical_client_state: C.client;
  canonical_client_progress:
    MR.mref (client_progress_preorder #CTypes.client_local_event);
  canonical_client_initial: Ghost.erased client_initial_state;
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
  : GTot (list EAPI.local_output) =
  EAPI.local_outputs_of_app_bytes (CT.response_app_out resp app_out)

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
            residual /\
          Seq.equal
            (CW.wire_serialize msg)
            (CT.network_consumed_prefix input consumed_len))
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
    assert (Seq.equal (CW.wire_serialize msg) consumed);
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
        residual' /\
      Seq.equal (CW.wire_serialize msg') consumed)
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
  EAPI.lemma_local_outputs_of_app_bytes_exact app_bytes;
  Seq.lemma_eq_elim
    app_bytes
    (CT.event_api_app_out ev)

// Isolated helper: derive [network_out_len == 0sz] from a known empty
// network-output projection.  Factored into its own lemma (rather than
// inlined at call sites) so that this small arithmetic/slice fact gets its
// own focused VC, independent of whatever large ambient context a caller
// happens to have accumulated.
let lemma_client_response_network_out_len_zero
  (resp:CT.client_response)
  (network_out:B.bytes)
  : Lemma
      (requires
        SZ.v resp.CT.network_out_len <= B.length network_out /\
        Seq.equal B.empty (CT.response_network_out resp network_out))
      (ensures resp.CT.network_out_len == 0sz)
=
  if resp.CT.network_out_len = 0sz then ()
  else (
    Seq.lemma_len_slice network_out 0 (SZ.v resp.CT.network_out_len);
    assert (B.length (CT.response_network_out resp network_out) == SZ.v resp.CT.network_out_len);
    assert False
  )

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
  | CS.ConnProtectedHandshake step ->
    (* Internal event: the matcher pins the step to a tail step, which
       [event_raw_delta_legal] requires to consume no raw input. *)
    CT.lemma_local_event_kind_matches_protected_is_tail
      st0 api.CTypes.client_local_kind api.CTypes.client_local_payload step
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
      (ensures
        client_canonical_step_rel #CTypes.client_local_event st0 st1)
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
        (ensures
          client_canonical_step_rel #CTypes.client_local_event st0 st1)
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
      (ensures
        client_progress_preorder #CTypes.client_local_event st0 st1)
  =
  if st0 = st1 then
    assert (client_progress_preorder #CTypes.client_local_event st0 st1)
  else (
    lemma_client_local_canonical_step st0 st1 api resp network_out app_out;
    RTC.closure_step
      (client_canonical_step_rel #CTypes.client_local_event)
      st0
      st1
  )

let lemma_client_step_from_local_witness
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (local_ev:CTypes.client_local_event)
  (conn_ev:CS.conn_event)
  (raw_sent:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list EAPI.local_output)
  : Lemma
      (requires
        client_api_event_matches
          st0
          (CTypes.client_local_event_api local_ev)
          conn_ev /\
        client_wire_outputs_match raw_sent wire_outputs /\
        client_local_outputs_match conn_ev local_outputs /\
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
        client_step
          st0
          (SM.LocalEvent local_ev)
          st1
          (CPI.step_output wire_outputs local_outputs))
=
  assert ((CPI.step_output wire_outputs local_outputs).SM.so_wire_outputs ==
    wire_outputs);
  assert ((CPI.step_output wire_outputs local_outputs).SM.so_local_outputs ==
    local_outputs);
  assert (client_api_event_matches
    st0
    (CTypes.client_local_event_api local_ev)
    conn_ev);
  assert (SMRep.sent_event_nonempty_seal_projection
    st0.CS.cs_model
    conn_ev
    raw_sent);
  assert (B.length B.empty == 0);
  assert (SMRep.received_event_nonempty_decode_projection
    st0.CS.cs_model
    conn_ev
    B.empty);
  assert (exists conn_ev' raw_sent'.
    client_api_event_matches
      st0
      (CTypes.client_local_event_api local_ev)
      conn_ev' /\
    client_wire_outputs_match
      raw_sent'
      (CPI.step_output wire_outputs local_outputs).SM.so_wire_outputs /\
    client_local_outputs_match
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
  assert (client_step #CTypes.client_local_event
    st0
    (SM.LocalEvent local_ev)
    st1
    (CPI.step_output wire_outputs local_outputs))

let lemma_client_local_step_ok_process_correct
  (initial:client_initial_state)
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
          (client_system #CTypes.client_local_event initial)
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
    Seq.lemma_eq_elim raw_received B.empty;
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
    assert (client_api_event_matches
      st0
      (CTypes.client_local_event_api local_ev)
      ev);
    assert (CS.legal_connection_delta
      st0
      {
        CS.delta_event = ev;
        CS.delta_raw_sent = raw_sent;
        CS.delta_raw_received = B.empty;
      }
      st1);
    assert (SMRep.sent_event_nonempty_seal_projection
      st0.CS.cs_model
      ev
      raw_sent);
    lemma_client_step_from_local_witness
      st0
      st1
      local_ev
      ev
      raw_sent
      wire_outputs
      local_outputs;
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
      (client_system #CTypes.client_local_event initial)
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
  (initial:client_initial_state)
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
          (client_system #CTypes.client_local_event initial)
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
  assert ((CTypes.client_local_process_result resp).CPI.process_produced_len ==
    resp.CT.network_out_len);
  assert (
    (resp.CT.status == CT.IllegalTransition /\
     (CTypes.client_local_process_result resp).CPI.process_status == CPI.IllegalTransition) \/
    (resp.CT.status == CT.ConnectionFailed /\
     (CTypes.client_local_process_result resp).CPI.process_status == CPI.ConnectionFailed));
  assert (
    (CTypes.client_local_process_result resp).CPI.process_status == CPI.IllegalTransition \/
    (CTypes.client_local_process_result resp).CPI.process_status == CPI.ConnectionFailed);
  assert (
    (CTypes.client_local_process_result resp).CPI.process_status == CPI.DecodeError \/
    (CTypes.client_local_process_result resp).CPI.process_status == CPI.IllegalTransition \/
    (CTypes.client_local_process_result resp).CPI.process_status == CPI.ConnectionFailed);
  assert (CPI.output_written
    network_out
    (CTypes.client_local_process_result resp).CPI.process_produced_len
    produced);
  if (exists ev' raw_sent' raw_received'.
      CT.legal_local_response
        st0
        st1
        resp
        api.CTypes.client_local_kind
        api.CTypes.client_local_payload
        ev'
        raw_sent'
        raw_received'
        network_out
        app_out)
  then (
    let ev' =
      FStar.IndefiniteDescription.indefinite_description_ghost
        CS.conn_event
        (fun ev' -> exists raw_sent' raw_received'.
          CT.legal_local_response
            st0
            st1
            resp
            api.CTypes.client_local_kind
            api.CTypes.client_local_payload
            ev'
            raw_sent'
            raw_received'
            network_out
            app_out) in
    let raw_sent' =
      FStar.IndefiniteDescription.indefinite_description_ghost
        B.bytes
        (fun raw_sent' -> exists raw_received'.
          CT.legal_local_response
            st0
            st1
            resp
            api.CTypes.client_local_kind
            api.CTypes.client_local_payload
            ev'
            raw_sent'
            raw_received'
            network_out
            app_out) in
    let raw_received' =
      FStar.IndefiniteDescription.indefinite_description_ghost
        B.bytes
        (fun raw_received' ->
          CT.legal_local_response
            st0
            st1
            resp
            api.CTypes.client_local_kind
            api.CTypes.client_local_payload
            ev'
            raw_sent'
            raw_received'
            network_out
            app_out) in
    assert (CT.legal_local_response
      st0
      st1
      resp
      api.CTypes.client_local_kind
      api.CTypes.client_local_payload
      ev'
      raw_sent'
      raw_received'
      network_out
      app_out);
    assert (CT.local_event_kind_matches
      st0
      api.CTypes.client_local_kind
      api.CTypes.client_local_payload
      ev');
    assert (client_api_event_matches st0 api ev');
    assert (CT.legal_response_for_event st0 st1 resp ev' raw_sent' raw_received' network_out app_out);
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = ev';
      CS.delta_raw_sent = raw_sent';
      CS.delta_raw_received = raw_received';
    } st1);
    lemma_client_api_event_raw_received_empty st0 st1 api resp ev' raw_sent' raw_received' network_out app_out;
    Seq.lemma_eq_elim raw_received' B.empty;
    assert (Seq.equal raw_sent' (CT.response_network_out resp network_out));
    Seq.lemma_eq_elim raw_sent' (CT.response_network_out resp network_out);
    Seq.lemma_eq_elim produced raw_sent';
    assert (client_wire_outputs_match raw_sent' wire_outputs);
    assert (CT.response_app_out_matches_event resp ev' app_out);
    lemma_client_response_local_outputs_match resp ev' app_out;
    assert (client_local_outputs_match ev' local_outputs);
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = ev';
      CS.delta_raw_sent = raw_sent';
      CS.delta_raw_received = B.empty;
    } st1);
    assert ((CPI.step_output wire_outputs local_outputs).SM.so_wire_outputs ==
      wire_outputs);
    assert ((CPI.step_output wire_outputs local_outputs).SM.so_local_outputs ==
      local_outputs);
    assert (
      client_api_event_matches st0 api ev' /\
      client_wire_outputs_match raw_sent' wire_outputs /\
      client_local_outputs_match ev' local_outputs /\
      CS.legal_connection_delta
        st0
        {
          CS.delta_event = ev';
          CS.delta_raw_sent = raw_sent';
          CS.delta_raw_received = B.empty;
        }
        st1);
    assert (exists conn_ev raw_sent.
      client_api_event_matches st0 api conn_ev /\
      client_wire_outputs_match raw_sent wire_outputs /\
      client_local_outputs_match conn_ev local_outputs /\
      CS.legal_connection_delta st0 {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent = raw_sent;
        CS.delta_raw_received = B.empty;
      } st1);
    assert (CTypes.client_local_event_api local_ev == api);
    assert (exists conn_ev raw_sent.
      client_api_event_matches st0 (CTypes.client_local_event_api local_ev) conn_ev /\
      client_wire_outputs_match raw_sent wire_outputs /\
      client_local_outputs_match conn_ev local_outputs /\
      CS.legal_connection_delta st0 {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent = raw_sent;
        CS.delta_raw_received = B.empty;
      } st1);
    assert (api == CTypes.client_local_event_api local_ev);
    assert (client_api_event_matches
      st0
      (CTypes.client_local_event_api local_ev)
      ev');
    assert (
      api == CTypes.client_local_event_api local_ev /\
      client_api_event_matches st0 api ev' /\
      client_wire_outputs_match raw_sent' wire_outputs /\
      client_local_outputs_match ev' local_outputs /\
      CS.legal_connection_delta st0 {
        CS.delta_event = ev';
        CS.delta_raw_sent = raw_sent';
        CS.delta_raw_received = raw_received';
      }       st1);
    assert (
      client_api_event_matches
        st0
        (CTypes.client_local_event_api local_ev)
        ev' /\
      client_wire_outputs_match raw_sent' wire_outputs /\
      client_local_outputs_match ev' local_outputs /\
      CS.legal_connection_delta st0 {
        CS.delta_event = ev';
        CS.delta_raw_sent = raw_sent';
        CS.delta_raw_received = raw_received';
      } st1);
    lemma_client_step_from_local_witness
      st0
      st1
      local_ev
      ev'
      raw_sent'
      wire_outputs
      local_outputs;
    assert (client_step
      st0
      (SM.LocalEvent local_ev)
      st1
      (CPI.step_output wire_outputs local_outputs));
    assert ((client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
      st0
      (SM.LocalEvent local_ev)
      st1
      (CPI.step_output wire_outputs local_outputs))
    by (
      FStar.Tactics.norm
        [delta_only [`%client_system; `%client_state_machine];
         iota; zeta; primops];
      FStar.Tactics.smt ());
    CPI.lemma_local_process_error_refines_step
      (client_system #CTypes.client_local_event initial)
      local_ev
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
      local_outputs
      produced;
    ()
  ) else if CT.unexpected_message_response st0 st1 resp network_out app_out then (
    let err = CT.tls_unexpected_message_error in
    let conn_ev = CS.ConnLocalEvent (CS.LocalFail err) in
    let api_fail : CTypes.client_api_event = {
      CTypes.client_local_kind = CT.LocalFail;
      CTypes.client_local_payload = B.empty;
    } in
    assert (CT.legal_response_for_event st0 st1 resp conn_ev B.empty B.empty network_out app_out);
    assert (api_fail.CTypes.client_local_kind == CT.LocalFail);
    assert (api_fail.CTypes.client_local_payload == B.empty);
    assert_norm (CT.local_event_kind_matches
      st0
      CT.LocalFail
      B.empty
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error)));
    assert (client_api_event_matches st0 api_fail conn_ev);
    assert (Seq.equal (CT.response_network_out resp network_out) B.empty);
    Seq.lemma_eq_elim produced (CT.response_network_out resp network_out);
    assert (client_wire_outputs_match B.empty wire_outputs);
    assert (CT.response_app_out_matches_event resp conn_ev app_out);
    lemma_client_response_local_outputs_match resp conn_ev app_out;
    assert (client_local_outputs_match conn_ev local_outputs);
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    } st1);
    assert_norm (CTypes.client_local_event_api (CTypes.ClientAPI api_fail) == api_fail);
    assert (client_api_event_matches
      st0
      (CTypes.client_local_event_api (CTypes.ClientAPI api_fail))
      conn_ev);
    assert (
      client_api_event_matches
        st0
        (CTypes.client_local_event_api (CTypes.ClientAPI api_fail))
        conn_ev /\
      client_wire_outputs_match B.empty wire_outputs /\
      client_local_outputs_match conn_ev local_outputs /\
      CS.legal_connection_delta st0 {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent = B.empty;
        CS.delta_raw_received = B.empty;
      } st1);
    assert (exists conn_ev' raw_sent.
      client_api_event_matches st0 api_fail conn_ev' /\
      client_wire_outputs_match raw_sent wire_outputs /\
      client_local_outputs_match conn_ev' local_outputs /\
      CS.legal_connection_delta st0 {
        CS.delta_event = conn_ev';
        CS.delta_raw_sent = raw_sent;
        CS.delta_raw_received = B.empty;
      } st1);
    lemma_client_step_from_local_witness
      st0
      st1
      (CTypes.ClientAPI api_fail)
      conn_ev
      B.empty
      wire_outputs
      local_outputs;
    assert (client_step
      st0
      (SM.LocalEvent (CTypes.ClientAPI api_fail))
      st1
      (CPI.step_output wire_outputs local_outputs));
    assert ((client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
      st0
      (SM.LocalEvent (CTypes.ClientAPI api_fail))
      st1
      (CPI.step_output wire_outputs local_outputs))
    by (
      FStar.Tactics.norm
        [delta_only [`%client_system; `%client_state_machine];
         iota; zeta; primops];
      FStar.Tactics.smt ());
    CPI.lemma_local_process_error_refines_step
      (client_system #CTypes.client_local_event initial)
      local_ev
      (CTypes.ClientAPI api_fail)
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
      local_outputs
      produced
  ) else (
    assert (CT.bad_finished_response st0 st1 resp network_out app_out);
    let err = CT.tls_bad_finished_error in
    let conn_ev = CS.ConnLocalEvent (CS.LocalFail err) in
    let api_fail : CTypes.client_api_event = {
      CTypes.client_local_kind = CT.LocalFail;
      CTypes.client_local_payload = B.empty;
    } in
    assert (CT.legal_response_for_event st0 st1 resp conn_ev B.empty B.empty network_out app_out);
    assert (api_fail.CTypes.client_local_kind == CT.LocalFail);
    assert (api_fail.CTypes.client_local_payload == B.empty);
    assert_norm (CT.local_event_kind_matches
      st0
      CT.LocalFail
      B.empty
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_bad_finished_error)));
    assert (client_api_event_matches st0 api_fail conn_ev);
    assert (Seq.equal (CT.response_network_out resp network_out) B.empty);
    Seq.lemma_eq_elim produced (CT.response_network_out resp network_out);
    assert (client_wire_outputs_match B.empty wire_outputs);
    assert (CT.response_app_out_matches_event resp conn_ev app_out);
    lemma_client_response_local_outputs_match resp conn_ev app_out;
    assert (client_local_outputs_match conn_ev local_outputs);
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    } st1);
    assert_norm (CTypes.client_local_event_api (CTypes.ClientAPI api_fail) == api_fail);
    assert (client_api_event_matches
      st0
      (CTypes.client_local_event_api (CTypes.ClientAPI api_fail))
      conn_ev);
    assert (
      client_api_event_matches
        st0
        (CTypes.client_local_event_api (CTypes.ClientAPI api_fail))
        conn_ev /\
      client_wire_outputs_match B.empty wire_outputs /\
      client_local_outputs_match conn_ev local_outputs /\
      CS.legal_connection_delta st0 {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent = B.empty;
        CS.delta_raw_received = B.empty;
      } st1);
    assert (exists conn_ev' raw_sent.
      client_api_event_matches st0 api_fail conn_ev' /\
      client_wire_outputs_match raw_sent wire_outputs /\
      client_local_outputs_match conn_ev' local_outputs /\
      CS.legal_connection_delta st0 {
        CS.delta_event = conn_ev';
        CS.delta_raw_sent = raw_sent;
        CS.delta_raw_received = B.empty;
      } st1);
    lemma_client_step_from_local_witness
      st0
      st1
      (CTypes.ClientAPI api_fail)
      conn_ev
      B.empty
      wire_outputs
      local_outputs;
    assert (client_step
      st0
      (SM.LocalEvent (CTypes.ClientAPI api_fail))
      st1
      (CPI.step_output wire_outputs local_outputs));
    assert ((client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
      st0
      (SM.LocalEvent (CTypes.ClientAPI api_fail))
      st1
      (CPI.step_output wire_outputs local_outputs))
    by (
      FStar.Tactics.norm
        [delta_only [`%client_system; `%client_state_machine];
         iota; zeta; primops];
      FStar.Tactics.smt ());
    CPI.lemma_local_process_error_refines_step
      (client_system #CTypes.client_local_event initial)
      local_ev
      (CTypes.ClientAPI api_fail)
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
      local_outputs
      produced
  );
  assert (CPI.local_process_correct
    (client_system #CTypes.client_local_event initial)
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
  (local_outputs:list EAPI.local_output)
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
  (local_outputs:list EAPI.local_output)
  : slprop =
  let api = CTypes.client_local_event_api ev in
  exists* (app_out:B.bytes).
    pts_to frame.tls_client_local_payload api.CTypes.client_local_payload **
    pts_to frame.tls_client_local_app_out app_out **
    pure (
      B.length app_out == SZ.v frame.tls_client_local_app_out_len)

(* Internal processing reuses the local frame.  It takes no event, so the
   payload buffer contents are existentially quantified rather than tied
   to a caller-supplied event's payload. *)
[@@pulse_unfold]
let client_internal_frame_pre
  (frame:tls_client_local_frame)
  (_st0:CS.connection_state)
  (_out:array U8.t)
  (out_len:SZ.t)
  (old_network_out:B.bytes)
  : slprop =
  exists* (payload:B.bytes).
    pts_to frame.tls_client_local_payload payload **
    pts_to
      frame.tls_client_local_app_out
      (Ghost.reveal frame.tls_client_local_old_app_out) **
    pure (
      B.length payload == SZ.v frame.tls_client_local_payload_len /\
      B.length old_network_out == SZ.v out_len /\
      B.length (Ghost.reveal frame.tls_client_local_old_app_out) ==
        SZ.v frame.tls_client_local_app_out_len)

let client_internal_frame_post
  (frame:tls_client_local_frame)
  (_result:CPI.internal_result)
  (_old_network_out:B.bytes)
  (_network_out:B.bytes)
  (_st0:CS.connection_state)
  (_st1:CS.connection_state)
  (_wire_outputs:list CW.wire_message)
  (_local_outputs:list EAPI.local_output)
  : slprop =
  exists* (payload:B.bytes) (app_out:B.bytes).
    pts_to frame.tls_client_local_payload payload **
    pts_to frame.tls_client_local_app_out app_out **
    pure (
      B.length payload == SZ.v frame.tls_client_local_payload_len /\
      B.length app_out == SZ.v frame.tls_client_local_app_out_len)

(* Phase 1: the TLS client has no internal events yet, so internal
   processing is unconditionally quiescent.  Phase 3 replaces the body
   with a real step over the pending record plaintext; this signature and
   its contract do not change. *)
(* ==================================================================== *)
(* Internal events (INTERNAL_EVENT_PLAN.md S3.3/S4).                    *)
(*                                                                      *)
(* An internal step drains one handshake message that is already        *)
(* retained in the pending protected-handshake plaintext.  It is a      *)
(* LOCAL event -- it consumes no wire input -- whose semantic content   *)
(* is a TAIL ConnProtectedHandshake step.                               *)
(* ==================================================================== *)

let client_is_internal (ev:CTypes.client_local_event) : bool =
  match CTypes.client_local_event_kind ev with
  | CT.LocalProcessPendingHandshake -> true
  | _ -> false

let lemma_client_is_internal_api_kind (ev:CTypes.client_local_event)
  : Lemma
      (requires client_is_internal ev)
      (ensures
        (CTypes.client_local_event_api ev).CTypes.client_local_kind ==
          CT.LocalProcessPendingHandshake)
=
  match ev with
  | CTypes.ClientAPI _ -> ()
  | CTypes.ClientValidateCertificate _ -> ()

let client_internal_event : CTypes.client_local_event =
  CTypes.ClientAPI {
    CTypes.client_local_kind = CT.LocalProcessPendingHandshake;
    CTypes.client_local_payload = B.empty;
  }

let lemma_client_internal_event_is_internal ()
  : Lemma (client_is_internal client_internal_event)
= ()

(** Unprocessed plaintext remains in the pending protected-handshake buffer. *)
let client_internal_pending (st:CS.connection_state) : prop =
  st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed <
  B.length
    st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes

let client_state_ahead
  (initial:client_initial_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : prop =
  CPI.state_ahead
    (client_system #CTypes.client_local_event initial)
    st0
    st1

let client_initial_wire_logs_empty
  (initial:client_initial_state)
  : prop =
  Seq.equal initial.CS.cs_wire_log.CL.raw_received B.empty /\
  Seq.equal initial.CS.cs_wire_log.CL.raw_sent B.empty

let client_invariant_pure
  (initial:client_initial_state)
  (received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  : prop =
  CT.client_end_to_end_invariant st /\
  st.CS.cs_model.CS.model_config == initial.CS.cs_model.CS.model_config /\
  Seq.equal received st.CS.cs_wire_log.CL.raw_received /\
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent /\
  client_initial_wire_logs_empty initial

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
  (local_outputs:list EAPI.local_output)
  (app_out:B.bytes)
  (buffer_resp:CT.client_buffer_response)
  : prop =
  result == CTypes.client_process_result buffer_resp /\
  CT.coalesced_network_bytes_end_to_end_correct
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
  (initial:client_initial_state)
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
  (local_outputs:list EAPI.local_output)
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
    (client_system #CTypes.client_local_event initial)
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

// Prove a canonical step for every state-changing network response.  Covers:
//   Case A – DecodeError  → LocalFail (tls_decode_error)
//   Case B1 – legal_received_tls_response → WireEvent
//   Case B2 – unexpected_message_response → LocalFail (tls_unexpected_message_error)
let lemma_client_network_changed_canonical_step
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
        st1 <> st0 /\
        CT.client_state_correct st0 /\
        CT.network_bytes_end_to_end_correct
          st0
          st1
          buffer_resp
          input_contents
          old_network_out
          network_out
          old_app_out
          app_out)
      (ensures
        client_canonical_step_rel #CTypes.client_local_event st0 st1)
  =
  let resp = buffer_resp.CT.response in
  let consumed_len = buffer_resp.CT.consumed_len in
  let raw_consumed = CT.network_consumed_prefix input_contents consumed_len in
  // Shared helper: prove the LocalFail canonical step for a given error and event.
  let lemma_localfail_step
    (err:T.tls_error)
    : Lemma
        (requires
          CT.legal_delta
            st0
            st1
            (CS.ConnLocalEvent (CS.LocalFail err))
            B.empty
            B.empty)
        (ensures
          client_canonical_step_rel #CTypes.client_local_event st0 st1)
    =
    CW.lemma_wire_outputs_of_empty ();
    Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format []) B.empty;
    let api : CTypes.client_api_event = {
      CTypes.client_local_kind = CT.LocalFail;
      CTypes.client_local_payload = B.empty;
    } in
    let conn_ev = CS.ConnLocalEvent (CS.LocalFail err) in
    assert (api.CTypes.client_local_kind == CT.LocalFail);
    assert (api.CTypes.client_local_payload == B.empty);
    assert_norm (CT.local_event_kind_matches
      st0
      CT.LocalFail
      B.empty
      (CS.ConnLocalEvent (CS.LocalFail err)));
    assert (client_api_event_matches st0 api conn_ev);
    assert (client_wire_outputs_match B.empty []);
    assert (client_local_outputs_match conn_ev []);
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
    assert (client_api_event_matches st0 api conn_ev /\
      client_wire_outputs_match (WF.serialize_all CW.tls_record_wire_format []) [] /\
      client_local_outputs_match conn_ev [] /\
      CS.legal_connection_delta st0 {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format [];
        CS.delta_raw_received = B.empty;
      } st1 /\
      SMRep.sent_event_nonempty_seal_projection
        st0.CS.cs_model
        conn_ev
        (WF.serialize_all CW.tls_record_wire_format []) /\
      SMRep.received_event_nonempty_decode_projection
        st0.CS.cs_model
        conn_ev
        B.empty);
    assert (exists conn_ev' raw_sent.
      client_api_event_matches st0 api conn_ev' /\
      client_wire_outputs_match raw_sent [] /\
      client_local_outputs_match conn_ev' [] /\
      CS.legal_connection_delta st0 {
        CS.delta_event = conn_ev';
        CS.delta_raw_sent = raw_sent;
        CS.delta_raw_received = B.empty;
      } st1 /\
      SMRep.sent_event_nonempty_seal_projection
        st0.CS.cs_model
        conn_ev'
        raw_sent /\
      SMRep.received_event_nonempty_decode_projection
        st0.CS.cs_model
        conn_ev'
        B.empty);
    assert (client_step st0 (SM.LocalEvent (CTypes.ClientAPI api)) st1 (CPI.step_output [] []))
    by (
      Tac.norm
        [delta_only
          [`%client_step];
         iota; zeta; primops];
      Tac.smt ());
    assert (client_canonical_step_rel #CTypes.client_local_event st0 st1)
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
  ) else (
    // Case B: non-DecodeError, non-StepOk, st1 != st0
    assert (CT.network_bytes_step_correct
      st0 st1 buffer_resp input_contents old_network_out network_out old_app_out app_out);
    assert (~ (CT.response_stuttered
      st0 st1 resp old_network_out network_out old_app_out app_out));
    if resp.CT.status = CT.IllegalTransition && consumed_len = 0sz then (
      // Case C: IllegalTransition with a forced zero-length consumption (the
      // client never reports real record-consumption bytes for a message that
      // was rejected as illegal in the current protocol state) → LocalFail
      // tls_unexpected_message_error, straight from the bypass disjunct of
      // network_bytes_step_correct (no wire parse witness is needed).
      assert (CT.unexpected_message_response st0 st1 resp network_out app_out);
      assert (CT.legal_response_for_event st0 st1 resp
        (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error))
        B.empty B.empty network_out app_out);
      assert (CT.legal_delta st0 st1
        (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error)) B.empty B.empty);
      lemma_localfail_step
        CT.tls_unexpected_message_error
    ) else (
    // Establish raw_record_parse_success raw_consumed.
    // From network_bytes_step_correct: first disjunct requires response_stuttered
    // which requires st1 == st0 – excluded.  In the second disjunct, since
    // resp.status != DecodeError and (resp.status != IllegalTransition \/
    // consumed_len <> 0sz), the first two inner options are excluded, giving
    // raw_record_parse_success raw_consumed.
    assert (CT.raw_record_parse_success raw_consumed);
    CT.lemma_raw_record_parse_success_nonempty raw_consumed;
    assert (B.length raw_consumed > 0);
    // Therefore consumed_len != 0sz (network_consumed_prefix returns a slice of
    // length SZ.v consumed_len when that fits within the input).
    assert (SZ.v consumed_len <= B.length input_contents);
    assert (SZ.v consumed_len > 0);
    // From network_bytes_decoded_message_projection: consumed_len != 0sz and
    // resp.status != DecodeError eliminate the first two options, leaving the
    // parser-backed decoded message witness.
    assert (CT.network_bytes_decoded_message_projection
      st0 st1 buffer_resp input_contents network_out app_out);
    assert (exists content_type fragment msg.
      CT.network_input_message_projection
        st0
        content_type
        fragment
        msg
        raw_consumed /\
      CT.decoded_message_event_projection
        st0
        st1
        resp
        msg
        raw_consumed
        network_out
        app_out);
    let msg =
      FStar.IndefiniteDescription.indefinite_description_ghost
        M.tls_message
        (fun msg -> exists content_type fragment.
          CT.network_input_message_projection
            st0
            content_type
            fragment
            msg
            raw_consumed /\
          CT.decoded_message_event_projection
            st0
            st1
            resp
            msg
            raw_consumed
            network_out
            app_out) in
    let content_type =
      FStar.IndefiniteDescription.indefinite_description_ghost
        U8.t
        (fun content_type -> exists fragment.
          CT.network_input_message_projection
            st0
            content_type
            fragment
            msg
            raw_consumed /\
          CT.decoded_message_event_projection
            st0
            st1
            resp
            msg
            raw_consumed
            network_out
            app_out) in
    let fragment =
      FStar.IndefiniteDescription.indefinite_description_ghost
        B.bytes
        (fun fragment ->
          CT.network_input_message_projection
            st0
            content_type
            fragment
            msg
            raw_consumed /\
          CT.decoded_message_event_projection
            st0
            st1
            resp
            msg
            raw_consumed
            network_out
            app_out) in
    assert (CT.network_input_message_projection
      st0
      content_type
      fragment
      msg
      raw_consumed);
    assert (CT.decoded_message_event_projection
      st0 st1 resp msg raw_consumed network_out app_out);
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
      assert (B.length (WF.serialize_all CW.tls_record_wire_format []) == 0);
      assert (SMRep.sent_event_nonempty_seal_projection
        st0.CS.cs_model
        conn_ev
        (WF.serialize_all CW.tls_record_wire_format []));
      lemma_client_received_network_event_nonempty_decode_projection
        st0
        msg
        raw_consumed;
      assert (SMRep.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev raw_consumed);
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
        SMRep.sent_event_nonempty_seal_projection
          st0.CS.cs_model
          conn_ev'
          (WF.serialize_all CW.tls_record_wire_format []) /\
        SMRep.received_event_nonempty_decode_projection
          st0.CS.cs_model
          conn_ev'
          (CW.wire_serialize wire) /\
        (exists content_type' fragment'.
          CT.network_input_message_projection
            st0
            content_type'
            fragment'
            msg'
            (CW.wire_serialize wire)) /\
        client_local_outputs_match conn_ev' local_outputs);
      let no_wire_outputs : list CW.wire_message = [] in
      assert ((CPI.step_output no_wire_outputs local_outputs).SM.so_wire_outputs == no_wire_outputs);
      assert ((CPI.step_output no_wire_outputs local_outputs).SM.so_local_outputs == local_outputs);
      lemma_client_network_input_projection_refines_core
        st0
        content_type
        fragment
        msg
        wire;
      assert (EC.network_input_message_projection st0 wire msg);
      assert (client_step #CTypes.client_local_event
        st0
        (SM.WireEvent wire)
        st1
        (CPI.step_output no_wire_outputs local_outputs));
      assert (client_canonical_step_rel #CTypes.client_local_event st0 st1)
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
    )
    )
  )

let lemma_client_network_progress
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
        CT.client_end_to_end_invariant st0 /\
        CT.network_bytes_end_to_end_correct
          st0
          st1
          buffer_resp
          input_contents
          old_network_out
          network_out
          old_app_out
          app_out)
      (ensures
        client_progress_preorder #CTypes.client_local_event st0 st1)
=
  if st0 = st1 then
    assert (client_progress_preorder #CTypes.client_local_event st0 st1)
  else (
    lemma_client_network_changed_canonical_step
      st0
      st1
      buffer_resp
      input_contents
      old_network_out
      network_out
      old_app_out
      app_out;
    RTC.closure_step
      (client_canonical_step_rel #CTypes.client_local_event)
      st0
      st1
  )

(**
  The head-protected disjunct of [coalesced_network_bytes_end_to_end_correct]
  forces a StepOk response, so any other status pins the strong predicate.
 **)
let lemma_client_coalesced_not_step_ok_is_strong
  (st0 st1:CS.connection_state)
  (buffer_resp:CT.client_buffer_response)
  (network_input:B.bytes)
  (old_network_out network_out:B.bytes)
  (old_app_out app_out:B.bytes)
  : Lemma
      (requires
        CT.coalesced_network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input
          old_network_out network_out old_app_out app_out /\
        buffer_resp.CT.response.CT.status =!= CT.StepOk)
      (ensures
        CT.network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input
          old_network_out network_out old_app_out app_out)
= ()

let lemma_client_network_common_witness_progress
  (initial:client_initial_state)  (received0:B.bytes)
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
  (local_outputs:list EAPI.local_output)
  : Lemma
      (requires
        client_invariant_pure initial received0 sent0 st0 /\
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
      (ensures
        client_progress_preorder #CTypes.client_local_event st0 st1)
=
  let result = CTypes.client_process_result buffer_resp in
  if result.CPI.process_status == CPI.StepOk then (
    CPI.lemma_network_process_ok_refines_transition
      (client_system #CTypes.client_local_event initial)
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
        (client_system #CTypes.client_local_event initial).WFSM.wfsm_wire_format
        (CPI.input_bytes input_contents input_len)
        msg
        consumed
        residual /\
      SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
      (client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.WireEvent msg)
        st1
        (CPI.step_output wire_outputs local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all
          (client_system #CTypes.client_local_event initial).WFSM.wfsm_wire_format
          wire_outputs) /\
      CPI.output_written network_out result.CPI.process_produced_len produced /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_received (Seq.append received0 consumed) /\
      Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced));
    let msg =
      FStar.IndefiniteDescription.indefinite_description_ghost
        CW.wire_message
        (fun msg -> exists residual produced.
          CPI.consumed_by_parse
            (client_system #CTypes.client_local_event initial).WFSM.wfsm_wire_format
            (CPI.input_bytes input_contents input_len)
            msg
            consumed
            residual /\
          SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
          (client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
            st0
            (SM.WireEvent msg)
            st1
            (CPI.step_output wire_outputs local_outputs) /\
          Seq.equal
            produced
            (WF.serialize_all
              (client_system #CTypes.client_local_event initial).WFSM.wfsm_wire_format
              wire_outputs) /\
          CPI.output_written network_out result.CPI.process_produced_len produced /\
          Seq.equal st1.CS.cs_wire_log.CL.raw_received (Seq.append received0 consumed) /\
          Seq.equal st1.CS.cs_wire_log.CL.raw_sent (Seq.append sent0 produced)) in
    assert (client_step #CTypes.client_local_event
      st0
      (SM.WireEvent msg)
      st1
      (CPI.step_output wire_outputs local_outputs));
    assert (client_canonical_step_rel #CTypes.client_local_event st0 st1);
    RTC.closure_step
      (client_canonical_step_rel #CTypes.client_local_event)
      st0
      st1
  ) else (
    if st1 == st0 then
      assert (client_progress_preorder #CTypes.client_local_event st0 st1)
    else (
      assert (buffer_resp.CT.response.CT.status <> CT.StepOk);
      assert (client_invariant_pure initial received0 sent0 st0);
      assert (CT.client_end_to_end_invariant st0);
      assert (CT.client_state_correct st0);
      // The head-protected disjunct of the coalesced predicate forces StepOk,
      // which is excluded here, so the strong predicate holds.
      lemma_client_coalesced_not_step_ok_is_strong
        st0
        st1
        buffer_resp
        input_contents
        old_network_out
        network_out
        (Ghost.reveal frame.tls_client_network_old_app_out)
        app_out;
      lemma_client_network_changed_canonical_step
        st0
        st1
        buffer_resp
        input_contents
        old_network_out
        network_out
        (Ghost.reveal frame.tls_client_network_old_app_out)
        app_out;
      RTC.closure_step
        (client_canonical_step_rel #CTypes.client_local_event)
        st0
        st1
    )
  )

let lemma_client_canonical_step_rel_state_ahead
  (initial:client_initial_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires
        client_canonical_step_rel #CTypes.client_local_event st0 st1)
      (ensures client_state_ahead initial st0 st1)
=
  let ev =
    FStar.IndefiniteDescription.indefinite_description_ghost
      (SM.event CW.wire_message CTypes.client_local_event)
      (fun ev -> exists out. client_step st0 ev st1 out) in
  let out =
    FStar.IndefiniteDescription.indefinite_description_ghost
      (SM.step_output CW.wire_message EAPI.local_output)
      (fun out -> client_step st0 ev st1 out) in
  let tr = {
    SM.tr_event = ev;
    SM.tr_next_state = st1;
    SM.tr_output = out;
  } in
  assert (SM.trace_reaches
    (client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine
    st0
    [tr]
    st1);
  assert (exists trace.
    SM.trace_reaches
      (client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine
      st0
      trace
      st1)

let lemma_client_progress_state_ahead
  (initial:client_initial_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires
        client_progress_preorder #CTypes.client_local_event st0 st1)
      (ensures client_state_ahead initial st0 st1)
=
  RTC.induct
    (client_canonical_step_rel #CTypes.client_local_event)
    (fun x y -> client_state_ahead initial x y)
    (fun x ->
      SM.lemma_state_evolves_refl
        (client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine
        x)
    (fun x y ->
      lemma_client_canonical_step_rel_state_ahead initial x y)
    (fun x y z ->
      SM.lemma_state_evolves_trans
        (client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine
        x
        y
        z)
    st0
    st1
    ()

let lemma_client_step_wire_log_delta
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires client_step st0 ev st1 out)
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
    eliminate exists (conn_ev:CS.conn_event).
      (client_wire_received_event st0 wire conn_ev /\
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
      client_local_outputs_match conn_ev out.SM.so_local_outputs)
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
    let api = CTypes.client_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      client_api_event_matches st0 api conn_ev /\
      client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      client_local_outputs_match conn_ev out.SM.so_local_outputs /\
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

let rec lemma_client_trace_wire_logs_match
  (initial:client_initial_state)
  (st0:CS.connection_state)
  (trace:list
    (SM.transition
      CS.connection_state
      CW.wire_message
      CTypes.client_local_event
      EAPI.local_output))
  (st1:CS.connection_state)
  : Lemma
      (requires
        SM.trace_reaches
          (client_state_machine initial)
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
    assert (client_step
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output);
    lemma_client_step_wire_log_delta
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output;
    lemma_client_trace_wire_logs_match
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

let lemma_client_state_ahead_valid_byte_trace
  (initial:client_initial_state)
  (received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  : Lemma
      (requires
        client_invariant_pure initial received sent st /\
        client_state_ahead initial initial st)
      (ensures
        WFSM.valid_byte_trace
          (client_system #CTypes.client_local_event initial)
          received
          st
          sent
          Seq.empty)
=
  eliminate exists trace.
    SM.trace_reaches
      (client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine
      initial
      trace
      st
  returns
    WFSM.valid_byte_trace
      (client_system #CTypes.client_local_event initial)
      received
      st
      sent
      Seq.empty
  with _.
  (
    assert ((client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine ==
      client_state_machine initial);
    assert ((client_system #CTypes.client_local_event initial).WFSM.wfsm_wire_format ==
      CW.tls_record_wire_format);
    lemma_client_trace_wire_logs_match
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
        (client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine
        (client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine.SM.sm_initial_state
        trace'
        st /\
      WF.parses_as
        (client_system #CTypes.client_local_event initial).WFSM.wfsm_wire_format
        received
        (WFSM.trace_input_messages trace')
        Seq.empty /\
      Seq.equal
        sent
        (WF.serialize_all
          (client_system #CTypes.client_local_event initial).WFSM.wfsm_wire_format
          (SM.trace_wire_outputs trace')))
  )

let lemma_client_legal_delta_histories_ahead
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

let lemma_client_step_histories_ahead
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires client_step st0 ev st1 out)
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
    let conn_ev =
      FStar.IndefiniteDescription.indefinite_description_ghost
        CS.conn_event
        (fun conn_ev ->
          client_wire_received_event st0 wire conn_ev /\
          CS.legal_connection_delta
            st0
            {
              CS.delta_event = conn_ev;
              CS.delta_raw_sent =
                WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
              CS.delta_raw_received = CW.wire_serialize wire;
            }
            st1 /\
          client_local_outputs_match conn_ev out.SM.so_local_outputs) in
    let delta = {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent =
        WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
      CS.delta_raw_received = CW.wire_serialize wire;
    } in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_client_legal_delta_histories_ahead st0 delta st1
  | SM.LocalEvent local ->
    let api = CTypes.client_local_event_api local in
    let conn_ev =
      FStar.IndefiniteDescription.indefinite_description_ghost
        CS.conn_event
        (fun conn_ev ->
          exists raw_sent raw_received.
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
              st1) in
    let raw_sent =
      FStar.IndefiniteDescription.indefinite_description_ghost
        B.bytes
        (fun raw_sent ->
          exists raw_received.
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
              st1) in
    let raw_received =
      FStar.IndefiniteDescription.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
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
            st1) in
    let delta = {
      CS.delta_event = conn_ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    } in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_client_legal_delta_histories_ahead st0 delta st1

let lemma_client_canonical_step_rel_histories_ahead
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires
        client_canonical_step_rel #CTypes.client_local_event st0 st1)
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
    FStar.IndefiniteDescription.indefinite_description_ghost
      (SM.event CW.wire_message CTypes.client_local_event)
      (fun ev -> exists out. client_step st0 ev st1 out) in
  let out =
    FStar.IndefiniteDescription.indefinite_description_ghost
      (SM.step_output CW.wire_message EAPI.local_output)
      (fun out -> client_step st0 ev st1 out) in
  lemma_client_step_histories_ahead st0 ev st1 out

let lemma_client_progress_histories_ahead
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires
        client_progress_preorder #CTypes.client_local_event st0 st1)
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
    (client_canonical_step_rel #CTypes.client_local_event)
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
      lemma_client_canonical_step_rel_histories_ahead x y)
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

let client_invariant
  (cc:canonical_client)
  (received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  : slprop =
  C.connection_exactly cc.canonical_client_state st **
  MR.pts_to cc.canonical_client_progress #1.0R st **
  MR.snapshot
    cc.canonical_client_progress
    (Ghost.reveal cc.canonical_client_initial) **
  pure (client_invariant_pure
    (Ghost.reveal cc.canonical_client_initial)
    received
    sent
    st)

[@@pulse_unfold]
let client_snapshot
  (cc:canonical_client)
 (received:B.bytes)
 (sent:B.bytes)
  (st:CS.connection_state)
  : slprop =
 MR.snapshot cc.canonical_client_progress st **
 pure (client_invariant_pure
   (Ghost.reveal cc.canonical_client_initial)
   received
   sent
   st)

ghost fn client_invariant_valid
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
      (client_system
        #CTypes.client_local_event
        (Ghost.reveal cc.canonical_client_initial))
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
    MR.recall_snapshot
      cc.canonical_client_progress;
    lemma_client_progress_state_ahead
      (Ghost.reveal cc.canonical_client_initial)
      (Ghost.reveal cc.canonical_client_initial)
      (Ghost.reveal st);
    lemma_client_state_ahead_valid_byte_trace
      (Ghost.reveal cc.canonical_client_initial)
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Ghost.reveal st);
  assert (pure (client_invariant_pure
    (Ghost.reveal cc.canonical_client_initial)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)));
  assert (pure (WFSM.valid_byte_trace
    (client_system
      #CTypes.client_local_event
      (Ghost.reveal cc.canonical_client_initial))
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

fn new_canonical_client
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_hostname_len /\
                 SZ.v trust_anchors_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_trust_anchors_len)
  returns cc:canonical_client
  ensures pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          client_invariant
            cc
            B.empty
            B.empty
            (CR.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds) **
          pure (CT.client_end_to_end_invariant
            (CR.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds))
{
  let c =
    C.new_client
      server_name
      server_name_len
      trust_anchors
      trust_anchors_len
      validation_time_seconds;
  let progress =
    MR.alloc #_ #(client_progress_preorder #CTypes.client_local_event)
    (CR.configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds);
  MR.take_snapshot
    progress
    (CR.configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds);
  let cc = {
    canonical_client_state = c;
    canonical_client_progress = progress;
    canonical_client_initial =
      Ghost.hide
        (CR.configured_initial_state
          (Ghost.reveal 'server_name_bytes)
          (Ghost.reveal 'trust_anchors_bytes)
          validation_time_seconds);
  };
  rewrite
    (CR.connection_exactly
      c
      (CR.configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds))
    as
    (C.connection_exactly
      cc.canonical_client_state
      (CR.configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds));
  rewrite
    (MR.pts_to
      progress
      #1.0R
      (CR.configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds))
    as
    (MR.pts_to
      cc.canonical_client_progress
      #1.0R
      (CR.configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds));
  rewrite
    (MR.snapshot
      progress
      (CR.configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds))
    as
    (MR.snapshot
      cc.canonical_client_progress
      (CR.configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds));
  assert (pure (Ghost.reveal cc.canonical_client_initial ==
    (CR.configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds)));
  rewrite
    (MR.snapshot
      cc.canonical_client_progress
      (CR.configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds))
    as
    (MR.snapshot
      cc.canonical_client_progress
      (Ghost.reveal cc.canonical_client_initial));
  assert (pure (Seq.equal B.empty
    (CR.configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds).CS.cs_wire_log.CL.raw_received));
  assert (pure (Seq.equal B.empty
    (CR.configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds).CS.cs_wire_log.CL.raw_sent));
  assert (pure (client_invariant_pure
    (CR.configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds)
    B.empty
    B.empty
    (CR.configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds)));
  fold
    (client_invariant
      cc
      B.empty
      B.empty
      (CR.configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds));
  cc
}

ghost fn take_client_snapshot
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
  assert (pure (client_invariant_pure
    (Ghost.reveal cc.canonical_client_initial)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)));
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

ghost fn recall_client_snapshot
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
      (client_system
        #CTypes.client_local_event
        (Ghost.reveal cc.canonical_client_initial))
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
    cc.canonical_client_progress
    #1.0R
    #(Ghost.reveal current_state)
    #(Ghost.reveal snapshot_state);
  lemma_client_progress_state_ahead
    (Ghost.reveal cc.canonical_client_initial)
    (Ghost.reveal snapshot_state)
    (Ghost.reveal current_state);
  lemma_client_progress_histories_ahead
    (Ghost.reveal snapshot_state)
    (Ghost.reveal current_state);
  assert (pure (CPI.state_ahead
    (client_system
      #CTypes.client_local_event
      (Ghost.reveal cc.canonical_client_initial))
    (Ghost.reveal snapshot_state)
    (Ghost.reveal current_state)));
  assert (pure (client_invariant_pure
    (Ghost.reveal cc.canonical_client_initial)
    (Ghost.reveal snapshot_received)
    (Ghost.reveal snapshot_sent)
    (Ghost.reveal snapshot_state)));
  assert (pure (client_invariant_pure
    (Ghost.reveal cc.canonical_client_initial)
    (Ghost.reveal current_received)
    (Ghost.reveal current_sent)
    (Ghost.reveal current_state)));
  assert (pure (CPI.histories_ahead
    (Ghost.reveal snapshot_received)
    (Ghost.reveal snapshot_sent)
    (Ghost.reveal current_received)
    (Ghost.reveal current_sent)));
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

ghost fn recall_client_snapshot_for_protocol
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
      (client_system
        #CTypes.client_local_event
        (Ghost.reveal cc.canonical_client_initial))
      (Ghost.reveal snapshot_state)
      (Ghost.reveal current_state) /\
    CPI.histories_ahead
      (Ghost.reveal snapshot_received)
      (Ghost.reveal snapshot_sent)
      (Ghost.reveal current_received)
      (Ghost.reveal current_sent))
{
  recall_client_snapshot
    cc
    snapshot_received
    snapshot_sent
    snapshot_state
    current_received
    current_sent
    current_state
}

let client_network_bridge_result
  (initial:client_initial_state)
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
    B.length input_contents == SZ.v input_len /\
    B.length network_out == B.length old_network_out /\
    B.length app_out == SZ.v base.tls_client_network_app_out_len /\
    CT.coalesced_network_bytes_end_to_end_correct
      st0
      st1
      buffer_resp
      input_contents
      old_network_out
      network_out
      (Ghost.reveal base.tls_client_network_old_app_out)
      app_out /\
    (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
      buffer_resp.CT.consumed_len == 0sz /\
      WS.parse_record_wire input_contents == None) /\
    (buffer_resp.CT.response.CT.status == CT.DecodeError ==>
      buffer_resp.CT.consumed_len == 0sz) /\
    (buffer_resp.CT.response.CT.status == CT.IllegalTransition ==>
      buffer_resp.CT.consumed_len == 0sz) /\
    (buffer_resp.CT.response.CT.status == CT.OutputBufferTooSmall ==> False)
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

let lemma_client_network_common_witness_from_parts
  (initial:client_initial_state)
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
  (consumed:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list EAPI.local_output)
  : Lemma
      (requires
        client_invariant_pure
          initial
          st1.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_sent
          st1 /\
        client_network_frame_post_fact
          base
          (CTypes.client_process_result buffer_resp)
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
          (client_system #CTypes.client_local_event initial)
          input_contents
          input_len
          old_network_out
          network_out
          out_len
          received0
          sent0
          st0
          (CTypes.client_process_result buffer_resp)
          st1.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_sent
          st1
          consumed
          wire_outputs
          local_outputs)
      (ensures
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
          local_outputs)
= ()

let lemma_client_network_bridge_result_from_common_witness
  (initial:client_initial_state)
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
  (consumed:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list EAPI.local_output)
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
          base
          st1
          app_out
          buffer_resp
          consumed
          wire_outputs
          local_outputs)
      (ensures
        client_network_bridge_result
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
      client_network_common_witness
        initial received0 sent0 st0 input_contents input_len
        old_network_out network_out out_len base st1 app_out buffer_resp
        consumed wire_outputs local_outputs')
    local_outputs;
  FStar.Classical.exists_intro
    (fun wire_outputs' -> exists local_outputs'.
      client_network_common_witness
        initial received0 sent0 st0 input_contents input_len
        old_network_out network_out out_len base st1 app_out buffer_resp
        consumed wire_outputs' local_outputs')
    wire_outputs;
  FStar.Classical.exists_intro
    (fun consumed' -> exists wire_outputs' local_outputs'.
      client_network_common_witness
        initial received0 sent0 st0 input_contents input_len
        old_network_out network_out out_len base st1 app_out buffer_resp
        consumed' wire_outputs' local_outputs')
    consumed

// NeedMoreInput: the wire format cannot parse a full record from the
// available bytes, so the response stutters (st1 == st0, nothing consumed,
// nothing produced).  [CW.lemma_wire_parse_none] lifts the record-level parse
// failure to the [CW.tls_record_wire_format] wire-format failure required by
// [CPI.network_process_correct]'s NeedMoreInput branch.
let lemma_client_network_need_more_input_bridge_result
  (initial:client_initial_state)
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
  : Lemma
      (requires
        client_invariant_pure initial received0 sent0 st0 /\
        CPI.buffers_wf input_contents input_len old_network_out out_len /\
        B.length input_contents == SZ.v input_len /\
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
        buffer_resp.CT.response.CT.status == CT.NeedMoreInput /\
        buffer_resp.CT.consumed_len == 0sz /\
        WS.parse_record_wire input_contents == None)
      (ensures
        client_network_bridge_result
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
  let resp = buffer_resp.CT.response in
  let old_app_out = Ghost.reveal base.tls_client_network_old_app_out in
  assert (CT.network_bytes_step_correct
    st0 st1 buffer_resp input_contents old_network_out network_out old_app_out app_out);
  // network_bytes_step_correct's first disjunct is exactly response_stuttered
  // (since consumed_len == 0sz); rule out the second disjunct, which (since
  // resp.status is neither DecodeError nor IllegalTransition) would force
  // raw_record_parse_success of the empty consumed prefix, contradicting
  // lemma_raw_record_parse_success_nonempty.
  if CT.response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out then ()
  else (
    let raw_consumed0 = CT.network_consumed_prefix input_contents 0sz in
    assert (Seq.equal raw_consumed0 B.empty);
    assert (CT.raw_record_parse_success raw_consumed0);
    CT.lemma_raw_record_parse_success_nonempty raw_consumed0;
    assert False
  );
  assert (CT.response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out);
  CW.lemma_wire_parse_none input_contents;
  assert (CW.tls_record_wire_format.WF.wf_parse input_contents == None);
  assert (Seq.equal (CPI.input_bytes input_contents input_len) input_contents);
  let consumed : B.bytes = B.empty in
  let wire_outputs : list CW.wire_message = [] in
  let local_outputs : list EAPI.local_output = [] in
  let result = CTypes.client_process_result buffer_resp in
  assert (result.CPI.process_status == CPI.NeedMoreInput);
  assert (result.CPI.process_consumed_len == 0sz);
  assert (result.CPI.process_produced_len == 0sz);
  assert (Seq.equal st1.CS.cs_wire_log.CL.raw_received st0.CS.cs_wire_log.CL.raw_received);
  assert (Seq.equal st1.CS.cs_wire_log.CL.raw_sent st0.CS.cs_wire_log.CL.raw_sent);
  assert (st1 == st0);
  assert (CPI.same_abstract_state
    received0 sent0
    st1.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_sent
    st0 st1);
  assert (Seq.equal network_out old_network_out);
  assert (CPI.network_process_correct
    (client_system #CTypes.client_local_event initial)
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
  assert (client_network_frame_post_fact
    base result input_contents input_len old_network_out network_out
    st0 st1 consumed wire_outputs local_outputs app_out buffer_resp);
  lemma_client_network_common_witness_from_parts
    initial received0 sent0 st0 input_contents input_len
    old_network_out network_out out_len base st1 app_out buffer_resp
    consumed wire_outputs local_outputs;
  lemma_client_network_bridge_result_from_common_witness
    initial received0 sent0 st0 input_contents input_len
    old_network_out network_out out_len base st1 app_out buffer_resp
    consumed wire_outputs local_outputs

// Isolated helper: prove [network_process_correct]'s shared
// DecodeError/IllegalTransition/ConnectionFailed match arm from its
// constituent facts, each supplied as an explicit parameter/hypothesis
// rather than picked up from a large ambient proof context.  Mirrors the
// server-side [lemma_server_connection_failed_network_process_correct]
// pattern, generalized over the three statuses that share this arm.
let lemma_client_local_fail_network_process_correct
  (initial:client_initial_state)
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
  : Lemma
      (requires
        CPI.buffers_wf input_contents input_len old_network_out out_len /\
        Seq.length network_out == Seq.length old_network_out /\
        (result.CPI.process_status == CPI.DecodeError \/
         result.CPI.process_status == CPI.IllegalTransition \/
         result.CPI.process_status == CPI.ConnectionFailed) /\
        SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
        CPI.network_error_refines_state_machine
          (client_system #CTypes.client_local_event initial)
          (CPI.input_bytes input_contents input_len)
          st0
          st1
          consumed
          wire_outputs
          local_outputs /\
        CPI.output_written
          network_out
          result.CPI.process_produced_len
          (WF.serialize_all CW.tls_record_wire_format wire_outputs) /\
        Seq.equal received1 (Seq.append received0 consumed) /\
        Seq.equal sent1
          (Seq.append sent0 (WF.serialize_all CW.tls_record_wire_format wire_outputs)))
      (ensures
        CPI.network_process_correct
          (client_system #CTypes.client_local_event initial)
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
  | CPI.DecodeError | CPI.IllegalTransition | CPI.ConnectionFailed ->
    FStar.Classical.exists_intro
      (fun produced' ->
        SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
        CPI.network_error_refines_state_machine
          (client_system #CTypes.client_local_event initial)
          (CPI.input_bytes input_contents input_len)
          st0 st1 consumed wire_outputs local_outputs /\
        Seq.equal produced' (WF.serialize_all CW.tls_record_wire_format wire_outputs) /\
        CPI.output_written network_out result.CPI.process_produced_len produced' /\
        Seq.equal received1 (Seq.append received0 consumed) /\
        Seq.equal sent1 (Seq.append sent0 produced'))
      (WF.serialize_all CW.tls_record_wire_format wire_outputs)
  | _ -> assert False

// Shared helper for the DecodeError and (zero-consumed) IllegalTransition
// cases: both are modeled as a purely local [LocalFail err] event with empty
// raw_sent/raw_received deltas, so [consumed] and [produced] are both empty
// and the [network_error_refines_state_machine] LocalEvent disjunct applies.
#push-options "--z3rlimit 100"
let lemma_client_local_fail_bridge_result
  (initial:client_initial_state)
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
  (err:T.tls_error)
  : Lemma
      (requires
        client_invariant_pure initial received0 sent0 st0 /\
        CPI.buffers_wf input_contents input_len old_network_out out_len /\
        B.length input_contents == SZ.v input_len /\
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
        (buffer_resp.CT.response.CT.status == CT.DecodeError \/
         buffer_resp.CT.response.CT.status == CT.IllegalTransition \/
         buffer_resp.CT.response.CT.status == CT.ConnectionFailed) /\
        buffer_resp.CT.consumed_len == 0sz /\
        CT.legal_response_for_event
          st0
          st1
          buffer_resp.CT.response
          (CS.ConnLocalEvent (CS.LocalFail err))
          B.empty
          B.empty
          network_out
          app_out)
      (ensures
        client_network_bridge_result
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
  let resp = buffer_resp.CT.response in
  let conn_ev = CS.ConnLocalEvent (CS.LocalFail err) in
  CW.lemma_wire_outputs_of_empty ();
  Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format []) B.empty;
  let api : CTypes.client_api_event = {
    CTypes.client_local_kind = CT.LocalFail;
    CTypes.client_local_payload = B.empty;
  } in
  assert_norm (CT.local_event_kind_matches st0 CT.LocalFail B.empty conn_ev);
  assert (client_api_event_matches st0 api conn_ev);
  assert (CT.legal_delta st0 st1 conn_ev B.empty B.empty);
  assert (CS.legal_connection_delta st0 {
    CS.delta_event = conn_ev;
    CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format [];
    CS.delta_raw_received = B.empty;
  } st1);
  assert (SMRep.sent_event_nonempty_seal_projection
    st0.CS.cs_model conn_ev (WF.serialize_all CW.tls_record_wire_format []));
  assert (SMRep.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty);
  // Local output: response_app_out_matches_event forces the response's app
  // bytes to match the (empty) app-received delta of a LocalFail event.
  assert (CT.response_app_out_matches_event resp conn_ev app_out);
  let local_outputs = client_response_local_outputs resp app_out in
  lemma_client_response_local_outputs_match resp conn_ev app_out;
  assert (client_local_outputs_match conn_ev local_outputs);
  assert (Seq.equal B.empty (CT.response_network_out resp network_out));
  assert (CT.response_wf resp network_out app_out);
  assert (SZ.v resp.CT.network_out_len <= B.length network_out);
  lemma_client_response_network_out_len_zero resp network_out;
  assert (resp.CT.network_out_len == 0sz);
  let wire_outputs = client_response_wire_outputs resp network_out in
  lemma_client_response_wire_outputs_serializes resp network_out;
  assert (Seq.equal
    (WF.serialize_all CW.tls_record_wire_format wire_outputs)
    (CT.response_network_out resp network_out));
  Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format wire_outputs) B.empty;
  assert (wire_outputs == []);
  assert (client_step st0 (SM.LocalEvent (CTypes.ClientAPI api)) st1
    (CPI.step_output wire_outputs local_outputs))
  by (
    Tac.norm
      [delta_only [`%client_step]; iota; zeta; primops];
    Tac.smt ());
  let consumed : B.bytes = B.empty in
  let result = CTypes.client_process_result buffer_resp in
  assert (result.CPI.process_status == CPI.DecodeError \/
    result.CPI.process_status == CPI.IllegalTransition \/
    result.CPI.process_status == CPI.ConnectionFailed);
  assert (result.CPI.process_consumed_len == buffer_resp.CT.consumed_len);
  assert (SZ.v result.CPI.process_consumed_len == Seq.length consumed);
  assert (CPI.network_error_refines_state_machine
    (client_system #CTypes.client_local_event initial)
    (CPI.input_bytes input_contents input_len)
    st0
    st1
    consumed
    wire_outputs
    local_outputs);
  lemma_client_response_output_written resp network_out;
  assert (CPI.output_written
    network_out
    result.CPI.process_produced_len
    (WF.serialize_all CW.tls_record_wire_format wire_outputs));
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    (Seq.append st0.CS.cs_wire_log.CL.raw_received consumed));
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (Seq.append st0.CS.cs_wire_log.CL.raw_sent
      (WF.serialize_all CW.tls_record_wire_format wire_outputs)));
  lemma_client_local_fail_network_process_correct
    initial input_contents input_len old_network_out network_out out_len
    received0 sent0 st0 result
    st1.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_sent
    st1 consumed wire_outputs local_outputs;
  assert (CPI.network_process_correct
    (client_system #CTypes.client_local_event initial)
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
  assert (client_network_frame_post_fact
    base result input_contents input_len old_network_out network_out
    st0 st1 consumed wire_outputs local_outputs app_out buffer_resp);
  CT.lemma_network_bytes_end_to_end_correct_preserves_config
    st0 st1 buffer_resp input_contents old_network_out network_out
    (Ghost.reveal base.tls_client_network_old_app_out) app_out;
  assert (client_invariant_pure
    initial
    st1.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_sent
    st1);
  lemma_client_network_common_witness_from_parts
    initial received0 sent0 st0 input_contents input_len
    old_network_out network_out out_len base st1 app_out buffer_resp
    consumed wire_outputs local_outputs;
  lemma_client_network_bridge_result_from_common_witness
    initial received0 sent0 st0 input_contents input_len
    old_network_out network_out out_len base st1 app_out buffer_resp
    consumed wire_outputs local_outputs
#pop-options

let lemma_client_network_decode_error_bridge_result
  (initial:client_initial_state)
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
  : Lemma
      (requires
        client_invariant_pure initial received0 sent0 st0 /\
        CPI.buffers_wf input_contents input_len old_network_out out_len /\
        B.length input_contents == SZ.v input_len /\
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
        buffer_resp.CT.response.CT.status == CT.DecodeError /\
        buffer_resp.CT.consumed_len == 0sz)
      (ensures
        client_network_bridge_result
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
  assert (CT.network_bytes_decode_error_projection
    st0 st1 buffer_resp input_contents network_out app_out);
  assert (CT.decode_error_response st0 st1 buffer_resp.CT.response network_out app_out);
  assert (CT.legal_response_for_event
    st0 st1 buffer_resp.CT.response
    (CS.ConnLocalEvent (CS.LocalFail CT.tls_decode_error))
    B.empty B.empty network_out app_out);
  lemma_client_local_fail_bridge_result
    initial received0 sent0 st0 input_contents input_len
    old_network_out network_out out_len base st1 app_out buffer_resp
    CT.tls_decode_error

let lemma_client_network_illegal_transition_bridge_result
  (initial:client_initial_state)
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
  : Lemma
      (requires
        client_invariant_pure initial received0 sent0 st0 /\
        CPI.buffers_wf input_contents input_len old_network_out out_len /\
        B.length input_contents == SZ.v input_len /\
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
        buffer_resp.CT.response.CT.status == CT.IllegalTransition /\
        buffer_resp.CT.consumed_len == 0sz)
      (ensures
        client_network_bridge_result
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
  let old_app_out = Ghost.reveal base.tls_client_network_old_app_out in
  assert (CT.network_bytes_step_correct
    st0 st1 buffer_resp input_contents old_network_out network_out old_app_out app_out);
  assert (CT.unexpected_message_response
    st0 st1 buffer_resp.CT.response network_out app_out);
  assert (CT.legal_response_for_event
    st0 st1 buffer_resp.CT.response
    (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error))
    B.empty B.empty network_out app_out);
  lemma_client_local_fail_bridge_result
    initial received0 sent0 st0 input_contents input_len
    old_network_out network_out out_len base st1 app_out buffer_resp
    CT.tls_unexpected_message_error

// Isolated helper: prove [network_process_correct]'s StepOk/ConnectionFailed
// match arms from their constituent facts, each supplied as an explicit
// parameter/hypothesis rather than picked up from a large ambient proof
// context.  Mirrors server's [lemma_server_network_step_ok_process_correct]
// isolation pattern.
let lemma_client_wire_event_network_process_correct
  (initial:client_initial_state)
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
  (wire:CW.wire_message)
  (consumed:B.bytes)
  (residual:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list EAPI.local_output)
  : Lemma
      (requires
        CPI.buffers_wf input_contents input_len old_network_out out_len /\
        Seq.length network_out == Seq.length old_network_out /\
        (result.CPI.process_status == CPI.StepOk \/
         result.CPI.process_status == CPI.ConnectionFailed) /\
        SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
        CPI.consumed_by_parse
          CW.tls_record_wire_format
          (CPI.input_bytes input_contents input_len)
          wire consumed residual /\
        (client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
          st0 (SM.WireEvent wire) st1 (CPI.step_output wire_outputs local_outputs) /\
        CPI.network_error_refines_state_machine
          (client_system #CTypes.client_local_event initial)
          (CPI.input_bytes input_contents input_len)
          st0 st1 consumed wire_outputs local_outputs /\
        CPI.output_written
          network_out
          result.CPI.process_produced_len
          (WF.serialize_all CW.tls_record_wire_format wire_outputs) /\
        Seq.equal received1 (Seq.append received0 consumed) /\
        Seq.equal sent1
          (Seq.append sent0 (WF.serialize_all CW.tls_record_wire_format wire_outputs)))
      (ensures
        CPI.network_process_correct
          (client_system #CTypes.client_local_event initial)
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
  let produced = WF.serialize_all CW.tls_record_wire_format wire_outputs in
  match result.CPI.process_status with
  | CPI.StepOk ->
    assert (exists msg' residual' produced'.
      CPI.consumed_by_parse
        CW.tls_record_wire_format
        (CPI.input_bytes input_contents input_len)
        msg' consumed residual' /\
      SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
      (client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
        st0 (SM.WireEvent msg') st1 (CPI.step_output wire_outputs local_outputs) /\
      Seq.equal produced' produced /\
      CPI.output_written network_out result.CPI.process_produced_len produced' /\
      Seq.equal received1 (Seq.append received0 consumed) /\
      Seq.equal sent1 (Seq.append sent0 produced'));
    assert ((client_system #CTypes.client_local_event initial).WFSM.wfsm_wire_format == CW.tls_record_wire_format);
    assert (exists msg' residual' produced'.
      CPI.consumed_by_parse
        (client_system #CTypes.client_local_event initial).WFSM.wfsm_wire_format
        (CPI.input_bytes input_contents input_len)
        msg' consumed residual' /\
      SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
      (client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
        st0 (SM.WireEvent msg') st1 (CPI.step_output wire_outputs local_outputs) /\
      Seq.equal produced'
        (WF.serialize_all
          (client_system #CTypes.client_local_event initial).WFSM.wfsm_wire_format
          wire_outputs) /\
      CPI.output_written network_out result.CPI.process_produced_len produced' /\
      Seq.equal received1 (Seq.append received0 consumed) /\
      Seq.equal sent1 (Seq.append sent0 produced'));
    assert (CPI.network_process_correct
      (client_system #CTypes.client_local_event initial)
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
  | CPI.ConnectionFailed ->
    assert (exists produced'.
      SZ.v result.CPI.process_consumed_len == Seq.length consumed /\
      CPI.network_error_refines_state_machine
        (client_system #CTypes.client_local_event initial)
        (CPI.input_bytes input_contents input_len)
        st0 st1 consumed wire_outputs local_outputs /\
      Seq.equal produced' produced /\
      CPI.output_written network_out result.CPI.process_produced_len produced' /\
      Seq.equal received1 (Seq.append received0 consumed) /\
      Seq.equal sent1 (Seq.append sent0 produced'));
    assert (CPI.network_process_correct
      (client_system #CTypes.client_local_event initial)
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
  | _ -> assert False

// Isolated helper: derive the [process_status] disjunction for the
// StepOk/ConnectionFailed case from the corresponding [client_response]
// status disjunction, in its own small VC (rather than relying on a large
// ambient context to unfold [CTypes.client_process_result]).
let lemma_client_process_result_step_ok_or_connection_failed
  (buffer_resp:CT.client_buffer_response)
  : Lemma
      (requires
        buffer_resp.CT.response.CT.status == CT.StepOk \/
        buffer_resp.CT.response.CT.status == CT.ConnectionFailed)
      (ensures
        (CTypes.client_process_result buffer_resp).CPI.process_status == CPI.StepOk \/
        (CTypes.client_process_result buffer_resp).CPI.process_status == CPI.ConnectionFailed)
= ()

// Isolated helper: derive [network_error_refines_state_machine] for the
// WireEvent case from a wire-parse witness, in its own small VC.
let lemma_client_wire_event_network_error_refines_state_machine
  (initial:client_initial_state)
  (input_contents:B.bytes)
  (input_len:SZ.t)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (wire:CW.wire_message)
  (consumed:B.bytes)
  (residual:B.bytes)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list EAPI.local_output)
  : Lemma
      (requires
        CPI.consumed_by_parse
          CW.tls_record_wire_format
          (CPI.input_bytes input_contents input_len)
          wire consumed residual /\
        (client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
          st0 (SM.WireEvent wire) st1 (CPI.step_output wire_outputs local_outputs))
      (ensures
        CPI.network_error_refines_state_machine
          (client_system #CTypes.client_local_event initial)
          (CPI.input_bytes input_contents input_len)
          st0 st1 consumed wire_outputs local_outputs)
=
  assert ((client_system #CTypes.client_local_event initial).WFSM.wfsm_wire_format == CW.tls_record_wire_format);
  assert (exists msg residual'.
    CPI.consumed_by_parse
      (client_system #CTypes.client_local_event initial).WFSM.wfsm_wire_format
      (CPI.input_bytes input_contents input_len)
      msg consumed residual' /\
    (client_system #CTypes.client_local_event initial).WFSM.wfsm_state_machine.SM.sm_step
      st0 (SM.WireEvent msg) st1 (CPI.step_output wire_outputs local_outputs));
  assert (CPI.network_error_refines_state_machine
    (client_system #CTypes.client_local_event initial)
    (CPI.input_bytes input_contents input_len)
    st0 st1 consumed wire_outputs local_outputs)

// StepOk and ConnectionFailed both arise only via the WireEvent path
// (unexpected_message_response, the alternative disjunct of
// decoded_message_event_projection, forces status == IllegalTransition, so it
// can never explain a StepOk/ConnectionFailed response) — hence
// legal_received_tls_response must hold, giving a genuine wire-parsed message.
let lemma_client_network_wire_event_bridge_result
  (initial:client_initial_state)
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
  : Lemma
      (requires
        client_invariant_pure initial received0 sent0 st0 /\
        CPI.buffers_wf input_contents input_len old_network_out out_len /\
        B.length input_contents == SZ.v input_len /\
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
        (buffer_resp.CT.response.CT.status == CT.StepOk \/
         buffer_resp.CT.response.CT.status == CT.ConnectionFailed))
      (ensures
        client_network_bridge_result
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
  let resp = buffer_resp.CT.response in
  let consumed_len = buffer_resp.CT.consumed_len in
  let raw_consumed = CT.network_consumed_prefix input_contents consumed_len in
  let old_app_out = Ghost.reveal base.tls_client_network_old_app_out in
  assert (CT.network_bytes_step_correct
    st0 st1 buffer_resp input_contents old_network_out network_out old_app_out app_out);
  // response_stuttered forces status == NeedMoreInput, contradicting our
  // hypothesis, so the second (non-stuttered) disjunct of
  // network_bytes_step_correct must hold.
  assert (SZ.v consumed_len <= B.length input_contents);
  Seq.lemma_len_slice input_contents 0 (SZ.v consumed_len);
  assert (Seq.length raw_consumed == SZ.v consumed_len);
  assert (CT.raw_record_parse_success raw_consumed);
  CT.lemma_raw_record_parse_success_nonempty raw_consumed;
  assert (B.length raw_consumed > 0);
  assert (SZ.v consumed_len > 0);
  assert (CT.network_bytes_decoded_message_projection
    st0 st1 buffer_resp input_contents network_out app_out);
  assert (exists content_type fragment msg.
    CT.network_input_message_projection st0 content_type fragment msg raw_consumed /\
    CT.decoded_message_event_projection st0 st1 resp msg raw_consumed network_out app_out);
  let msg =
    FStar.IndefiniteDescription.indefinite_description_ghost
      M.tls_message
      (fun msg -> exists content_type fragment.
        CT.network_input_message_projection st0 content_type fragment msg raw_consumed /\
        CT.decoded_message_event_projection st0 st1 resp msg raw_consumed network_out app_out) in
  assert (CT.decoded_message_event_projection st0 st1 resp msg raw_consumed network_out app_out);
  // unexpected_message_response forces status == IllegalTransition, which is
  // excluded here, so legal_received_tls_response must be the witness.
  assert (CT.legal_received_tls_response st0 st1 resp msg raw_consumed network_out app_out);
  assert (CT.legal_response_for_event st0 st1 resp
    (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = msg })
    B.empty raw_consumed network_out app_out);
  lemma_client_consumed_prefix_parse input_contents consumed_len;
  let wire =
    FStar.IndefiniteDescription.indefinite_description_ghost
      CW.wire_message
      (fun w -> exists residual.
        CPI.consumed_by_parse CW.tls_record_wire_format input_contents w raw_consumed residual /\
        Seq.equal (CW.wire_serialize w) raw_consumed) in
  let residual =
    FStar.IndefiniteDescription.indefinite_description_ghost
      B.bytes
      (fun r ->
        CPI.consumed_by_parse CW.tls_record_wire_format input_contents wire raw_consumed r /\
        Seq.equal (CW.wire_serialize wire) raw_consumed) in
  assert (CPI.consumed_by_parse CW.tls_record_wire_format input_contents wire raw_consumed residual);
  assert (Seq.equal (CW.wire_serialize wire) raw_consumed);
  let conn_ev = CS.ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = msg;
  } in
  assert (Seq.equal B.empty (CT.response_network_out resp network_out));
  assert (CT.response_wf resp network_out app_out);
  assert (SZ.v resp.CT.network_out_len <= B.length network_out);
  lemma_client_response_network_out_len_zero resp network_out;
  assert (resp.CT.network_out_len == 0sz);
  let wire_outputs = client_response_wire_outputs resp network_out in
  lemma_client_response_wire_outputs_serializes resp network_out;
  assert (Seq.equal
    (WF.serialize_all CW.tls_record_wire_format wire_outputs)
    (CT.response_network_out resp network_out));
  Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format wire_outputs) B.empty;
  assert (wire_outputs == []);
  assert (CT.response_app_out_matches_event resp conn_ev app_out);
  let local_outputs = client_response_local_outputs resp app_out in
  lemma_client_response_local_outputs_match resp conn_ev app_out;
  assert (client_local_outputs_match conn_ev local_outputs);
  assert (CT.legal_delta st0 st1 conn_ev B.empty raw_consumed);
  assert (CS.legal_connection_delta st0 {
    CS.delta_event = conn_ev;
    CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format wire_outputs;
    CS.delta_raw_received = CW.wire_serialize wire;
  } st1);
  assert (SMRep.sent_event_nonempty_seal_projection
    st0.CS.cs_model conn_ev (WF.serialize_all CW.tls_record_wire_format wire_outputs));
  lemma_client_received_network_event_nonempty_decode_projection st0 msg raw_consumed;
  assert (SMRep.received_event_nonempty_decode_projection
    st0.CS.cs_model conn_ev (CW.wire_serialize wire));
  assert (exists content_type' fragment'.
    CT.network_input_message_projection st0 content_type' fragment' msg (CW.wire_serialize wire));
  let content_type =
    FStar.IndefiniteDescription.indefinite_description_ghost
      U8.t
      (fun content_type -> exists fragment.
        CT.network_input_message_projection
          st0 content_type fragment msg (CW.wire_serialize wire)) in
  let fragment =
    FStar.IndefiniteDescription.indefinite_description_ghost
      B.bytes
      (fun fragment ->
        CT.network_input_message_projection
          st0 content_type fragment msg (CW.wire_serialize wire)) in
  lemma_client_network_input_projection_refines_core
    st0
    content_type
    fragment
    msg
    wire;
  assert (EC.network_input_message_projection st0 wire msg);
  assert (client_step #CTypes.client_local_event st0 (SM.WireEvent wire) st1
    (CPI.step_output wire_outputs local_outputs))
  by (
    Tac.norm
      [delta_only [`%client_step]; iota; zeta; primops];
    Tac.smt ());
  let consumed = raw_consumed in
  let result = CTypes.client_process_result buffer_resp in
  lemma_client_process_result_step_ok_or_connection_failed buffer_resp;
  assert (result.CPI.process_status == CPI.StepOk \/
    result.CPI.process_status == CPI.ConnectionFailed);
  assert (SZ.v result.CPI.process_consumed_len == Seq.length consumed);
  assert (CPI.consumed_by_parse
    CW.tls_record_wire_format
    (CPI.input_bytes input_contents input_len)
    wire
    consumed
    residual);
  lemma_client_response_output_written resp network_out;
  assert (CPI.output_written
    network_out
    result.CPI.process_produced_len
    (WF.serialize_all CW.tls_record_wire_format wire_outputs));
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    (Seq.append st0.CS.cs_wire_log.CL.raw_received consumed));
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (Seq.append st0.CS.cs_wire_log.CL.raw_sent
      (WF.serialize_all CW.tls_record_wire_format wire_outputs)));
  lemma_client_wire_event_network_error_refines_state_machine
    initial input_contents input_len st0 st1 wire consumed residual
    wire_outputs local_outputs;
  assert (CPI.network_error_refines_state_machine
    (client_system #CTypes.client_local_event initial)
    (CPI.input_bytes input_contents input_len)
    st0 st1 consumed wire_outputs local_outputs);
  lemma_client_wire_event_network_process_correct
    initial input_contents input_len old_network_out network_out out_len
    received0 sent0 st0 result
    st1.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_sent
    st1 wire consumed residual wire_outputs local_outputs;
  assert (CPI.network_process_correct
    (client_system #CTypes.client_local_event initial)
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
  assert (client_network_frame_post_fact
    base result input_contents input_len old_network_out network_out
    st0 st1 consumed wire_outputs local_outputs app_out buffer_resp);
  CT.lemma_network_bytes_end_to_end_correct_preserves_config
    st0 st1 buffer_resp input_contents old_network_out network_out
    (Ghost.reveal base.tls_client_network_old_app_out) app_out;
  assert (client_invariant_pure
    initial
    st1.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_sent
    st1);
  lemma_client_network_common_witness_from_parts
    initial received0 sent0 st0 input_contents input_len
    old_network_out network_out out_len base st1 app_out buffer_resp
    consumed wire_outputs local_outputs;
  lemma_client_network_bridge_result_from_common_witness
    initial received0 sent0 st0 input_contents input_len
    old_network_out network_out out_len base st1 app_out buffer_resp
    consumed wire_outputs local_outputs

(**
  The head step of a protected handshake record yields the same network bridge
  result as a received network message.  This is the second disjunct of
  [coalesced_network_bytes_end_to_end_correct], and the reason the canonical
  ProtocolImplementation can be pointed at the coalescing receive primitive.
 **)
let lemma_client_network_protected_head_bridge_result
  (initial:client_initial_state)
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
  (step:CS.protected_handshake_step)
  : Lemma
      (requires
        client_invariant_pure initial received0 sent0 st0 /\
        CPI.buffers_wf input_contents input_len old_network_out out_len /\
        B.length input_contents == SZ.v input_len /\
        B.length network_out == B.length old_network_out /\
        B.length app_out == SZ.v base.tls_client_network_app_out_len /\
        0 < SZ.v buffer_resp.CT.consumed_len /\
        SZ.v buffer_resp.CT.consumed_len <= B.length input_contents /\
        CT.protected_handshake_step_correct
          st0
          st1
          buffer_resp.CT.response
          step
          (CT.network_consumed_prefix input_contents buffer_resp.CT.consumed_len)
          network_out
          app_out /\
        Seq.equal network_out old_network_out /\
        Seq.equal app_out (Ghost.reveal base.tls_client_network_old_app_out))
      (ensures
        client_network_bridge_result
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
  let resp = buffer_resp.CT.response in
  let consumed_len = buffer_resp.CT.consumed_len in
  let raw_consumed = CT.network_consumed_prefix input_contents consumed_len in
  let conn_ev = CS.ConnProtectedHandshake step in
  let old_app_out = Ghost.reveal base.tls_client_network_old_app_out in
  Seq.lemma_len_slice input_contents 0 (SZ.v consumed_len);
  assert (Seq.length raw_consumed == SZ.v consumed_len);
  assert (B.length raw_consumed > 0);
  assert (CT.legal_response_for_event
    st0 st1 resp conn_ev B.empty raw_consumed network_out app_out);
  assert (CT.legal_delta st0 st1 conn_ev B.empty raw_consumed);
  // A tail step demands an empty raw-received delta, but the consumed prefix
  // is non-empty; hence this is the head step of the record.
  assert (step.CS.protected_handshake_head == true);
  assert (CS.raw_records_exactly raw_consumed T.Application_data 1);
  CSL.lemma_raw_records_exactly_one_parse_record raw_consumed T.Application_data;
  WS.lemma_parse_record_implies_parse_record_wire raw_consumed;
  assert (CT.raw_record_parse_success raw_consumed);
  lemma_client_consumed_prefix_parse input_contents consumed_len;
  let wire =
    FStar.IndefiniteDescription.indefinite_description_ghost
      CW.wire_message
      (fun w -> exists residual.
        CPI.consumed_by_parse CW.tls_record_wire_format input_contents w raw_consumed residual /\
        Seq.equal (CW.wire_serialize w) raw_consumed) in
  let residual =
    FStar.IndefiniteDescription.indefinite_description_ghost
      B.bytes
      (fun r ->
        CPI.consumed_by_parse CW.tls_record_wire_format input_contents wire raw_consumed r /\
        Seq.equal (CW.wire_serialize wire) raw_consumed) in
  assert (CPI.consumed_by_parse CW.tls_record_wire_format input_contents wire raw_consumed residual);
  assert (Seq.equal (CW.wire_serialize wire) raw_consumed);
  assert (Seq.equal B.empty (CT.response_network_out resp network_out));
  assert (CT.response_wf resp network_out app_out);
  lemma_client_response_network_out_len_zero resp network_out;
  assert (resp.CT.network_out_len == 0sz);
  let wire_outputs = client_response_wire_outputs resp network_out in
  lemma_client_response_wire_outputs_serializes resp network_out;
  Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format wire_outputs) B.empty;
  assert (wire_outputs == []);
  assert (CT.response_app_out_matches_event resp conn_ev app_out);
  let local_outputs = client_response_local_outputs resp app_out in
  lemma_client_response_local_outputs_match resp conn_ev app_out;
  assert (client_local_outputs_match conn_ev local_outputs);
  assert (CS.legal_connection_delta st0 {
    CS.delta_event = conn_ev;
    CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format wire_outputs;
    CS.delta_raw_received = CW.wire_serialize wire;
  } st1);
  assert (SMRep.sent_event_nonempty_seal_projection
    st0.CS.cs_model conn_ev (WF.serialize_all CW.tls_record_wire_format wire_outputs));
  assert (SMRep.received_event_nonempty_decode_projection
    st0.CS.cs_model conn_ev (CW.wire_serialize wire));
  assert (SMCan.canonical_wire_step st0 st1 conn_ev
    (WF.serialize_all CW.tls_record_wire_format wire_outputs)
    (CW.wire_serialize wire));
  EC.lemma_client_wire_step_from_protected_head_witness
    #CTypes.client_local_event
    st0 st1 wire step (CPI.step_output wire_outputs local_outputs);
  assert (client_step #CTypes.client_local_event st0 (SM.WireEvent wire) st1
    (CPI.step_output wire_outputs local_outputs));
  let consumed = raw_consumed in
  let result = CTypes.client_process_result buffer_resp in
  lemma_client_process_result_step_ok_or_connection_failed buffer_resp;
  assert (SZ.v result.CPI.process_consumed_len == Seq.length consumed);
  lemma_client_response_output_written resp network_out;
  assert (CPI.output_written
    network_out
    result.CPI.process_produced_len
    (WF.serialize_all CW.tls_record_wire_format wire_outputs));
  lemma_client_wire_event_network_error_refines_state_machine
    initial input_contents input_len st0 st1 wire consumed residual
    wire_outputs local_outputs;
  lemma_client_wire_event_network_process_correct
    initial input_contents input_len old_network_out network_out out_len
    received0 sent0 st0 result
    st1.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_sent
    st1 wire consumed residual wire_outputs local_outputs;
  assert (CT.coalesced_network_bytes_end_to_end_correct
    st0 st1 buffer_resp input_contents old_network_out network_out
    old_app_out app_out);
  CT.lemma_coalesced_network_bytes_end_to_end_correct_preserves_invariant
    st0 st1 buffer_resp input_contents old_network_out network_out
    old_app_out app_out;
  CSL.lemma_step_model_preserves_config st0.CS.cs_model conn_ev st1.CS.cs_model;
  assert (client_invariant_pure
    initial
    st1.CS.cs_wire_log.CL.raw_received
    st1.CS.cs_wire_log.CL.raw_sent
    st1);
  assert (client_network_frame_post_fact
    base result input_contents input_len old_network_out network_out
    st0 st1 consumed wire_outputs local_outputs app_out buffer_resp);
  lemma_client_network_common_witness_from_parts
    initial received0 sent0 st0 input_contents input_len
    old_network_out network_out out_len base st1 app_out buffer_resp
    consumed wire_outputs local_outputs;
  lemma_client_network_bridge_result_from_common_witness
    initial received0 sent0 st0 input_contents input_len
    old_network_out network_out out_len base st1 app_out buffer_resp
    consumed wire_outputs local_outputs

let lemma_client_network_bridge_obligation
  (base:tls_client_network_frame)
  : Lemma
      (ensures client_network_bridge_obligation base)=
  introduce forall initial received0 sent0 st0 input_contents input_len
    old_network_out network_out out_len st1 app_out buffer_resp.
    client_invariant_pure initial received0 sent0 st0 /\
    CPI.buffers_wf input_contents input_len old_network_out out_len /\
    B.length input_contents == SZ.v input_len /\
    B.length network_out == B.length old_network_out /\
    B.length app_out == SZ.v base.tls_client_network_app_out_len /\
    CT.coalesced_network_bytes_end_to_end_correct
      st0
      st1
      buffer_resp
      input_contents
      old_network_out
      network_out
      (Ghost.reveal base.tls_client_network_old_app_out)
      app_out /\
    (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
      buffer_resp.CT.consumed_len == 0sz /\
      WS.parse_record_wire input_contents == None) /\
    (buffer_resp.CT.response.CT.status == CT.DecodeError ==>
      buffer_resp.CT.consumed_len == 0sz) /\
    (buffer_resp.CT.response.CT.status == CT.IllegalTransition ==>
      buffer_resp.CT.consumed_len == 0sz) /\
    (buffer_resp.CT.response.CT.status == CT.OutputBufferTooSmall ==> False)
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
  with
    introduce _ ==> _ with _.
    let old_app_out = Ghost.reveal base.tls_client_network_old_app_out in
    match buffer_resp.CT.response.CT.status with
    | CT.StepOk ->
      if CT.network_bytes_end_to_end_correct
           st0 st1 buffer_resp input_contents
           old_network_out network_out old_app_out app_out
      then
        lemma_client_network_wire_event_bridge_result
          initial received0 sent0 st0 input_contents input_len
          old_network_out network_out out_len base st1 app_out buffer_resp
      else (
        // The coalesced predicate's second disjunct: a head protected-handshake
        // step consuming a non-empty prefix of the input.
        let step =
          FStar.IndefiniteDescription.indefinite_description_ghost
            CS.protected_handshake_step
            (fun step ->
              0 < SZ.v buffer_resp.CT.consumed_len /\
              SZ.v buffer_resp.CT.consumed_len <= B.length input_contents /\
              CT.protected_handshake_step_correct
                st0 st1 buffer_resp.CT.response step
                (CT.network_consumed_prefix input_contents buffer_resp.CT.consumed_len)
                network_out app_out /\
              Seq.equal network_out old_network_out /\
              Seq.equal app_out old_app_out) in
        lemma_client_network_protected_head_bridge_result
          initial received0 sent0 st0 input_contents input_len
          old_network_out network_out out_len base st1 app_out buffer_resp step
      )
    | CT.NeedMoreInput ->
      lemma_client_coalesced_not_step_ok_is_strong
        st0 st1 buffer_resp input_contents
        old_network_out network_out old_app_out app_out;
      lemma_client_network_need_more_input_bridge_result
        initial received0 sent0 st0 input_contents input_len
        old_network_out network_out out_len base st1 app_out buffer_resp
    | CT.DecodeError ->
      lemma_client_coalesced_not_step_ok_is_strong
        st0 st1 buffer_resp input_contents
        old_network_out network_out old_app_out app_out;
      lemma_client_network_decode_error_bridge_result
        initial received0 sent0 st0 input_contents input_len
        old_network_out network_out out_len base st1 app_out buffer_resp
    | CT.IllegalTransition ->
      lemma_client_coalesced_not_step_ok_is_strong
        st0 st1 buffer_resp input_contents
        old_network_out network_out old_app_out app_out;
      lemma_client_network_illegal_transition_bridge_result
        initial received0 sent0 st0 input_contents input_len
        old_network_out network_out out_len base st1 app_out buffer_resp
    | CT.OutputBufferTooSmall ->
      assert False
    | CT.ConnectionFailed ->
      lemma_client_coalesced_not_step_ok_is_strong
        st0 st1 buffer_resp input_contents
        old_network_out network_out old_app_out app_out;
      lemma_client_network_wire_event_bridge_result
        initial received0 sent0 st0 input_contents input_len
        old_network_out network_out out_len base st1 app_out buffer_resp

noeq
type tls_client_network_bridge_frame = {
  tls_client_network_bridge_base: tls_client_network_frame;
}

let lemma_client_network_bridge_frame_obligation
  (frame:tls_client_network_bridge_frame)
  : Lemma
      (ensures
        client_network_bridge_obligation frame.tls_client_network_bridge_base)
=
  lemma_client_network_bridge_obligation frame.tls_client_network_bridge_base

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
  (local_outputs:list EAPI.local_output)
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
          (local_outputs:list EAPI.local_output).
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
        (client_system
          #CTypes.client_local_event
          (Ghost.reveal cc.canonical_client_initial))
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
    C.process_coalesced_network_bytes
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
  assert (pure (CT.coalesced_network_bytes_end_to_end_correct
    (Ghost.reveal st0)
    st1
    buffer_resp
    (Ghost.reveal input_contents)
    (Ghost.reveal old_out)
    network_out_bytes
    (Ghost.reveal frame.tls_client_network_bridge_base.tls_client_network_old_app_out)
    app_out_bytes));
  assert (pure (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
    buffer_resp.CT.consumed_len == 0sz /\
    WS.parse_record_wire (Ghost.reveal input_contents) == None));
  assert (pure (buffer_resp.CT.response.CT.status == CT.DecodeError ==>
    buffer_resp.CT.consumed_len == 0sz));
  assert (pure (buffer_resp.CT.response.CT.status == CT.IllegalTransition ==>
    buffer_resp.CT.consumed_len == 0sz));
  assert (pure (buffer_resp.CT.response.CT.status == CT.OutputBufferTooSmall ==> False));
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
    exists (local_outputs:list EAPI.local_output).
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
        exists (local_outputs:list EAPI.local_output).
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
    exists (local_outputs:list EAPI.local_output).
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
    exists (local_outputs:list EAPI.local_output).
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
        exists (local_outputs:list EAPI.local_output).
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
  assert (pure (exists (local_outputs:list EAPI.local_output).
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
  let local_outputse : Ghost.erased (local_outputs:list EAPI.local_output{
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
      (list EAPI.local_output)
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
  assert (pure (CT.coalesced_network_bytes_end_to_end_correct
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
    (client_system
      #CTypes.client_local_event
      (Ghost.reveal cc.canonical_client_initial))
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
    (client_system
      #CTypes.client_local_event
      (Ghost.reveal cc.canonical_client_initial))
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
  pure (
    SZ.v out_len == Seq.length (Ghost.reveal old_out) /\
    ~ (client_is_internal ev))
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased B.bytes)
                (sent1:Ghost.erased B.bytes)
                (st1:Ghost.erased CS.connection_state)
                (out_contents:B.bytes)
                (wire_outputs:list CW.wire_message)
                (local_outputs:list EAPI.local_output).
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
      (client_system
        #CTypes.client_local_event
        (Ghost.reveal cc.canonical_client_initial))
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
    let local_outputse : Ghost.erased (local_outputs:list EAPI.local_output{
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
      (client_system
        #CTypes.client_local_event
        (Ghost.reveal cc.canonical_client_initial))
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


(** A step consuming no raw input cannot be a HEAD step: a head step must
    take delivery of exactly one Application_data record, and the empty byte
    string carries none. **)
let lemma_protected_step_empty_raw_is_tail
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  : Lemma
      (requires CS.event_raw_delta_legal model (CS.ConnProtectedHandshake step) B.empty B.empty)
      (ensures step.CS.protected_handshake_head == false)
=
  if step.CS.protected_handshake_head
  then (
    CSL.lemma_raw_records_exactly_one_parse_record B.empty T.Application_data;
    WS.lemma_parse_record_implies_parse_record_wire B.empty;
    eliminate exists fragment.
      WS.parse_record B.empty == Some (T.Application_data, fragment, B.length B.empty)
    returns False
    with _pr.
      WS.lemma_parse_record_wire_some_consumed_positive
        B.empty T.Application_data fragment (B.length B.empty)
  )

(** The internal kind matches only TAIL protected-handshake events. **)
let lemma_internal_kind_matches_only_tail
  (st:CS.connection_state)
  (payload:B.bytes)
  (ev:CS.conn_event)
  : Lemma
      (requires
        CT.local_event_kind_matches st CT.LocalProcessPendingHandshake payload ev)
      (ensures
        (exists step.
          ev == CS.ConnProtectedHandshake step /\
          step.CS.protected_handshake_head == false))
=
  match ev with
  | CS.ConnProtectedHandshake step ->
    CT.lemma_local_event_kind_matches_protected_is_tail
      st CT.LocalProcessPendingHandshake payload step
  | _ -> ()

(** When the pending buffer holds no unprocessed plaintext, no internal step
    is enabled: a tail step's legality requires its offset -- which is pinned
    to [hb_encrypted_server_handshake_parsed] -- to lie strictly inside the
    buffer. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_no_internal_step_when_not_pending
  (initial:EC.client_initial_state)
  (st0:CS.connection_state)
  : Lemma
      (requires ~ (client_internal_pending st0))
      (ensures
        CPI.no_internal_step_enabled
          (client_system #CTypes.client_local_event initial)
          client_is_internal
          st0)
=
  introduce
    CPI.internal_step_enabled
      (client_system #CTypes.client_local_event initial)
      client_is_internal
      st0
    ==> False
  with _pf. (
    eliminate exists (ev:CTypes.client_local_event)
                     (st1:CS.connection_state)
                     (output:SM.step_output CW.wire_message EAPI.local_output).
      client_is_internal ev /\
      client_step st0 (SM.LocalEvent ev) st1 output
    returns False
    with _pe. (
      eliminate exists conn_ev raw_sent.
        client_representation_matches st0 ev conn_ev /\
        client_wire_outputs_match raw_sent output.SM.so_wire_outputs /\
        client_local_outputs_match conn_ev output.SM.so_local_outputs /\
        SMCan.canonical_wire_step st0 st1 conn_ev raw_sent B.empty
      returns False
      with _pc. (
        lemma_client_is_internal_api_kind ev;
        assert (CTypes.client_local_event_matches st0 ev conn_ev);
        assert (CT.local_event_kind_matches
          st0
          CT.LocalProcessPendingHandshake
          (CTypes.client_local_event_api ev).CTypes.client_local_payload
          conn_ev);
        lemma_internal_kind_matches_only_tail
          st0
          (CTypes.client_local_event_api ev).CTypes.client_local_payload
          conn_ev;
        eliminate exists step.
          conn_ev == CS.ConnProtectedHandshake step /\
          step.CS.protected_handshake_head == false
        returns False
        with _ps. (
          assert (CS.legal_protected_handshake_step st0.CS.cs_model step);
          assert (step.CS.protected_handshake_offset <
            B.length step.CS.protected_handshake_fragment)
        )
      )
    )
  )
#pop-options

(** A successful drain of one pending handshake message IS a client local
    step at the internal event.  This is decision S1 discharged for TLS: the
    internal step inherits the local-event refinement rather than needing a
    parallel one. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 60"
let lemma_internal_step_is_client_step
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:CT.client_response)
  (step:CS.protected_handshake_step)
  : Lemma
      (requires
        CT.protected_handshake_step_correct st0 st1 resp step B.empty B.empty B.empty)
      (ensures
        client_step
          st0
          (SM.LocalEvent client_internal_event)
          st1
          (CPI.step_output
            ([] <: list CW.wire_message)
            ([] <: list EAPI.local_output)))
=
  let conn_ev = CS.ConnProtectedHandshake step in
  assert (CT.legal_response_for_event
    st0 st1 resp conn_ev B.empty B.empty B.empty B.empty);
  assert (CS.legal_connection_delta st0 {
    CS.delta_event = conn_ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } st1);
  lemma_protected_step_empty_raw_is_tail st0.CS.cs_model step;
  assert (CT.local_event_kind_matches
    st0 CT.LocalProcessPendingHandshake B.empty conn_ev);
  CTypes.lemma_client_api_event_semantic_exact
    st0
    (CTypes.client_local_event_api client_internal_event)
    conn_ev;
  assert (client_api_event_matches
    st0
    (CTypes.client_local_event_api client_internal_event)
    conn_ev);
  assert (Seq.equal
    (WF.serialize_all CW.tls_record_wire_format ([] <: list CW.wire_message))
    B.empty);
  assert (client_wire_outputs_match B.empty ([] <: list CW.wire_message));
  assert (Seq.equal
    (EAPI.local_outputs_app_bytes ([] <: list EAPI.local_output))
    (CL.concat_bytes (EAPI.conn_event_app_received_delta conn_ev)));
  assert (client_local_outputs_match conn_ev ([] <: list EAPI.local_output));
  assert (B.length B.empty == 0);
  assert (SMRep.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev B.empty);
  lemma_client_step_from_local_witness
    st0
    st1
    client_internal_event
    conn_ev
    B.empty
    ([] <: list CW.wire_message)
    ([] <: list EAPI.local_output)
#pop-options

let internal_noop_result : CPI.internal_result =
  {
    CPI.internal_status = CPI.InternalQuiescent;
    CPI.internal_process = {
      CPI.process_status = CPI.StepOk;
      CPI.process_consumed_len = 0sz;
      CPI.process_produced_len = 0sz;
      CPI.process_app_len = 0sz;
    };
  }

let internal_progress_result : CPI.internal_result =
  {
    CPI.internal_status = CPI.InternalProgress;
    CPI.internal_process = {
      CPI.process_status = CPI.StepOk;
      CPI.process_consumed_len = 0sz;
      CPI.process_produced_len = 0sz;
      CPI.process_app_len = 0sz;
    };
  }

let internal_failed_result (status:CPI.process_status) : CPI.internal_result =
  {
    CPI.internal_status = CPI.InternalFailed;
    CPI.internal_process = {
      CPI.process_status = status;
      CPI.process_consumed_len = 0sz;
      CPI.process_produced_len = 0sz;
      CPI.process_app_len = 0sz;
    };
  }

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_internal_quiescent_correct
  (initial:EC.client_initial_state)
  (st0:CS.connection_state)
  (old_out:B.bytes)
  (out_len:SZ.t)
  (received0:B.bytes)
  (sent0:B.bytes)
  : Lemma
      (requires
        ~ (client_internal_pending st0) /\
        SZ.v out_len == Seq.length old_out)
      (ensures
        CPI.internal_process_correct
          (client_system #CTypes.client_local_event initial)
          client_is_internal
          client_internal_pending
          old_out old_out out_len
          received0 sent0 st0
          internal_noop_result
          received0 sent0 st0
          ([] <: list CW.wire_message)
          ([] <: list EAPI.local_output))
=
  lemma_no_internal_step_when_not_pending initial st0
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 80"
let lemma_internal_progress_correct
  (initial:EC.client_initial_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:CT.client_response)
  (old_out:B.bytes)
  (out_len:SZ.t)
  (received0:B.bytes)
  (sent0:B.bytes)
  : Lemma
      (requires
        CT.pending_protected_handshake_result_correct st0 st1 (Some resp) /\
        resp.CT.status == CT.StepOk /\
        SZ.v out_len == Seq.length old_out /\
        Seq.equal received0 st0.CS.cs_wire_log.CL.raw_received /\
        Seq.equal sent0 st0.CS.cs_wire_log.CL.raw_sent)
      (ensures
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config /\
        CPI.internal_process_correct
          (client_system #CTypes.client_local_event initial)
          client_is_internal
          client_internal_pending
          old_out old_out out_len
          received0 sent0 st0
          internal_progress_result
          st1.CS.cs_wire_log.CL.raw_received
          st1.CS.cs_wire_log.CL.raw_sent
          st1
          ([] <: list CW.wire_message)
          ([] <: list EAPI.local_output))
=
  eliminate exists step.
    CT.protected_handshake_step_correct st0 st1 resp step B.empty B.empty B.empty
  returns
    st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config /\
    CPI.internal_process_correct
      (client_system #CTypes.client_local_event initial)
      client_is_internal
      client_internal_pending
      old_out old_out out_len
      received0 sent0 st0
      internal_progress_result
      st1.CS.cs_wire_log.CL.raw_received
      st1.CS.cs_wire_log.CL.raw_sent
      st1
      ([] <: list CW.wire_message)
      ([] <: list EAPI.local_output)
  with _ps. (
    lemma_internal_step_is_client_step st0 st1 resp step;
    lemma_client_internal_event_is_internal ();
    CSL.lemma_step_model_preserves_config
      st0.CS.cs_model
      (CS.ConnProtectedHandshake step)
      st1.CS.cs_model;
    assert (CS.legal_connection_delta st0 {
      CS.delta_event = CS.ConnProtectedHandshake step;
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    } st1);
    assert (Seq.equal st1.CS.cs_wire_log.CL.raw_received received0);
    assert (Seq.equal
      st1.CS.cs_wire_log.CL.raw_sent
      (Seq.append sent0 (B.empty <: B.bytes)));
    assert (Seq.equal
      (WF.serialize_all CW.tls_record_wire_format ([] <: list CW.wire_message))
      B.empty);
    assert (CPI.output_written old_out 0sz (B.empty <: B.bytes))
  )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 60"
let lemma_internal_failed_correct
  (initial:EC.client_initial_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:CT.client_response)
  (old_out:B.bytes)
  (out_len:SZ.t)
  (received0:B.bytes)
  (sent0:B.bytes)
  : Lemma
      (requires
        CT.pending_protected_handshake_result_correct st0 st1 (Some resp) /\
        (resp.CT.status == CT.DecodeError \/
         resp.CT.status == CT.IllegalTransition) /\
        SZ.v out_len == Seq.length old_out /\
        Seq.equal received0 st0.CS.cs_wire_log.CL.raw_received /\
        Seq.equal sent0 st0.CS.cs_wire_log.CL.raw_sent)
      (ensures
        st1 == st0 /\
        CPI.internal_process_correct
          (client_system #CTypes.client_local_event initial)
          client_is_internal
          client_internal_pending
          old_out old_out out_len
          received0 sent0 st0
          (internal_failed_result
            (if resp.CT.status = CT.DecodeError
             then CPI.DecodeError
             else CPI.IllegalTransition))
          received0 sent0 st0
          ([] <: list CW.wire_message)
          ([] <: list EAPI.local_output))
=
  lemma_client_internal_event_is_internal ();
  assert (Seq.equal
    (WF.serialize_all CW.tls_record_wire_format ([] <: list CW.wire_message))
    B.empty);
  assert (CPI.output_written old_out 0sz (B.empty <: B.bytes));
  assert (Seq.equal received0 received0);
  assert (Seq.equal sent0 (Seq.append sent0 (B.empty <: B.bytes)));
  assert (CPI.local_error_refines_state_machine
    (client_system #CTypes.client_local_event initial)
    st0 st0
    ([] <: list CW.wire_message)
    ([] <: list EAPI.local_output))
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_internal_progress_preorder
  (initial:EC.client_initial_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:CT.client_response)
  : Lemma
      (requires
        CT.pending_protected_handshake_result_correct st0 st1 (Some resp) /\
        resp.CT.status == CT.StepOk)
      (ensures client_progress_preorder #CTypes.client_local_event st0 st1)
=
  if st0 = st1
  then assert (client_progress_preorder #CTypes.client_local_event st0 st1)
  else (
    eliminate exists step.
      CT.protected_handshake_step_correct st0 st1 resp step B.empty B.empty B.empty
    returns client_canonical_step_rel #CTypes.client_local_event st0 st1
    with _ps. lemma_internal_step_is_client_step st0 st1 resp step;
    RTC.closure_step
      (client_canonical_step_rel #CTypes.client_local_event)
      st0
      st1
  )
#pop-options

fn client_process_internal
  (cc:canonical_client)
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
  client_internal_frame_pre
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
  client_invariant
    cc
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1) **
  client_internal_frame_post
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
      (client_system
        #CTypes.client_local_event
        (Ghost.reveal cc.canonical_client_initial))
      client_is_internal
      client_internal_pending
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
  unfold (client_internal_frame_pre
    frame
    (Ghost.reveal st0)
    out
    out_len
    (Ghost.reveal old_out));
  let empty_payload = V.alloc 0uy 0sz;
  V.to_array_pts_to empty_payload;
  rewrite
    (C.connection_exactly cc.canonical_client_state (Ghost.reveal st0))
    as
    (CR.connection_exactly cc.canonical_client_state (Ghost.reveal st0));
  let pending =
    C.process_pending_protected_handshake
      cc.canonical_client_state
      (V.vec_to_array empty_payload);
  with st1. assert (CR.connection_exactly cc.canonical_client_state st1);
  V.to_vec_pts_to empty_payload;
  V.free empty_payload;
  match pending {
    None -> {
      rewrite
        (CR.connection_exactly cc.canonical_client_state st1)
        as
        (C.connection_exactly cc.canonical_client_state (Ghost.reveal st0));
      lemma_internal_quiescent_correct
        (Ghost.reveal cc.canonical_client_initial)
        (Ghost.reveal st0)
        (Ghost.reveal old_out)
        out_len
        (Ghost.reveal received0)
        (Ghost.reveal sent0);
      fold (client_internal_frame_post
        frame
        internal_noop_result
        (Ghost.reveal old_out)
        (Ghost.reveal old_out)
        (Ghost.reveal st0)
        (Ghost.reveal st0)
        ([] <: list CW.wire_message)
        ([] <: list EAPI.local_output));
      fold (client_invariant
        cc
        (Ghost.reveal received0)
        (Ghost.reveal sent0)
        (Ghost.reveal st0));
      internal_noop_result
    }
    Some resp -> {
      let ok = resp.CT.status = CT.StepOk;
      if ok {
        let st1e : Ghost.erased CS.connection_state = Ghost.hide st1;
        let received1e : Ghost.erased B.bytes =
          Ghost.hide st1.CS.cs_wire_log.CL.raw_received;
        let sent1e : Ghost.erased B.bytes =
          Ghost.hide st1.CS.cs_wire_log.CL.raw_sent;
        lemma_internal_progress_correct
          (Ghost.reveal cc.canonical_client_initial)
          (Ghost.reveal st0)
          st1
          resp
          (Ghost.reveal old_out)
          out_len
          (Ghost.reveal received0)
          (Ghost.reveal sent0);
        lemma_internal_progress_preorder
          (Ghost.reveal cc.canonical_client_initial)
          (Ghost.reveal st0)
          st1
          resp;
        rewrite
          (CR.connection_exactly cc.canonical_client_state st1)
          as
          (C.connection_exactly cc.canonical_client_state (Ghost.reveal st1e));
        MR.update cc.canonical_client_progress (Ghost.reveal st1e);
        fold (client_internal_frame_post
          frame
          internal_progress_result
          (Ghost.reveal old_out)
          (Ghost.reveal old_out)
          (Ghost.reveal st0)
          (Ghost.reveal st1e)
          ([] <: list CW.wire_message)
          ([] <: list EAPI.local_output));
        fold (client_invariant
          cc
          (Ghost.reveal received1e)
          (Ghost.reveal sent1e)
          (Ghost.reveal st1e));
        internal_progress_result
      } else {
        lemma_internal_failed_correct
          (Ghost.reveal cc.canonical_client_initial)
          (Ghost.reveal st0)
          st1
          resp
          (Ghost.reveal old_out)
          out_len
          (Ghost.reveal received0)
          (Ghost.reveal sent0);
        rewrite
          (CR.connection_exactly cc.canonical_client_state st1)
          as
          (C.connection_exactly cc.canonical_client_state (Ghost.reveal st0));
        let failed =
          internal_failed_result
            (if resp.CT.status = CT.DecodeError
             then CPI.DecodeError
             else CPI.IllegalTransition);
        fold (client_internal_frame_post
          frame
          failed
          (Ghost.reveal old_out)
          (Ghost.reveal old_out)
          (Ghost.reveal st0)
          (Ghost.reveal st0)
          ([] <: list CW.wire_message)
          ([] <: list EAPI.local_output));
        fold (client_invariant
          cc
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0));
        failed
      }
    }
  }
}

noextract
let client_protocol_implementation
  : CPI.protocol_implementation
    canonical_client
    CS.connection_state
    CW.wire_message
    CTypes.client_local_event
    EAPI.local_output
  =
  {
    CPI.pi_system =
    (fun cc ->
      client_system
        #CTypes.client_local_event
        (Ghost.reveal cc.canonical_client_initial));
    CPI.pi_internal = client_is_internal;
    CPI.pi_internal_pending = client_internal_pending;
    CPI.pi_invariant = client_invariant;
    CPI.pi_snapshot = client_snapshot;
    CPI.pi_network_frame = tls_client_network_bridge_frame;
    CPI.pi_network_frame_pre = client_network_bridge_frame_pre;
    CPI.pi_network_frame_post = client_network_bridge_frame_post;
    CPI.pi_local_frame = tls_client_local_frame;
    CPI.pi_local_frame_pre = client_local_frame_pre;
    CPI.pi_local_frame_post = client_local_frame_post;
    CPI.pi_internal_frame_pre = client_internal_frame_pre;
    CPI.pi_internal_frame_post = client_internal_frame_post;
    CPI.pi_invariant_valid = client_invariant_valid;
    CPI.pi_take_snapshot = take_client_snapshot;
    CPI.pi_recall_snapshot = recall_client_snapshot_for_protocol;
    CPI.pi_process_network = client_process_network;
    CPI.pi_process_local = client_process_local;
    CPI.pi_process_internal = client_process_internal;
  }
