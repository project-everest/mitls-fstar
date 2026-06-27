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
module MR = Pulse.Lib.MonotonicGhostRef
module Pre = FStar.Preorder
module Seq = FStar.Seq
module SM = Common.StateMachine
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine

(**
  Canonical Common.ProtocolImplementation boundary for the low-level client.

  This file currently contains the auditable state-machine/invariant/snapshot
  boundary and status/result adapters.  The actual [CPI.protocol_implementation]
  record is intentionally not constructed here yet: bridging the existing
  [CT.network_bytes_end_to_end_correct] predicate to the stricter
  [CPI.network_process_correct] shape needs the lemmas listed in the final
  report (notably raw-record output decomposition and parser-failure facts).
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
    (match local with
    | CTypes.ClientAPI api ->
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
    | CTypes.ClientGhostStep ->
      exists delta.
        CS.legal_connection_delta st0 delta st1 /\
        client_wire_outputs_match
          delta.CS.delta_raw_sent
          out.SM.so_wire_outputs /\
        client_local_outputs_match
          delta.CS.delta_event
          out.SM.so_local_outputs)

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

noeq
type canonical_client = {
  canonical_client_state: C.client;
  canonical_client_initial: Ghost.erased CS.connection_state;
}

let client_state_ahead
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : prop =
  CPI.state_ahead (client_system initial) st0 st1

[@@pulse_unfold]
let client_invariant
  (cc:canonical_client)
  (received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  : slprop =
  C.connection_exactly cc.canonical_client_state st **
  pure (
    CT.client_end_to_end_invariant st /\
    st.CS.cs_model.CS.model_config ==
      (Ghost.reveal cc.canonical_client_initial).CS.cs_model.CS.model_config /\
    Seq.equal received st.CS.cs_wire_log.CL.raw_received /\
    Seq.equal sent st.CS.cs_wire_log.CL.raw_sent)

[@@pulse_unfold]
let client_snapshot
  (cc:canonical_client)
  (_received:B.bytes)
  (_sent:B.bytes)
  (st:CS.connection_state)
  : slprop =
  MR.snapshot (C.client_state_ref cc.canonical_client_state) st

ghost
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
  unfold (C.connection_exactly
    cc.canonical_client_state
    (Ghost.reveal st));
  MR.take_snapshot
    (C.client_state_ref cc.canonical_client_state)
    (Ghost.reveal st);
  fold (C.connection_exactly
    cc.canonical_client_state
    (Ghost.reveal st));
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

ghost
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
  pure (CS.connection_state_evolves
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
  unfold (C.connection_exactly
    cc.canonical_client_state
    (Ghost.reveal current_state));
  MR.recall_snapshot
    (C.client_state_ref cc.canonical_client_state);
  fold (C.connection_exactly
    cc.canonical_client_state
    (Ghost.reveal current_state));
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
