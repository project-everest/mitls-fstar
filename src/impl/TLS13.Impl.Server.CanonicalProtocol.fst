module TLS13.Impl.Server.CanonicalProtocol

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CPI = Common.ProtocolImplementation
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.ConnectionState
module CW = TLS13.Impl.CanonicalWire
module CTypes = TLS13.Impl.CanonicalTypes
module MR = Pulse.Lib.MonotonicGhostRef
module S = TLS13.Impl.Server
module Seq = FStar.Seq
module SM = Common.StateMachine
module ST = TLS13.Impl.Server.Types
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine

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
        CS.legal_connection_delta st0 delta st1 /\
        server_wire_outputs_match
          delta.CS.delta_raw_sent
          out.SM.so_wire_outputs /\
        server_local_outputs_match
          delta.CS.delta_event
          out.SM.so_local_outputs)

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
}

let server_state_ahead
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : prop =
  CPI.state_ahead (server_system initial) st0 st1

[@@pulse_unfold]
let server_invariant
  (srv:canonical_server)
  (received:B.bytes)
  (sent:B.bytes)
  (st:CS.connection_state)
  : slprop =
  S.connection_exactly srv.canonical_server_state st **
  pure (
    ST.server_end_to_end_invariant st /\
    st.CS.cs_model.CS.model_config ==
      (Ghost.reveal srv.canonical_server_initial).CS.cs_model.CS.model_config /\
    Seq.equal received st.CS.cs_wire_log.CL.raw_received /\
    Seq.equal sent st.CS.cs_wire_log.CL.raw_sent)

[@@pulse_unfold]
let server_snapshot
  (srv:canonical_server)
  (_received:B.bytes)
  (_sent:B.bytes)
  (st:CS.connection_state)
  : slprop =
  MR.snapshot (S.server_state_ref srv.canonical_server_state) st

ghost
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

ghost
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
  pure (CS.connection_state_evolves
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
