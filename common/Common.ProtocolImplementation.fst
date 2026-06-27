module Common.ProtocolImplementation

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Seq = FStar.Seq
module SM = Common.StateMachine
module SZ = FStar.SizeT
module TCP = Common.TCP
module U8 = FStar.UInt8
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine

type process_status =
  | ProcessOk
  | ParseFailed
  | OutputTooSmall

noeq
type process_result = {
  process_status: process_status;
  process_consumed_len: SZ.t;
  process_produced_len: SZ.t;
}

let bounded_len
  (bytes:TCP.bytes)
  (len:SZ.t)
  : nat =
  if SZ.v len <= Seq.length bytes then SZ.v len else Seq.length bytes

let input_bytes
  (input:TCP.bytes)
  (input_len:SZ.t)
  : TCP.bytes =
  Seq.slice input 0 (bounded_len input input_len)

let output_prefix
  (out:TCP.bytes)
  (produced_len:SZ.t)
  : TCP.bytes =
  Seq.slice out 0 (bounded_len out produced_len)

let buffers_wf
  (input:TCP.bytes)
  (input_len:SZ.t)
  (out:TCP.bytes)
  (out_len:SZ.t)
  : prop =
  SZ.v input_len <= Seq.length input /\
  SZ.v out_len == Seq.length out

let consumed_by_parse
  (#wire_message:Type0)
  (fmt:WF.wire_format wire_message)
  (available:TCP.bytes)
  (msg:wire_message)
  (consumed:TCP.bytes)
  (residual:TCP.bytes)
  : prop =
  exists parsed_msg.
    fmt.WF.wf_parse available == Some (parsed_msg, residual) /\
    fmt.WF.wf_equal parsed_msg msg /\
  Seq.equal available (Seq.append consumed residual)

let output_written
  (out_bytes:TCP.bytes)
  (produced_len:SZ.t)
  (produced:TCP.bytes)
  : prop =
  SZ.v produced_len == Seq.length produced /\
  SZ.v produced_len <= Seq.length out_bytes /\
  Seq.equal (output_prefix out_bytes produced_len) produced

let same_abstract_state
  (#state:Type0)
  (received0 sent0 received1 sent1:TCP.bytes)
  (st0 st1:state)
  : prop =
  Seq.equal received1 received0 /\
  Seq.equal sent1 sent0 /\
  st1 == st0

let state_ahead
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event)
  (st0:state)
  (st1:state)
  : prop =
  exists trace.
    SM.trace_reaches system.WFSM.wfsm_state_machine st0 trace st1

let network_process_correct
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event)
  (input:TCP.bytes)
  (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:process_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  : prop =
  buffers_wf input input_len old_out out_len /\
  Seq.length out_bytes == Seq.length old_out /\
  (match result.process_status with
  | ProcessOk ->
    exists msg consumed residual outputs produced.
      consumed_by_parse
        system.WFSM.wfsm_wire_format
        (input_bytes input input_len)
        msg
        consumed
        residual /\
      SZ.v result.process_consumed_len == Seq.length consumed /\
      system.WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.WireEvent msg)
        st1
        outputs /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format outputs) /\
      output_written out_bytes result.process_produced_len produced /\
      Seq.equal received1 (Seq.append received0 consumed) /\
      Seq.equal sent1 (Seq.append sent0 produced)
  | ParseFailed ->
    system.WFSM.wfsm_wire_format.WF.wf_parse (input_bytes input input_len) == None /\
    result.process_consumed_len == 0sz /\
    result.process_produced_len == 0sz /\
    same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
    Seq.equal out_bytes old_out
  | OutputTooSmall ->
    exists msg consumed residual outputs produced st_candidate.
      consumed_by_parse
        system.WFSM.wfsm_wire_format
        (input_bytes input input_len)
        msg
        consumed
        residual /\
      system.WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.WireEvent msg)
        st_candidate
        outputs /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format outputs) /\
      SZ.v out_len < Seq.length produced /\
      result.process_consumed_len == 0sz /\
      result.process_produced_len == 0sz /\
      same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
      Seq.equal out_bytes old_out)

let local_process_correct
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event)
  (ev:local_event)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:process_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  : prop =
  SZ.v out_len == Seq.length old_out /\
  Seq.length out_bytes == Seq.length old_out /\
  result.process_consumed_len == 0sz /\
  (match result.process_status with
  | ProcessOk ->
    exists outputs produced.
      system.WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.LocalEvent ev)
        st1
        outputs /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format outputs) /\
      output_written out_bytes result.process_produced_len produced /\
      Seq.equal received1 received0 /\
      Seq.equal sent1 (Seq.append sent0 produced)
  | ParseFailed ->
    False
  | OutputTooSmall ->
    exists outputs produced st_candidate.
      system.WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.LocalEvent ev)
        st_candidate
        outputs /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format outputs) /\
      SZ.v out_len < Seq.length produced /\
      result.process_produced_len == 0sz /\
      same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
      Seq.equal out_bytes old_out)

noextract
class protocol_implementation
  (impl:Type0)
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  =
{
  pi_system:
    WFSM.wire_format_state_machine state wire_message local_event;

  pi_invariant:
    impl ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    slprop;

  pi_snapshot:
    impl ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    slprop;

  pi_invariant_valid:
    i:impl ->
    received:Ghost.erased TCP.bytes ->
    sent:Ghost.erased TCP.bytes ->
    st:Ghost.erased state ->
      stt unit
        (pi_invariant
          i
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st))
        (fun _ ->
          pi_invariant
            i
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st) **
          pure (
            WFSM.valid_byte_trace
              pi_system
              (Ghost.reveal received)
              (Ghost.reveal st)
              (Ghost.reveal sent)
              Seq.empty));

  pi_take_snapshot:
    i:impl ->
    received:Ghost.erased TCP.bytes ->
    sent:Ghost.erased TCP.bytes ->
    st:Ghost.erased state ->
      stt unit
        (pi_invariant
          i
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st))
        (fun _ ->
          pi_invariant
            i
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st) **
          pi_snapshot
            i
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st));

  pi_recall_snapshot:
    i:impl ->
    snapshot_received:Ghost.erased TCP.bytes ->
    snapshot_sent:Ghost.erased TCP.bytes ->
    snapshot_state:Ghost.erased state ->
    current_received:Ghost.erased TCP.bytes ->
    current_sent:Ghost.erased TCP.bytes ->
    current_state:Ghost.erased state ->
      stt unit
        (pi_snapshot
          i
          (Ghost.reveal snapshot_received)
          (Ghost.reveal snapshot_sent)
          (Ghost.reveal snapshot_state) **
         pi_invariant
          i
          (Ghost.reveal current_received)
          (Ghost.reveal current_sent)
          (Ghost.reveal current_state))
        (fun _ ->
          pi_snapshot
            i
            (Ghost.reveal snapshot_received)
            (Ghost.reveal snapshot_sent)
            (Ghost.reveal snapshot_state) **
          pi_invariant
            i
            (Ghost.reveal current_received)
            (Ghost.reveal current_sent)
            (Ghost.reveal current_state) **
          pure (
            state_ahead
              pi_system
              (Ghost.reveal snapshot_state)
              (Ghost.reveal current_state)));

  pi_process_network:
    i:impl ->
    input:array U8.t ->
    input_len:SZ.t ->
    out:array U8.t ->
    out_len:SZ.t ->
    received0:Ghost.erased TCP.bytes ->
    sent0:Ghost.erased TCP.bytes ->
    st0:Ghost.erased state ->
    input_contents:Ghost.erased TCP.bytes ->
    old_out:Ghost.erased TCP.bytes ->
      stt process_result
        (pi_invariant
          i
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0) **
         pts_to input (Ghost.reveal input_contents) **
         pts_to out (Ghost.reveal old_out) **
         pure (
          buffers_wf
            (Ghost.reveal input_contents)
            input_len
            (Ghost.reveal old_out)
            out_len))
        (fun result ->
          exists* (received1:Ghost.erased TCP.bytes)
                  (sent1:Ghost.erased TCP.bytes)
                  (st1:Ghost.erased state)
                  (out_contents:TCP.bytes).
            pi_invariant
              i
              (Ghost.reveal received1)
              (Ghost.reveal sent1)
              (Ghost.reveal st1) **
            pts_to input (Ghost.reveal input_contents) **
            pts_to out out_contents **
            pure (
              network_process_correct
                pi_system
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
                (Ghost.reveal st1)));

  pi_process_local:
    i:impl ->
    ev:local_event ->
    out:array U8.t ->
    out_len:SZ.t ->
    received0:Ghost.erased TCP.bytes ->
    sent0:Ghost.erased TCP.bytes ->
    st0:Ghost.erased state ->
    old_out:Ghost.erased TCP.bytes ->
      stt process_result
        (pi_invariant
          i
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0) **
         pts_to out (Ghost.reveal old_out) **
         pure (SZ.v out_len == Seq.length (Ghost.reveal old_out)))
        (fun result ->
          exists* (received1:Ghost.erased TCP.bytes)
                  (sent1:Ghost.erased TCP.bytes)
                  (st1:Ghost.erased state)
                  (out_contents:TCP.bytes).
            pi_invariant
              i
              (Ghost.reveal received1)
              (Ghost.reveal sent1)
              (Ghost.reveal st1) **
            pts_to out out_contents **
            pure (
              local_process_correct
                pi_system
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
                (Ghost.reveal st1)));
}
