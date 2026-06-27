module Common.ProtocolImplementation

#lang-pulse

open Pulse.Lib.Pervasives

module Seq = FStar.Seq
module SM = Common.StateMachine
module SZ = FStar.SizeT
module TCP = Common.TCP
module U8 = FStar.UInt8
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine

type process_status =
  | StepOk
  | NeedMoreInput
  | ParseFailed
  | DecodeError
  | IllegalTransition
  | OutputBufferTooSmall
  | ConnectionFailed

noeq
type process_result = {
  process_status: process_status;
  process_consumed_len: SZ.t;
  process_produced_len: SZ.t;
  process_app_len: SZ.t;
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

let no_progress_status (status:process_status) : bool =
  match status with
  | NeedMoreInput
  | ParseFailed -> true
  | _ -> false

let non_step_status (status:process_status) : bool =
  match status with
  | DecodeError
  | IllegalTransition
  | OutputBufferTooSmall
  | ConnectionFailed -> true
  | _ -> false

let state_ahead
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (st0:state)
  (st1:state)
  : prop =
  exists trace.
    SM.trace_reaches system.WFSM.wfsm_state_machine st0 trace st1

let step_output
  (#wire_message:Type0)
  (#local_output:Type0)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : SM.step_output wire_message local_output =
  {
    SM.so_wire_outputs = wire_outputs;
    SM.so_local_outputs = local_outputs;
  }

let network_process_correct
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (input:TCP.bytes)
  (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:process_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (consumed:TCP.bytes)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : prop =
  buffers_wf input input_len old_out out_len /\
  Seq.length out_bytes == Seq.length old_out /\
  (match result.process_status with
  | StepOk ->
    exists msg residual produced.
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
        (step_output wire_outputs local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
      output_written out_bytes result.process_produced_len produced /\
      Seq.equal received1 (Seq.append received0 consumed) /\
      Seq.equal sent1 (Seq.append sent0 produced)
  | NeedMoreInput ->
    system.WFSM.wfsm_wire_format.WF.wf_parse (input_bytes input input_len) == None /\
    Seq.equal consumed Seq.empty /\
    wire_outputs == [] /\
    local_outputs == [] /\
    result.process_consumed_len == 0sz /\
    result.process_produced_len == 0sz /\
    same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
    Seq.equal out_bytes old_out
  | ParseFailed ->
    system.WFSM.wfsm_wire_format.WF.wf_parse (input_bytes input input_len) == None /\
    Seq.equal consumed Seq.empty /\
    wire_outputs == [] /\
    local_outputs == [] /\
    result.process_consumed_len == 0sz /\
    result.process_produced_len == 0sz /\
    same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
    Seq.equal out_bytes old_out
  | OutputBufferTooSmall ->
    exists msg parsed_consumed residual produced st_candidate.
      consumed_by_parse
        system.WFSM.wfsm_wire_format
        (input_bytes input input_len)
        msg
        parsed_consumed
        residual /\
      system.WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.WireEvent msg)
        st_candidate
        (step_output wire_outputs local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
      SZ.v out_len < Seq.length produced /\
      Seq.equal consumed Seq.empty /\
      result.process_consumed_len == 0sz /\
      result.process_produced_len == 0sz /\
      same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
      Seq.equal out_bytes old_out
  | DecodeError
  | IllegalTransition
  | ConnectionFailed ->
    exists produced.
      SZ.v result.process_consumed_len == Seq.length consumed /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
      output_written out_bytes result.process_produced_len produced /\
      Seq.equal received1 (Seq.append received0 consumed) /\
      Seq.equal sent1 (Seq.append sent0 produced))

let local_process_correct
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (ev:local_event)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:process_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : prop =
  SZ.v out_len == Seq.length old_out /\
  Seq.length out_bytes == Seq.length old_out /\
  result.process_consumed_len == 0sz /\
  (match result.process_status with
  | StepOk ->
    exists produced.
      system.WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.LocalEvent ev)
        st1
        (step_output wire_outputs local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
      output_written out_bytes result.process_produced_len produced /\
      Seq.equal received1 received0 /\
      Seq.equal sent1 (Seq.append sent0 produced)
  | NeedMoreInput ->
    False
  | ParseFailed ->
    False
  | OutputBufferTooSmall ->
    exists produced st_candidate.
      system.WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.LocalEvent ev)
        st_candidate
        (step_output wire_outputs local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
      SZ.v out_len < Seq.length produced /\
      result.process_produced_len == 0sz /\
      same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
      Seq.equal out_bytes old_out
  | DecodeError
  | IllegalTransition
  | ConnectionFailed ->
    exists produced.
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
      output_written out_bytes result.process_produced_len produced /\
      Seq.equal received1 received0 /\
      Seq.equal sent1 (Seq.append sent0 produced))

let lemma_network_process_ok_refines_transition
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (input:TCP.bytes)
  (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:process_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (consumed:TCP.bytes)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : Lemma
      (requires
        network_process_correct
          system
          input
          input_len
          old_out
          out_bytes
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
          local_outputs /\
        result.process_status == StepOk)
      (ensures
        exists msg residual produced.
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
            (step_output wire_outputs local_outputs) /\
          Seq.equal
            produced
            (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
          output_written out_bytes result.process_produced_len produced /\
          Seq.equal received1 (Seq.append received0 consumed) /\
          Seq.equal sent1 (Seq.append sent0 produced))
=
  ()

let lemma_local_process_ok_refines_transition
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (ev:local_event)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:process_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : Lemma
      (requires
        local_process_correct
          system
          ev
          old_out
          out_bytes
          out_len
          received0
          sent0
          st0
          result
          received1
          sent1
          st1
          wire_outputs
          local_outputs /\
        result.process_status == StepOk)
      (ensures
        exists produced.
          system.WFSM.wfsm_state_machine.SM.sm_step
            st0
            (SM.LocalEvent ev)
            st1
            (step_output wire_outputs local_outputs) /\
          Seq.equal
            produced
            (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
          output_written out_bytes result.process_produced_len produced /\
          Seq.equal received1 received0 /\
          Seq.equal sent1 (Seq.append sent0 produced))
=
  ()

noextract
class protocol_implementation
  (impl:Type0)
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  (local_output:Type0)
  =
{
  pi_system:
    impl ->
      GTot (WFSM.wire_format_state_machine state wire_message local_event local_output);

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

  pi_network_frame:
    Type0;

  pi_network_frame_pre:
    pi_network_frame ->
    array U8.t ->
    SZ.t ->
    array U8.t ->
    SZ.t ->
    TCP.bytes ->
    TCP.bytes ->
    slprop;

  pi_network_frame_post:
    pi_network_frame ->
    process_result ->
    TCP.bytes ->
    SZ.t ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    state ->
    TCP.bytes ->
    list wire_message ->
    list local_output ->
    slprop;

  pi_local_frame:
    Type0;

  pi_local_frame_pre:
    local_event ->
    pi_local_frame ->
    state ->
    array U8.t ->
    SZ.t ->
    TCP.bytes ->
    slprop;

  pi_local_frame_post:
    local_event ->
    pi_local_frame ->
    process_result ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    state ->
    list wire_message ->
    list local_output ->
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
              (pi_system i)
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
              (pi_system i)
              (Ghost.reveal snapshot_state)
              (Ghost.reveal current_state)));

  pi_process_network:
    i:impl ->
    frame:pi_network_frame ->
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
          pi_network_frame_pre
            frame
            input
            input_len
            out
            out_len
            (Ghost.reveal input_contents)
            (Ghost.reveal old_out) **
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
                  (out_contents:TCP.bytes)
                  (consumed:TCP.bytes)
                  (wire_outputs:list wire_message)
                  (local_outputs:list local_output).
            pi_invariant
              i
              (Ghost.reveal received1)
              (Ghost.reveal sent1)
              (Ghost.reveal st1) **
            pi_network_frame_post
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
              network_process_correct
                (pi_system i)
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
                local_outputs));

  pi_process_local:
    i:impl ->
    ev:local_event ->
    frame:pi_local_frame ->
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
         pi_local_frame_pre
           ev
           frame
           (Ghost.reveal st0)
           out
           out_len
           (Ghost.reveal old_out) **
         pts_to out (Ghost.reveal old_out) **
         pure (SZ.v out_len == Seq.length (Ghost.reveal old_out)))
        (fun result ->
          exists* (received1:Ghost.erased TCP.bytes)
                  (sent1:Ghost.erased TCP.bytes)
                  (st1:Ghost.erased state)
                  (out_contents:TCP.bytes)
                  (wire_outputs:list wire_message)
                  (local_outputs:list local_output).
            pi_invariant
              i
              (Ghost.reveal received1)
              (Ghost.reveal sent1)
              (Ghost.reveal st1) **
            pi_local_frame_post
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
              local_process_correct
                (pi_system i)
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
                local_outputs));
}
