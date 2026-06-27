module Common.WireFormatStateMachine

module L = FStar.List.Tot
module Seq = FStar.Seq
module SM = Common.StateMachine
module TCP = Common.TCP
module WF = Common.WireFormat

noextract
class wire_format_state_machine
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  =
{
  wfsm_state_machine:
    SM.state_machine state wire_message local_event;

  wfsm_wire_format:
    WF.wire_format wire_message;
}

let event_input_messages
  (#wire_message:Type0)
  (#local_event:Type0)
  (ev:SM.event wire_message local_event)
  : list wire_message =
  match ev with
  | SM.WireEvent msg -> [msg]
  | SM.LocalEvent _ -> []

let rec trace_input_messages
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (trace:list (SM.transition state wire_message local_event))
  : Tot (list wire_message)
        (decreases trace)
=
  match trace with
  | [] -> []
  | tr :: rest ->
    L.append (event_input_messages tr.SM.tr_event) (trace_input_messages rest)

let valid_byte_trace
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (system:wire_format_state_machine state wire_message local_event)
  (input_bytes:TCP.bytes)
  (st1:state)
  (output_bytes:TCP.bytes)
  (residual_input:TCP.bytes)
  : GTot prop =
  exists trace.
    SM.trace_reaches
      system.wfsm_state_machine
      system.wfsm_state_machine.SM.sm_initial_state
      trace
      st1 /\
    WF.parses_as
      system.wfsm_wire_format
      input_bytes
      (trace_input_messages trace)
      residual_input /\
    Seq.equal
      output_bytes
      (WF.serialize_all
        system.wfsm_wire_format
        (SM.trace_outputs trace))

let lemma_serialized_trace_inputs_refine_bytes
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (system:wire_format_state_machine state wire_message local_event)
  (laws:WF.wire_format_stream_laws wire_message system.wfsm_wire_format)
  (st0:state)
  (trace:list (SM.transition state wire_message local_event))
  (st1:state)
  (residual_input:TCP.bytes)
  : Lemma
      (requires
        SM.trace_reaches system.wfsm_state_machine st0 trace st1)
      (ensures
        st0 == system.wfsm_state_machine.SM.sm_initial_state ==>
        valid_byte_trace
          system
          (WF.serialize_with_tail
            system.wfsm_wire_format
            (trace_input_messages trace)
            residual_input)
          st1
          (WF.serialize_all
            system.wfsm_wire_format
            (SM.trace_outputs trace))
          residual_input)
=
  WF.lemma_parse_serialize_with_tail_inverse
    system.wfsm_wire_format
    laws
    (trace_input_messages trace)
    residual_input;
  assert (WF.parses_as
    system.wfsm_wire_format
    (WF.serialize_with_tail
      system.wfsm_wire_format
      (trace_input_messages trace)
      residual_input)
    (trace_input_messages trace)
    residual_input);
  assert (Seq.equal
    (WF.serialize_all
      system.wfsm_wire_format
      (SM.trace_outputs trace))
    (WF.serialize_all
      system.wfsm_wire_format
    (SM.trace_outputs trace)));
  if st0 == system.wfsm_state_machine.SM.sm_initial_state then
    assert (exists trace'.
    SM.trace_reaches
      system.wfsm_state_machine
      system.wfsm_state_machine.SM.sm_initial_state
      trace'
      st1 /\
    WF.parses_as
      system.wfsm_wire_format
      (WF.serialize_with_tail
        system.wfsm_wire_format
        (trace_input_messages trace)
        residual_input)
      (trace_input_messages trace')
      residual_input /\
    Seq.equal
      (WF.serialize_all
        system.wfsm_wire_format
        (SM.trace_outputs trace))
      (WF.serialize_all
        system.wfsm_wire_format
        (SM.trace_outputs trace')))
