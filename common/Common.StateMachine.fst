module Common.StateMachine

module ID = FStar.IndefiniteDescription
module L = FStar.List.Tot

type event (wire_message:Type0) (local_event:Type0) =
  | WireEvent: wire_message -> event wire_message local_event
  | LocalEvent: local_event -> event wire_message local_event

noextract
class state_machine
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  =
{
  sm_initial_state:
    state;

  sm_step:
    state ->
    event wire_message local_event ->
    state ->
    list wire_message ->
    GTot prop;
}

noeq
type transition
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  =
{
  tr_event: event wire_message local_event;
  tr_next_state: state;
  tr_outputs: list wire_message;
}

let rec trace_reaches
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (sm:state_machine state wire_message local_event)
  (st0:state)
  (trace:list (transition state wire_message local_event))
  (st1:state)
  : GTot prop
        (decreases trace)
=
  match trace with
  | [] ->
    st1 == st0
  | tr :: rest ->
    sm.sm_step st0 tr.tr_event tr.tr_next_state tr.tr_outputs /\
    trace_reaches sm tr.tr_next_state rest st1

let state_evolves
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (sm:state_machine state wire_message local_event)
  (st0:state)
  (st1:state)
  : GTot prop =
  exists trace. trace_reaches sm st0 trace st1

let valid_state
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (sm:state_machine state wire_message local_event)
  (st:state)
  : GTot prop =
  state_evolves sm sm.sm_initial_state st

let rec trace_events
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (trace:list (transition state wire_message local_event))
  : Tot (list (event wire_message local_event))
        (decreases trace)
=
  match trace with
  | [] -> []
  | tr :: rest -> tr.tr_event :: trace_events rest

let rec trace_outputs
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (trace:list (transition state wire_message local_event))
  : Tot (list wire_message)
        (decreases trace)
=
  match trace with
  | [] -> []
  | tr :: rest -> L.append tr.tr_outputs (trace_outputs rest)

let rec lemma_trace_reaches_append
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (sm:state_machine state wire_message local_event)
  (st0:state)
  (st1:state)
  (st2:state)
  (trace01:list (transition state wire_message local_event))
  (trace12:list (transition state wire_message local_event))
  : Lemma
      (requires
        trace_reaches sm st0 trace01 st1 /\
        trace_reaches sm st1 trace12 st2)
      (ensures
        trace_reaches sm st0 (L.append trace01 trace12) st2)
      (decreases trace01)
=
  match trace01 with
  | [] -> ()
  | tr :: rest ->
    lemma_trace_reaches_append
      sm
      tr.tr_next_state
      st1
      st2
      rest
      trace12

let lemma_state_evolves_refl
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (sm:state_machine state wire_message local_event)
  (st:state)
  : Lemma
      (ensures state_evolves sm st st)
=
  assert (trace_reaches sm st [] st)

let lemma_initial_state_valid
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (sm:state_machine state wire_message local_event)
  : Lemma
      (ensures valid_state sm sm.sm_initial_state)
=
  lemma_state_evolves_refl sm sm.sm_initial_state

let lemma_state_evolves_trans
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (sm:state_machine state wire_message local_event)
  (st0:state)
  (st1:state)
  (st2:state)
  : Lemma
      (requires
        state_evolves sm st0 st1 /\
        state_evolves sm st1 st2)
      (ensures state_evolves sm st0 st2)
=
  let trace01 =
    ID.indefinite_description_ghost
      (list (transition state wire_message local_event))
      (fun trace -> trace_reaches sm st0 trace st1) in
  let trace12 =
    ID.indefinite_description_ghost
      (list (transition state wire_message local_event))
      (fun trace -> trace_reaches sm st1 trace st2) in
  lemma_trace_reaches_append sm st0 st1 st2 trace01 trace12;
  assert (trace_reaches sm st0 (L.append trace01 trace12) st2)

let lemma_valid_state_after_step
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (sm:state_machine state wire_message local_event)
  (st0:state)
  (ev:event wire_message local_event)
  (st1:state)
  (outputs:list wire_message)
  : Lemma
      (requires
        valid_state sm st0 /\
        sm.sm_step st0 ev st1 outputs)
      (ensures valid_state sm st1)
=
  let trace0 =
    ID.indefinite_description_ghost
      (list (transition state wire_message local_event))
      (fun trace -> trace_reaches sm sm.sm_initial_state trace st0) in
  let step_trace = [{
    tr_event = ev;
    tr_next_state = st1;
    tr_outputs = outputs;
  }] in
  assert (trace_reaches sm st0 step_trace st1);
  lemma_trace_reaches_append sm sm.sm_initial_state st0 st1 trace0 step_trace;
  assert (trace_reaches sm sm.sm_initial_state (L.append trace0 step_trace) st1)
