module Common.Protocol.System

(**
  Generic finite-endpoint hostile execution environment.

  This module owns all protocol-independent machinery:

    * append-only delivery and replay;
    * public-message injection;
    * global no-reuse accounting for fresh values;
    * monotone dynamic compromise;
    * honest packet provenance and packet positions; and
    * a canonical effect history.

  Protocol code supplies only intrinsically labelled endpoint rules.  This
  composer never matches a protocol message, state, phase, or rule constructor.
*)

module L = FStar.List.Tot
module SM = Common.StateMachine
module E = Common.Protocol.Labelled

type packet_origin =
  | Honest:
      sender:E.endpoint_id ->
      packet_origin
  | Attacker:
      packet_origin

noeq
type packet
  (message:Type0)
  =
{
  packet_message:
    message;
  packet_origin:
    packet_origin;
}

noeq
type system_effect
  (message:Type0)
  (fresh:Type0)
  (semantic_event:Type0)
  =
  | Generated:
      owner:E.endpoint_id ->
      value:fresh ->
      system_effect message fresh semantic_event
  | ObservedReceive:
      receiver:E.endpoint_id ->
      packet_index:nat ->
      payload:message ->
      system_effect message fresh semantic_event
  | ProtocolEffect:
      owner:E.endpoint_id ->
      event:semantic_event ->
      system_effect message fresh semantic_event
  | ObservedSend:
      sender:E.endpoint_id ->
      packet_index:nat ->
      payload:message ->
      system_effect message fresh semantic_event
  | AttackerInjected:
      packet_index:nat ->
      payload:message ->
      system_effect message fresh semantic_event
  | Compromised:
      endpoint:E.endpoint_id ->
      system_effect message fresh semantic_event

noeq
type system_state
  (endpoint_state:Type0)
  (message:Type0)
  (fresh:Type0)
  (semantic_event:Type0)
  =
{
  endpoint_states:
    list endpoint_state;
  network:
    list (packet message);
  generated:
    list fresh;
  compromised:
    list E.endpoint_id;
  history:
    list (system_effect message fresh semantic_event);
}

noeq
type action
  (message:Type0)
  (local_event:Type0)
  =
  | Run:
      endpoint:E.endpoint_id ->
      event:local_event ->
      action message local_event
  | Deliver:
      packet_index:nat ->
      endpoint:E.endpoint_id ->
      action message local_event
  | Inject:
      injected_message:message ->
      action message local_event
  | Corrupt:
      endpoint:E.endpoint_id ->
      action message local_event

noeq
type step_label
  (message:Type0)
  (fresh:Type0)
  (semantic_event:Type0)
  (rule_data:Type0)
  =
  | EndpointRule:
      witness:E.labelled_rule rule_data message fresh semantic_event ->
      step_label message fresh semantic_event rule_data
  | InjectionStep:
      step_label message fresh semantic_event rule_data
  | CorruptionStep:
      step_label message fresh semantic_event rule_data

let rec fresh_not_in
  (#fresh:Type0)
  (value:fresh)
  (values:list fresh)
  : Tot prop
      (decreases values)
  =
  match values with
  | [] ->
    True
  | head :: tail ->
    value =!= head /\ fresh_not_in value tail

let rec fresh_batch
  (#fresh:Type0)
  (new_values:list fresh)
  (old_values:list fresh)
  : Tot prop
      (decreases new_values)
  =
  match new_values with
  | [] ->
    True
  | head :: tail ->
    fresh_not_in head old_values /\
    fresh_not_in head tail /\
    fresh_batch tail old_values

let empty_output
  (#message:Type0)
  (#local_output:Type0)
  : SM.step_output message local_output
  =
  {
    SM.so_wire_outputs = [];
    SM.so_local_outputs = [];
  }

let rec honest_packets
  (#message:Type0)
  (sender:E.endpoint_id)
  (messages:list message)
  : Tot (list (packet message))
      (decreases messages)
  =
  match messages with
  | [] ->
    []
  | message :: rest ->
    {
      packet_message = message;
      packet_origin = Honest sender;
    } :: honest_packets sender rest

let append_honest
  (#message:Type0)
  (network:list (packet message))
  (sender:E.endpoint_id)
  (messages:list message)
  : list (packet message)
  =
  L.append network (honest_packets sender messages)

let rec story_effects
  (#message:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (owner:E.endpoint_id)
  (next_packet_index:nat)
  (story:E.rule_story message fresh semantic_event)
  : Tot (list (system_effect message fresh semantic_event))
      (decreases story)
  =
  match story with
  | [] ->
    []
  | E.StoryFresh value :: rest ->
    Generated owner value ::
    story_effects owner next_packet_index rest
  | E.StorySemantic event :: rest ->
    ProtocolEffect owner event ::
    story_effects owner next_packet_index rest
  | E.StorySend payload :: rest ->
    ObservedSend owner next_packet_index payload ::
    story_effects owner (next_packet_index + 1) rest

let receive_effects
  (#message:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#local_event:Type0)
  (receiver:E.endpoint_id)
  (event:E.trigger message local_event)
  : list (system_effect message fresh semantic_event)
  =
  match event with
  | E.TriggerLocal _ ->
    []
  | E.TriggerReceive index message ->
    [ ObservedReceive receiver index message ]

let endpoint_effects
  (#message:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#local_event:Type0)
  (owner:E.endpoint_id)
  (event:E.trigger message local_event)
  (story:E.rule_story message fresh semantic_event)
  (network_length:nat)
  : list (system_effect message fresh semantic_event)
  =
  L.append
    (receive_effects owner event)
    (story_effects owner network_length story)

noextract
class configuration
  (endpoint_state:Type0)
  (message:Type0)
  (local_event:Type0)
  (local_output:Type0)
  (fresh:Type0)
  (semantic_event:Type0)
  (rule_data:Type0)
  =
{
  endpoints:
    E.endpoint_semantics
      endpoint_state message local_event local_output fresh semantic_event rule_data;
  public_message:
    message ->
    GTot prop;
}

let initial
  (#endpoint_state:Type0)
  (#message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#rule_data:Type0)
  (config:
    configuration
      endpoint_state message local_event local_output fresh semantic_event rule_data)
  : system_state endpoint_state message fresh semantic_event
  =
  {
    endpoint_states = config.endpoints.E.initial_states;
    network = [];
    generated = [];
    compromised = [];
    history = [];
  }

let rec update_at
  (#endpoint_state:Type0)
  (states:list endpoint_state)
  (index:nat)
  (value:endpoint_state)
  : Tot (list endpoint_state)
      (decreases states)
  =
  match states with
  | [] ->
    []
  | head :: tail ->
    if index = 0
    then value :: tail
    else head :: update_at tail (index - 1) value

let endpoint_successor
  (#endpoint_state:Type0)
  (#message:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (state0:system_state endpoint_state message fresh semantic_event)
  (who:E.endpoint_id)
  (next_endpoint:endpoint_state)
  (next_network:list (packet message))
  (next_generated:list fresh)
  (next_history:list (system_effect message fresh semantic_event))
  : system_state endpoint_state message fresh semantic_event
  =
  {
    state0 with
      endpoint_states = update_at state0.endpoint_states who next_endpoint;
      network = next_network;
      generated = next_generated;
      history = next_history;
  }

let endpoint_step
  (#endpoint_state:Type0)
  (#message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#rule_data:Type0)
  (config:
    configuration
      endpoint_state message local_event local_output fresh semantic_event rule_data)
  (state0:system_state endpoint_state message fresh semantic_event)
  (who:E.endpoint_id)
  (event:E.trigger message local_event)
  (witness:E.labelled_rule rule_data message fresh semantic_event)
  (state1:system_state endpoint_state message fresh semantic_event)
  (output:SM.step_output message local_output)
  : GTot prop
  =
  let story = witness.E.rule_story in
  let fresh_values = E.story_fresh_values story in
  who < L.length state0.endpoint_states /\
  fresh_batch fresh_values state0.generated /\
  E.story_messages story == output.SM.so_wire_outputs /\
  (let local0 = L.index state0.endpoint_states who in
   exists next_endpoint.
     config.endpoints.E.step_rule who local0 event witness
       next_endpoint output /\
     state1 ==
       endpoint_successor
         state0
         who
         next_endpoint
         (append_honest state0.network who output.SM.so_wire_outputs)
         (L.append state0.generated fresh_values)
         (L.append
           state0.history
           (endpoint_effects
             who event story (L.length state0.network))))

let step
  (#endpoint_state:Type0)
  (#message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#rule_data:Type0)
  (config:
    configuration
      endpoint_state message local_event local_output fresh semantic_event rule_data)
  (state0:system_state endpoint_state message fresh semantic_event)
  (system_action:action message local_event)
  (label:step_label message fresh semantic_event rule_data)
  (state1:system_state endpoint_state message fresh semantic_event)
  (output:SM.step_output message local_output)
  : GTot prop
  =
  match system_action, label with
  | Run who local_event, EndpointRule witness ->
    endpoint_step config state0 who
      (E.TriggerLocal local_event) witness state1 output

  | Deliver index who, EndpointRule witness ->
    index < L.length state0.network /\
    (let message = (L.index state0.network index).packet_message in
     endpoint_step config state0 who
       (E.TriggerReceive index message) witness state1 output)

  | Inject message, InjectionStep ->
    config.public_message message /\
    output == empty_output /\
    state1 == {
      state0 with
        network =
          L.append state0.network [{
            packet_message = message;
            packet_origin = Attacker;
          }];
        history =
          L.append state0.history
            [ AttackerInjected (L.length state0.network) message ];
    }

  | Corrupt who, CorruptionStep ->
    who < L.length state0.endpoint_states /\
    fresh_not_in who state0.compromised /\
    output == empty_output /\
    state1 == {
      state0 with
        compromised = L.append state0.compromised [ who ];
        history = L.append state0.history [ Compromised who ];
    }

  | _, _ ->
    False

(** The unlabelled system is definitionally the erasure of its step label. *)
let erased_step
  (#endpoint_state:Type0)
  (#message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#rule_data:Type0)
  (config:
    configuration
      endpoint_state message local_event local_output fresh semantic_event rule_data)
  (state0:system_state endpoint_state message fresh semantic_event)
  (system_action:action message local_event)
  (state1:system_state endpoint_state message fresh semantic_event)
  (output:SM.step_output message local_output)
  : GTot prop
  =
  exists label.
    step config state0 system_action label state1 output

noeq
type transition
  (endpoint_state:Type0)
  (message:Type0)
  (local_event:Type0)
  (local_output:Type0)
  (fresh:Type0)
  (semantic_event:Type0)
  (rule_data:Type0)
  =
{
  transition_action:
    action message local_event;
  transition_rule:
    step_label message fresh semantic_event rule_data;
  transition_next:
    system_state endpoint_state message fresh semantic_event;
  transition_output:
    SM.step_output message local_output;
}

let rec trace_reaches
  (#endpoint_state:Type0)
  (#message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#rule_data:Type0)
  (config:
    configuration
      endpoint_state message local_event local_output fresh semantic_event rule_data)
  (state0:system_state endpoint_state message fresh semantic_event)
  (trace:
    list
      (transition
        endpoint_state message local_event local_output
        fresh semantic_event rule_data))
  (state1:system_state endpoint_state message fresh semantic_event)
  : GTot prop
      (decreases trace)
  =
  match trace with
  | [] ->
    state1 == state0
  | head :: tail ->
    step config state0
      head.transition_action
      head.transition_rule
      head.transition_next
      head.transition_output /\
    trace_reaches config head.transition_next tail state1

let lemma_step_erases
  (#endpoint_state:Type0)
  (#message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#rule_data:Type0)
  (config:
    configuration
      endpoint_state message local_event local_output fresh semantic_event rule_data)
  (state0:system_state endpoint_state message fresh semantic_event)
  (system_action:action message local_event)
  (label:step_label message fresh semantic_event rule_data)
  (state1:system_state endpoint_state message fresh semantic_event)
  (output:SM.step_output message local_output)
  : Lemma
      (requires
        step config state0 system_action label state1 output)
      (ensures
        erased_step config state0 system_action state1 output)
  =
  introduce exists label'.
    step config state0 system_action label' state1 output
  with label and ()
