module NSL.Sample.Protocol

(** NSL instantiation of the generic hostile-system construction. *)

module G = Common.Protocol.System

open NSL.Sample.Types
open NSL.Sample.Wire
open NSL.Sample.StateMachine

noextract
let configuration
  (initiator responder:principal)
  : G.configuration
      endpoint_state message local_event local_output
      fresh_value semantic_event rule_case
  =
  {
    G.endpoints = endpoint_semantics initiator responder;
    G.public_message = (fun _ -> True);
  }

type protocol_state =
  G.system_state endpoint_state message fresh_value semantic_event

type protocol_action =
  G.action message local_event

type protocol_label =
  G.step_label message fresh_value semantic_event rule_case

type protocol_transition =
  G.transition
    endpoint_state message local_event local_output
    fresh_value semantic_event rule_case

let initial
  (initiator responder:principal)
  : protocol_state
  =
  G.initial (configuration initiator responder)

let step
  (initiator responder:principal)
  (state0:protocol_state)
  (action:protocol_action)
  (label:protocol_label)
  (state1:protocol_state)
  (output:output)
  : GTot prop
  =
  G.step
    (configuration initiator responder)
    state0 action label state1 output

let erased_step
  (initiator responder:principal)
  (state0:protocol_state)
  (action:protocol_action)
  (state1:protocol_state)
  (output:output)
  : GTot prop
  =
  G.erased_step
    (configuration initiator responder)
    state0 action state1 output

let trace_reaches
  (initiator responder:principal)
  (state0:protocol_state)
  (trace:list protocol_transition)
  (state1:protocol_state)
  : GTot prop
  =
  G.trace_reaches
    (configuration initiator responder)
    state0 trace state1
