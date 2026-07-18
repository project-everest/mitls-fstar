module TLS13.Spec.StateMachine.Reachability

(**
  Auxiliary: reachability closure over the core legal-delta relation
  (single-step relation, its reflexive-transitive closure, and the top-level
  connection_state_consistent reachability invariant). Builds only on
  TLS13.Spec.StateMachine.
**)

module RTC = FStar.ReflexiveTransitiveClosure

open FStar.List.Tot

open TLS13.Spec.StateMachine

(* Multi-step model evolution helpers: fold the core single-step [step_model]
   and [legal_event] relations over event lists.  These live in the reachability
   layer (rather than the core) because they are only used to state multi-step /
   replay / reachability consistency, not by the core state/step/legal roots. *)
let rec step_model_many
  (model:connection_model)
  (events:list conn_event)
  : GTot (option connection_model)
        (decreases events)
  =
  match events with
  | [] -> Some model
  | ev :: rest ->
    (match step_model model ev with
     | Some model' -> step_model_many model' rest
     | None -> None)
let model_after_events (cfg:connection_config) (events:list conn_event)
  : GTot (option connection_model) =
  step_model_many (initial_model cfg) events
let rec model_events_legal
  (model:connection_model)
  (events:list conn_event)
  (final:connection_model)
  : GTot prop
        (decreases events)
  =
  match events with
  | [] -> final == model
  | ev :: rest ->
    legal_event model ev /\
    (match step_model model ev with
     | Some model' -> model_events_legal model' rest final
     | None -> False)

let connection_state_single_step : RTC.binrel connection_state =
  fun st0 st1 -> exists delta. legal_connection_delta st0 delta st1
let connection_state_evolves : RTC.preorder connection_state =
  RTC.closure connection_state_single_step
let connection_state_consistent (st:connection_state) : GTot prop =
  connection_state_evolves (initial st.cs_model.model_config) st
