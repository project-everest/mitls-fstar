module Common.Protocol.Interpretation

(**
  Generic interpretation of a canonical protocol history.

  [Common.Protocol.System] already records every delivery, fresh value, semantic
  protocol effect, send, injection, and compromise.  A symbolic backend therefore
  interprets that history directly; it does not define a second product state
  machine or prove a protocol-specific execution lifting theorem.
*)

module E = Common.Protocol.Labelled
module S = Common.Protocol.System
module L = FStar.List.Tot

noextract
class interpreter
  (message:Type0)
  (fresh:Type0)
  (semantic_event:Type0)
  (model:Type0)
  =
{
  initial_model:
    model;

  generated:
    model ->
    E.endpoint_id ->
    fresh ->
    Tot model;

  received:
    model ->
    E.endpoint_id ->
    nat ->
    message ->
    Tot model;

  protocol_effect:
    model ->
    E.endpoint_id ->
    semantic_event ->
    Tot model;

  sent:
    model ->
    E.endpoint_id ->
    nat ->
    message ->
    Tot model;

  injected:
    model ->
    nat ->
    message ->
    Tot model;

  compromised:
    model ->
    E.endpoint_id ->
    Tot model;
}

let interpret_one
  (#message:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#model:Type0)
  (backend:interpreter message fresh semantic_event model)
  (state:model)
  (event:S.system_effect message fresh semantic_event)
  : model
  =
  match event with
  | S.Generated owner value ->
    backend.generated state owner value
  | S.ObservedReceive receiver index payload ->
    backend.received state receiver index payload
  | S.ProtocolEffect owner semantic ->
    backend.protocol_effect state owner semantic
  | S.ObservedSend sender index payload ->
    backend.sent state sender index payload
  | S.AttackerInjected index payload ->
    backend.injected state index payload
  | S.Compromised endpoint ->
    backend.compromised state endpoint

let rec interpret_from
  (#message:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#model:Type0)
  (backend:interpreter message fresh semantic_event model)
  (state:model)
  (history:list (S.system_effect message fresh semantic_event))
  : Tot model
      (decreases history)
  =
  match history with
  | [] ->
    state
  | event :: rest ->
    interpret_from backend (interpret_one backend state event) rest

let interpret_history
  (#message:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#model:Type0)
  (backend:interpreter message fresh semantic_event model)
  (history:list (S.system_effect message fresh semantic_event))
  : model
  =
  interpret_from backend backend.initial_model history

let symbolic_view
  (#endpoint_state:Type0)
  (#message:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#model:Type0)
  (backend:interpreter message fresh semantic_event model)
  (concrete:S.system_state endpoint_state message fresh semantic_event)
  : model
  =
  interpret_history backend concrete.S.history

(**
  Optional invariant package for symbolic backends.  Preservation is proved once
  over the generic history fold; a protocol backend supplies only its one-effect
  preservation argument.
*)
noextract
class verified_interpreter
  (message:Type0)
  (fresh:Type0)
  (semantic_event:Type0)
  (model:Type0)
  (backend:interpreter message fresh semantic_event model)
  =
{
  model_invariant:
    model ->
    GTot prop;

  initial_valid:
    unit ->
    Lemma
      (ensures
        model_invariant backend.initial_model);

  effect_preserves:
    state:model ->
    event:S.system_effect message fresh semantic_event ->
    Lemma
      (requires
        model_invariant state)
      (ensures
        model_invariant (interpret_one backend state event));
}

(** Incremental interpretation follows directly from append. *)
let rec lemma_interpret_append
  (#message:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#model:Type0)
  (backend:interpreter message fresh semantic_event model)
  (state:model)
  (prefix suffix:list (S.system_effect message fresh semantic_event))
  : Lemma
      (ensures
        interpret_from backend state (L.append prefix suffix) ==
        interpret_from backend
          (interpret_from backend state prefix)
          suffix)
      (decreases prefix)
  =
  match prefix with
  | [] ->
    ()
  | event :: rest ->
    lemma_interpret_append backend
      (interpret_one backend state event)
      rest
      suffix

let rec lemma_interpret_from_preserves
  (#message:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#model:Type0)
  (backend:interpreter message fresh semantic_event model)
  (verified:
    verified_interpreter message fresh semantic_event model backend)
  (state:model)
  (history:list (S.system_effect message fresh semantic_event))
  : Lemma
      (requires
        verified.model_invariant state)
      (ensures
        verified.model_invariant
          (interpret_from backend state history))
      (decreases history)
  =
  match history with
  | [] ->
    ()
  | event :: rest ->
    verified.effect_preserves state event;
    lemma_interpret_from_preserves backend verified
      (interpret_one backend state event)
      rest

let lemma_interpret_history_valid
  (#message:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#model:Type0)
  (backend:interpreter message fresh semantic_event model)
  (verified:
    verified_interpreter message fresh semantic_event model backend)
  (history:list (S.system_effect message fresh semantic_event))
  : Lemma
      (ensures
        verified.model_invariant
          (interpret_history backend history))
  =
  verified.initial_valid ();
  lemma_interpret_from_preserves backend verified
    backend.initial_model
    history
