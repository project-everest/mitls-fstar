module Common.Protocol.Labelled

(**
  Intrinsically labelled endpoint semantics.

  A protocol defines one [rule] type and one [step_rule] relation.  The ordinary,
  unlabelled relation is only existential erasure of that rule.  Consequently
  there is no separately maintained audit classifier and no completeness proof
  that has to rediscover which protocol transition occurred.

  Each rule also carries its fresh values and semantic effects.  The generic
  system composer uses this information directly; it never inspects protocol
  messages, control states, or rule constructors.
*)

module SM = Common.StateMachine

(** Endpoint instances are positions in a finite system-owned state vector. *)
type endpoint_id = nat

noeq
type trigger
  (message:Type0)
  (local_event:Type0)
  =
  | TriggerLocal:
      event:local_event ->
      trigger message local_event
  | TriggerReceive:
      packet_index:nat ->
      payload:message ->
      trigger message local_event

noeq
type story_item
  (message:Type0)
  (fresh:Type0)
  (semantic_event:Type0)
  =
  | StoryFresh:
      value:fresh ->
      story_item message fresh semantic_event
  | StorySemantic:
      event:semantic_event ->
      story_item message fresh semantic_event
  | StorySend:
      payload:message ->
      story_item message fresh semantic_event

type rule_story
  (message:Type0)
  (fresh:Type0)
  (semantic_event:Type0)
  =
  list (story_item message fresh semantic_event)

(**
  The story is structurally part of every rule witness.  A protocol may choose
  any [rule_data], but it cannot provide a witness without also providing the
  exact ordered fresh/semantic/send story consumed by the generic composer.
*)
noeq
type labelled_rule
  (rule_data:Type0)
  (message:Type0)
  (fresh:Type0)
  (semantic_event:Type0)
  =
{
  rule_payload:
    rule_data;
  rule_story:
    rule_story message fresh semantic_event;
}

let rec story_fresh_values
  (#message:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (story:rule_story message fresh semantic_event)
  : Tot (list fresh)
      (decreases story)
  =
  match story with
  | [] ->
    []
  | StoryFresh value :: rest ->
    value :: story_fresh_values rest
  | _ :: rest ->
    story_fresh_values rest

let rec story_messages
  (#message:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (story:rule_story message fresh semantic_event)
  : Tot (list message)
      (decreases story)
  =
  match story with
  | [] ->
    []
  | StorySend payload :: rest ->
    payload :: story_messages rest
  | _ :: rest ->
    story_messages rest

noextract
class endpoint_semantics
  (state:Type0)
  (message:Type0)
  (local_event:Type0)
  (local_output:Type0)
  (fresh:Type0)
  (semantic_event:Type0)
  (rule_data:Type0)
  =
{
  initial_states:
    list state;

  step_rule:
    endpoint_id ->
    state ->
    trigger message local_event ->
    labelled_rule rule_data message fresh semantic_event ->
    state ->
    SM.step_output message local_output ->
    GTot prop;
}

let erased_step
  (#state:Type0)
  (#message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#rule_data:Type0)
  (semantics:
    endpoint_semantics
      state message local_event local_output fresh semantic_event rule_data)
  (who:endpoint_id)
  (state0:state)
  (event:trigger message local_event)
  (state1:state)
  (output:SM.step_output message local_output)
  : GTot prop
  =
  exists witness.
    semantics.step_rule who state0 event witness state1 output

(** Erasure is sound by definition. *)
let lemma_rule_erases
  (#state:Type0)
  (#message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#rule_data:Type0)
  (semantics:
    endpoint_semantics
      state message local_event local_output fresh semantic_event rule_data)
  (who:endpoint_id)
  (state0:state)
  (event:trigger message local_event)
  (witness:labelled_rule rule_data message fresh semantic_event)
  (state1:state)
  (output:SM.step_output message local_output)
  : Lemma
      (requires
        semantics.step_rule who state0 event witness state1 output)
      (ensures
        erased_step semantics who state0 event state1 output)
  =
  introduce exists witness'.
    semantics.step_rule who state0 event witness' state1 output
  with witness and ()

(** Completeness is existential elimination, not a protocol-specific proof. *)
let lemma_erased_has_rule
  (#state:Type0)
  (#message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (#fresh:Type0)
  (#semantic_event:Type0)
  (#rule_data:Type0)
  (semantics:
    endpoint_semantics
      state message local_event local_output fresh semantic_event rule_data)
  (who:endpoint_id)
  (state0:state)
  (event:trigger message local_event)
  (state1:state)
  (output:SM.step_output message local_output)
  : Lemma
      (requires
        erased_step semantics who state0 event state1 output)
      (ensures
        exists witness.
          semantics.step_rule who state0 event witness state1 output)
  =
  ()
