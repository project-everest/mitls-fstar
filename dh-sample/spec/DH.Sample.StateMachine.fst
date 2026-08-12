module DH.Sample.StateMachine

(**
  The single authoritative ISO-DH endpoint semantics.

  Rules are intrinsic witnesses of transitions.  Each witness contains all
  values needed to state both the concrete state change and its semantic story.
  There is no later audit classifier and no symbolic state machine that has to
  reconstruct which rule occurred.

      A -> B : A, gx
      B -> A : B, gy, Sign_B(A, gx, gy)
      A -> B : Sign_A(B, gx, gy)
*)

module SM = Common.StateMachine
module E = Common.Protocol.Labelled

open DH.Sample.Types
open DH.Sample.Wire
open DH.Sample.Crypto

noeq
type semantic_event =
  | PublicShare:
      private_value:scalar ->
      public_value:share ->
      semantic_event
  | SharedSecret:
      private_value:scalar ->
      peer_public_value:share ->
      result:session_key ->
      semantic_event
  | SignatureCreated:
      signer:principal ->
      partner:principal ->
      initiator_share:share ->
      responder_share:share ->
      result:signature ->
      semantic_event
  | SignatureAccepted:
      signer:principal ->
      partner:principal ->
      initiator_share:share ->
      responder_share:share ->
      signature:signature ->
      semantic_event
  | Completed:
      peer:principal ->
      key:session_key ->
      semantic_event

(**
  The four constructors are the four protocol inference rules.  Values repeated
  from the state or wire message are intentional: they make the rule's complete
  authenticated transcript and crypto results explicit in one reviewable place.
*)
noeq
type rule_case =
  | InitiatorStarts:
      private_value:scalar ->
      public_value:share ->
      rule_case
  | InitiatorAccepts:
      initiator:principal ->
      private_value:scalar ->
      initiator_share:share ->
      responder:principal ->
      responder_share:share ->
      responder_signature:signature ->
      key:session_key ->
      initiator_signature:signature ->
      rule_case
  | ResponderReplies:
      responder:principal ->
      initiator:principal ->
      initiator_share:share ->
      private_value:scalar ->
      responder_share:share ->
      key:session_key ->
      responder_signature:signature ->
      rule_case
  | ResponderAccepts:
      responder:principal ->
      initiator:principal ->
      initiator_share:share ->
      responder_share:share ->
      key:session_key ->
      initiator_signature:signature ->
      rule_case

type rule =
  E.labelled_rule rule_case message scalar semantic_event

type output = SM.step_output message local_output
type trigger = E.trigger message local_event

let initiator_endpoint : E.endpoint_id = 0
let responder_endpoint : E.endpoint_id = 1

let step_rule
  (who:E.endpoint_id)
  (state0:endpoint_state)
  (event:trigger)
  (witness:rule)
  (state1:endpoint_state)
  (result:output)
  : GTot prop
  =
  match who, event, witness.E.rule_payload with
  | 0, E.TriggerLocal Start,
    InitiatorStarts private_value public_value ->
      state0.role == Initiator /\
      state0.phase == InitiatorReady /\
      public_value == public_share private_value /\
      witness.E.rule_story == [
        E.StoryFresh private_value;
        E.StorySemantic (PublicShare private_value public_value);
        E.StorySend (Message1 state0.me public_value);
      ] /\
      state1 == {
        state0 with
          phase = InitiatorWaiting;
          my_scalar = Some private_value;
          my_share = Some public_value;
      } /\
      result == {
        SM.so_wire_outputs = [ Message1 state0.me public_value ];
        SM.so_local_outputs = [];
      }

  | 0, E.TriggerReceive _ (Message2 responder responder_share responder_signature),
    InitiatorAccepts
      initiator private_value initiator_share responder' responder_share'
      responder_signature' key initiator_signature ->
      state0.role == Initiator /\
      state0.phase == InitiatorWaiting /\
      responder == responder' /\
      responder_share == responder_share' /\
      responder_signature == responder_signature' /\
      initiator == state0.me /\
      state0.peer == Some responder /\
      state0.my_scalar == Some private_value /\
      state0.my_share == Some initiator_share /\
      verify
        responder
        (transcript state0.me initiator_share responder_share)
        responder_signature /\
      key == derive private_value responder_share /\
      initiator_signature ==
        sign state0.me
          (transcript responder initiator_share responder_share) /\
      witness.E.rule_story == [
        E.StorySemantic (
          SignatureAccepted
            responder
            initiator
            initiator_share
            responder_share
            responder_signature);
        E.StorySemantic (SharedSecret private_value responder_share key);
        E.StorySemantic (
          SignatureCreated
            initiator
            responder
            initiator_share
            responder_share
            initiator_signature);
        E.StorySend (Message3 initiator_signature);
        E.StorySemantic (Completed responder key);
      ] /\
      state1 == {
        state0 with
          phase = InitiatorComplete;
          peer_share = Some responder_share;
          key = Some key;
      } /\
      result == {
        SM.so_wire_outputs = [ Message3 initiator_signature ];
        SM.so_local_outputs = [ SessionEstablished responder key ];
      }

  | 1, E.TriggerReceive _ (Message1 initiator initiator_share),
    ResponderReplies
      responder initiator' initiator_share' private_value responder_share
      key responder_signature ->
      state0.role == Responder /\
      state0.phase == ResponderReady /\
      initiator == initiator' /\
      initiator_share == initiator_share' /\
      responder == state0.me /\
      responder_share == public_share private_value /\
      key == derive private_value initiator_share /\
      responder_signature ==
        sign state0.me
          (transcript initiator initiator_share responder_share) /\
      witness.E.rule_story == [
        E.StoryFresh private_value;
        E.StorySemantic (PublicShare private_value responder_share);
        E.StorySemantic (SharedSecret private_value initiator_share key);
        E.StorySemantic (
          SignatureCreated
            responder
            initiator
            initiator_share
            responder_share
            responder_signature);
        E.StorySend (
          Message2 state0.me responder_share responder_signature);
      ] /\
      state1 == {
        state0 with
          phase = ResponderWaiting;
          peer = Some initiator;
          my_scalar = Some private_value;
          my_share = Some responder_share;
          peer_share = Some initiator_share;
          key = Some key;
      } /\
      result == {
        SM.so_wire_outputs = [
          Message2 state0.me responder_share responder_signature
        ];
        SM.so_local_outputs = [];
      }

  | 1, E.TriggerReceive _ (Message3 initiator_signature),
    ResponderAccepts
      responder initiator initiator_share responder_share key initiator_signature' ->
      state0.role == Responder /\
      state0.phase == ResponderWaiting /\
      initiator_signature == initiator_signature' /\
      responder == state0.me /\
      state0.peer == Some initiator /\
      state0.peer_share == Some initiator_share /\
      state0.my_share == Some responder_share /\
      state0.key == Some key /\
      verify
        initiator
        (transcript state0.me initiator_share responder_share)
        initiator_signature /\
      witness.E.rule_story == [
        E.StorySemantic (
          SignatureAccepted
            initiator
            responder
            initiator_share
            responder_share
            initiator_signature);
        E.StorySemantic (Completed initiator key);
      ] /\
      state1 == { state0 with phase = ResponderComplete } /\
      result == {
        SM.so_wire_outputs = [];
        SM.so_local_outputs = [ SessionEstablished initiator key ];
      }

  | _, _, _ ->
    False

noextract
let endpoint_semantics
  (initiator responder:principal)
  : E.endpoint_semantics
      endpoint_state message local_event local_output scalar semantic_event rule_case
  =
  {
    E.initial_states = [
      initiator_initial initiator responder;
      responder_initial responder;
    ];
    E.step_rule = step_rule;
  }

let erased_step
  (initiator responder:principal)
  (who:E.endpoint_id)
  (state0:endpoint_state)
  (event:trigger)
  (state1:endpoint_state)
  (result:output)
  : GTot prop
  =
  E.erased_step
    (endpoint_semantics initiator responder)
    who state0 event state1 result

(**
  This is the only endpoint completeness result: every erased transition already
  contains one of the original four rule witnesses.
*)
let lemma_erased_step_has_rule
  (initiator responder:principal)
  (who:E.endpoint_id)
  (state0:endpoint_state)
  (event:trigger)
  (state1:endpoint_state)
  (result:output)
  : Lemma
      (requires
        erased_step initiator responder who state0 event state1 result)
      (ensures
        exists witness.
          step_rule who state0 event witness state1 result)
  =
  E.lemma_erased_has_rule
    (endpoint_semantics initiator responder)
    who state0 event state1 result
