module NSL.Sample.StateMachine

(**
  The single authoritative Needham-Schroeder-Lowe endpoint semantics.

      A -> B : {N_A, A}_K_B
      B -> A : {N_A, N_B, B}_K_A
      A -> B : {N_B}_K_B

  Every rule intrinsically carries its ordered fresh, crypto, send, and
  completion story.  No audit classifier or symbolic state machine reconstructs
  the rule later.
 *)

module SM = Common.StateMachine
module E = Common.Protocol.Labelled

open NSL.Sample.Types
open NSL.Sample.Wire
open NSL.Sample.Crypto

let initiator_endpoint : E.endpoint_id = 0
let responder_endpoint : E.endpoint_id = 1

noeq
type recipient_key =
  | EndpointKey:
      endpoint:E.endpoint_id ->
      recipient_key
  | ExternalKey:
      principal:principal ->
      recipient_key

let recipient_principal
  (initiator responder:principal)
  (recipient:recipient_key)
  : principal
  =
  match recipient with
  | EndpointKey endpoint ->
    if endpoint = initiator_endpoint then initiator else responder
  | ExternalKey principal ->
    principal

let recipient_key_valid
  (initiator responder:principal)
  (recipient:recipient_key)
  : prop
  =
  match recipient with
  | EndpointKey endpoint ->
    endpoint == initiator_endpoint \/ endpoint == responder_endpoint
  | ExternalKey principal ->
    principal =!= initiator /\ principal =!= responder

noeq
type semantic_event =
  | CiphertextCreated:
      creator:principal ->
      recipient:principal ->
      recipient_key:recipient_key ->
      plaintext:plaintext ->
      randomness:pke_randomness ->
      result:ciphertext ->
      semantic_event
  | CiphertextAccepted:
      recipient:principal ->
      plaintext:plaintext ->
      ciphertext:ciphertext ->
      semantic_event
  | Completed:
      peer:principal ->
      initiator_nonce:nonce ->
      responder_nonce:nonce ->
      semantic_event

noeq
type rule_case =
  | InitiatorStarts:
      initiator_nonce:nonce ->
      randomness:pke_randomness ->
      ciphertext:ciphertext ->
      rule_case
  | InitiatorFinishes:
      initiator:principal ->
      responder:principal ->
      initiator_nonce:nonce ->
      responder_nonce:nonce ->
      received_ciphertext:ciphertext ->
      randomness:pke_randomness ->
      sent_ciphertext:ciphertext ->
      rule_case
  | ResponderReplies:
      responder:principal ->
      initiator:principal ->
      recipient_key:recipient_key ->
      initiator_nonce:nonce ->
      responder_nonce:nonce ->
      received_ciphertext:ciphertext ->
      randomness:pke_randomness ->
      sent_ciphertext:ciphertext ->
      rule_case
  | ResponderFinishes:
      responder:principal ->
      initiator:principal ->
      initiator_nonce:nonce ->
      responder_nonce:nonce ->
      received_ciphertext:ciphertext ->
      rule_case

type rule =
  E.labelled_rule rule_case message fresh_value semantic_event

type output = SM.step_output message local_output
type trigger = E.trigger message local_event

let step_rule
  (configured_initiator configured_responder:principal)
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
    InitiatorStarts initiator_nonce randomness ciphertext ->
      state0.role == Initiator /\
      state0.phase == InitiatorReady /\
      state0.me == configured_initiator /\
      state0.peer == Some configured_responder /\
      ciphertext ==
        encrypt configured_responder randomness
          (PlainMessage1 initiator_nonce configured_initiator) /\
      witness.E.rule_story == [
        E.StoryFresh (FreshNonce initiator_nonce);
        E.StoryFresh (FreshRandomness randomness);
        E.StorySemantic (
          CiphertextCreated
            configured_initiator configured_responder
            (EndpointKey responder_endpoint)
            (PlainMessage1 initiator_nonce configured_initiator)
            randomness ciphertext);
        E.StorySend (Encrypted ciphertext);
      ] /\
      state1 == {
        state0 with
          phase = InitiatorWaiting;
          initiator_nonce = Some initiator_nonce;
      } /\
      result == {
        SM.so_wire_outputs = [ Encrypted ciphertext ];
        SM.so_local_outputs = [];
      }

  | 0, E.TriggerReceive _ (Encrypted received_ciphertext),
    InitiatorFinishes
      initiator responder initiator_nonce responder_nonce
      received_ciphertext' randomness sent_ciphertext ->
      state0.role == Initiator /\
      state0.phase == InitiatorWaiting /\
      initiator == state0.me /\
      responder == configured_responder /\
      state0.peer == Some responder /\
      state0.initiator_nonce == Some initiator_nonce /\
      received_ciphertext == received_ciphertext' /\
      decrypt initiator received_ciphertext ==
        Some (PlainMessage2 initiator_nonce responder_nonce responder) /\
      sent_ciphertext ==
        encrypt responder randomness (PlainMessage3 responder_nonce) /\
      witness.E.rule_story == [
        E.StorySemantic (
          CiphertextAccepted initiator
            (PlainMessage2 initiator_nonce responder_nonce responder)
            received_ciphertext);
        E.StoryFresh (FreshRandomness randomness);
        E.StorySemantic (
          CiphertextCreated initiator responder
            (EndpointKey responder_endpoint)
            (PlainMessage3 responder_nonce)
            randomness sent_ciphertext);
        E.StorySend (Encrypted sent_ciphertext);
        E.StorySemantic (
          Completed responder initiator_nonce responder_nonce);
      ] /\
      state1 == {
        state0 with
          phase = InitiatorComplete;
          responder_nonce = Some responder_nonce;
      } /\
      result == {
        SM.so_wire_outputs = [ Encrypted sent_ciphertext ];
        SM.so_local_outputs = [
          SessionEstablished responder initiator_nonce responder_nonce
        ];
      }

  | 1, E.TriggerReceive _ (Encrypted received_ciphertext),
    ResponderReplies
      responder initiator recipient_key initiator_nonce responder_nonce
      received_ciphertext' randomness sent_ciphertext ->
      state0.role == Responder /\
      state0.phase == ResponderReady /\
      responder == state0.me /\
      responder == configured_responder /\
      initiator == configured_initiator /\
      recipient_key == EndpointKey initiator_endpoint /\
      received_ciphertext == received_ciphertext' /\
      decrypt responder received_ciphertext ==
        Some (PlainMessage1 initiator_nonce initiator) /\
      recipient_principal
        configured_initiator configured_responder recipient_key == initiator /\
      sent_ciphertext ==
        encrypt initiator randomness
          (PlainMessage2 initiator_nonce responder_nonce responder) /\
      witness.E.rule_story == [
        E.StorySemantic (
          CiphertextAccepted responder
            (PlainMessage1 initiator_nonce initiator)
            received_ciphertext);
        E.StoryFresh (FreshNonce responder_nonce);
        E.StoryFresh (FreshRandomness randomness);
        E.StorySemantic (
          CiphertextCreated responder initiator recipient_key
            (PlainMessage2 initiator_nonce responder_nonce responder)
            randomness sent_ciphertext);
        E.StorySend (Encrypted sent_ciphertext);
      ] /\
      state1 == {
        state0 with
          phase = ResponderWaiting;
          peer = Some initiator;
          initiator_nonce = Some initiator_nonce;
          responder_nonce = Some responder_nonce;
      } /\
      result == {
        SM.so_wire_outputs = [ Encrypted sent_ciphertext ];
        SM.so_local_outputs = [];
      }

  | 1, E.TriggerReceive _ (Encrypted received_ciphertext),
    ResponderFinishes
      responder initiator initiator_nonce responder_nonce
      received_ciphertext' ->
      state0.role == Responder /\
      state0.phase == ResponderWaiting /\
      responder == state0.me /\
      state0.peer == Some initiator /\
      state0.initiator_nonce == Some initiator_nonce /\
      state0.responder_nonce == Some responder_nonce /\
      received_ciphertext == received_ciphertext' /\
      decrypt responder received_ciphertext ==
        Some (PlainMessage3 responder_nonce) /\
      witness.E.rule_story == [
        E.StorySemantic (
          CiphertextAccepted responder
            (PlainMessage3 responder_nonce)
            received_ciphertext);
        E.StorySemantic (
          Completed initiator initiator_nonce responder_nonce);
      ] /\
      state1 == { state0 with phase = ResponderComplete } /\
      result == {
        SM.so_wire_outputs = [];
        SM.so_local_outputs = [
          SessionEstablished initiator initiator_nonce responder_nonce
        ];
      }

  | _, _, _ ->
    False

noextract
let endpoint_semantics
  (initiator responder:principal)
  : E.endpoint_semantics
      endpoint_state message local_event local_output
      fresh_value semantic_event rule_case
  =
  {
    E.initial_states = [
      initiator_initial initiator responder;
      responder_initial responder;
    ];
    E.step_rule = step_rule initiator responder;
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
          step_rule initiator responder
            who state0 event witness state1 result)
  =
  E.lemma_erased_has_rule
    (endpoint_semantics initiator responder)
    who state0 event state1 result
