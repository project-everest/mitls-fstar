module DH.Sample.DY.Coherence

(**
  Protocol-specific audit theorem over the authoritative endpoint rules.

  This module does not define another transition system.  It proves once, by
  cases on the four intrinsic rule witnesses, that every completion recorded by
  the generic system is preceded by the matching accepted signature and key
  derivation in the same canonical history.
*)

module E = Common.Protocol.Labelled
module G = Common.Protocol.System
module SM0 = Common.StateMachine
module SM = DH.Sample.StateMachine
module Protocol = DH.Sample.Protocol
module List = FStar.List.Tot

open DH.Sample.Types
open DH.Sample.Wire

type history =
  list (G.system_effect message scalar SM.semantic_event)

let rec occurs
  (target:G.system_effect message scalar SM.semantic_event)
  (events:history)
  : prop
  =
  match events with
  | [] -> False
  | head :: tail ->
    head == target \/ occurs target tail

let rec before
  (first second:G.system_effect message scalar SM.semantic_event)
  (events:history)
  : prop
  =
  match events with
  | [] -> False
  | head :: tail ->
    (head == first /\ occurs second tail) \/
    before first second tail

let completion_evidence
  (events:history)
  (owner:E.endpoint_id)
  (peer:principal)
  (key:session_key)
  : prop
  =
  (owner == SM.initiator_endpoint \/
   owner == SM.responder_endpoint) /\
  (exists
     (partner:principal)
     (initiator_share responder_share:share)
     (accepted_sig:signature).
     before
       (G.ProtocolEffect owner
         (SM.SignatureAccepted
           peer partner
           initiator_share responder_share
           accepted_sig))
       (G.ProtocolEffect owner (SM.Completed peer key))
       events)

let completion_coherent (events:history) : prop =
  forall (owner:E.endpoint_id) (peer:principal) (key:session_key).
    occurs
      (G.ProtocolEffect owner (SM.Completed peer key))
      events
    ==>
    completion_evidence events owner peer key

#push-options "--fuel 3 --ifuel 1 --z3rlimit 10"
let rec occurs_append
  (target:G.system_effect message scalar SM.semantic_event)
  (left right:history)
  : Lemma
      (ensures
        occurs target (List.append left right) <==>
        (occurs target left \/ occurs target right))
      (decreases left)
  =
  match left with
  | [] -> ()
  | _ :: tail ->
    occurs_append target tail right

let rec before_append_left
  (first second:G.system_effect message scalar SM.semantic_event)
  (left right:history)
  : Lemma
      (requires before first second left)
      (ensures before first second (List.append left right))
      (decreases left)
  =
  match left with
  | [] -> ()
  | _ :: tail ->
    if before first second tail
    then before_append_left first second tail right
    else
      occurs_append second tail right

let rec before_append_right
  (first second:G.system_effect message scalar SM.semantic_event)
  (left right:history)
  : Lemma
      (requires before first second right)
      (ensures before first second (List.append left right))
      (decreases left)
  =
  match left with
  | [] -> ()
  | _ :: tail ->
    before_append_right first second tail right
#pop-options

#push-options "--fuel 4 --ifuel 1 --z3rlimit 10 --split_queries always"
let completion_evidence_append_left
  (left right:history)
  (owner:E.endpoint_id)
  (peer:principal)
  (key:session_key)
  : Lemma
      (requires completion_evidence left owner peer key)
      (ensures
        completion_evidence
          (List.append left right) owner peer key)
  =
  assert (
    owner == SM.initiator_endpoint \/
    owner == SM.responder_endpoint);
  assert (
    exists
      (partner:principal)
      (initiator_share responder_share:share)
      (accepted_sig:signature).
      before
        (G.ProtocolEffect owner
          (SM.SignatureAccepted
            peer partner
            initiator_share responder_share
            accepted_sig))
        (G.ProtocolEffect owner (SM.Completed peer key))
        left);
  eliminate
    exists
      (partner:principal)
      (initiator_share responder_share:share)
      (accepted_sig:signature).
      before
        (G.ProtocolEffect owner
          (SM.SignatureAccepted
            peer partner
            initiator_share responder_share
            accepted_sig))
        (G.ProtocolEffect owner (SM.Completed peer key))
        left
  returns
    completion_evidence
      (List.append left right) owner peer key
  with _.
    (before_append_left
       (G.ProtocolEffect owner
         (SM.SignatureAccepted
           peer partner
           initiator_share responder_share
           accepted_sig))
       (G.ProtocolEffect owner (SM.Completed peer key))
       left right;
     introduce
       exists
         (accepted_partner:principal)
         (gx gy:share)
         (accepted_signature:signature).
         before
           (G.ProtocolEffect owner
             (SM.SignatureAccepted
               peer accepted_partner gx gy accepted_signature))
           (G.ProtocolEffect owner (SM.Completed peer key))
           (List.append left right)
       with
         partner initiator_share responder_share
         accepted_sig
       and ())

let completion_evidence_append_right
  (left right:history)
  (owner:E.endpoint_id)
  (peer:principal)
  (key:session_key)
  : Lemma
      (requires completion_evidence right owner peer key)
      (ensures
        completion_evidence
          (List.append left right) owner peer key)
  =
  assert (
    owner == SM.initiator_endpoint \/
    owner == SM.responder_endpoint);
  assert (
    exists
      (partner:principal)
      (initiator_share responder_share:share)
      (accepted_sig:signature).
      before
        (G.ProtocolEffect owner
          (SM.SignatureAccepted
            peer partner
            initiator_share responder_share
            accepted_sig))
        (G.ProtocolEffect owner (SM.Completed peer key))
        right);
  eliminate
    exists
      (partner:principal)
      (initiator_share responder_share:share)
      (accepted_sig:signature).
      before
        (G.ProtocolEffect owner
          (SM.SignatureAccepted
            peer partner
            initiator_share responder_share
            accepted_sig))
        (G.ProtocolEffect owner (SM.Completed peer key))
        right
  returns
    completion_evidence
      (List.append left right) owner peer key
  with _.
    (before_append_right
       (G.ProtocolEffect owner
         (SM.SignatureAccepted
           peer partner
           initiator_share responder_share
           accepted_sig))
       (G.ProtocolEffect owner (SM.Completed peer key))
       left right;
     introduce
       exists
         (accepted_partner:principal)
         (gx gy:share)
         (accepted_signature:signature).
         before
           (G.ProtocolEffect owner
             (SM.SignatureAccepted
               peer accepted_partner gx gy accepted_signature))
           (G.ProtocolEffect owner (SM.Completed peer key))
           (List.append left right)
       with
         partner initiator_share responder_share
         accepted_sig
       and ())

let completion_coherent_append
  (left right:history)
  : Lemma
      (requires
        completion_coherent left /\
        completion_coherent right)
      (ensures
        completion_coherent (List.append left right))
  =
  introduce forall
    (target_owner:E.endpoint_id)
    (target_peer:principal)
    (target_key:session_key).
    occurs
      (G.ProtocolEffect target_owner
        (SM.Completed target_peer target_key))
      (List.append left right)
    ==>
    completion_evidence
      (List.append left right)
      target_owner target_peer target_key
  with begin
    introduce
      occurs
        (G.ProtocolEffect target_owner
          (SM.Completed target_peer target_key))
        (List.append left right)
      ==>
      completion_evidence
        (List.append left right)
        target_owner target_peer target_key
    with _. (
      occurs_append
        (G.ProtocolEffect target_owner
          (SM.Completed target_peer target_key))
        left right;
      assert (
        occurs
          (G.ProtocolEffect target_owner
            (SM.Completed target_peer target_key))
          left \/
        occurs
          (G.ProtocolEffect target_owner
            (SM.Completed target_peer target_key))
          right);
      eliminate
        occurs
          (G.ProtocolEffect target_owner
            (SM.Completed target_peer target_key))
          left \/
        occurs
          (G.ProtocolEffect target_owner
            (SM.Completed target_peer target_key))
          right
      returns
        completion_evidence
          (List.append left right)
          target_owner target_peer target_key
      with _.
        completion_evidence_append_left
          left right target_owner target_peer target_key
      and _.
        completion_evidence_append_right
          left right target_owner target_peer target_key)
  end
#pop-options

#push-options "--fuel 8 --ifuel 2 --z3rlimit 10 --split_queries always"
let endpoint_rule_effects_coherent
  (who:E.endpoint_id)
  (event:E.trigger message local_event)
  (witness:SM.rule)
  (network_length:nat)
  : Lemma
      (requires
        exists
          (state0 state1:endpoint_state)
          (output:SM.output).
          SM.step_rule
            who state0 event witness state1 output)
      (ensures
        completion_coherent
          (G.endpoint_effects
            who event witness.E.rule_story
            network_length))
  =
  eliminate
    exists
      (state0 state1:endpoint_state)
      (output:SM.output).
      SM.step_rule who state0 event witness state1 output
  returns
    completion_coherent
      (G.endpoint_effects
        who event witness.E.rule_story
        network_length)
  with _.
    (match witness.E.rule_payload with
     | SM.InitiatorStarts _ _ -> ()
     | SM.InitiatorAccepts
         initiator private_value initiator_share
         responder responder_share responder_signature
         key initiator_signature ->
       introduce
         exists
           (partner:principal)
           (gx gy:share)
           (signature:signature).
           before
             (G.ProtocolEffect SM.initiator_endpoint
               (SM.SignatureAccepted
                 responder partner gx gy signature))
             (G.ProtocolEffect SM.initiator_endpoint
               (SM.Completed responder key))
             (G.endpoint_effects
               who event witness.E.rule_story network_length)
         with
           initiator initiator_share responder_share
           responder_signature
         and ()
     | SM.ResponderReplies _ _ _ _ _ _ _ -> ()
     | SM.ResponderAccepts
         responder initiator initiator_share
         responder_share key initiator_signature ->
       introduce
         exists
           (partner:principal)
           (gx gy:share)
           (signature:signature).
           before
             (G.ProtocolEffect SM.responder_endpoint
               (SM.SignatureAccepted
                 initiator partner gx gy signature))
             (G.ProtocolEffect SM.responder_endpoint
               (SM.Completed initiator key))
             (G.endpoint_effects
               who event witness.E.rule_story network_length)
         with
           responder initiator_share responder_share
           initiator_signature
         and ())
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let endpoint_step_preserves_completion
  (initiator responder:principal)
  (state0:Protocol.protocol_state)
  (who:E.endpoint_id)
  (event:E.trigger message local_event)
  (witness:SM.rule)
  (state1:Protocol.protocol_state)
  (output:SM.output)
  : Lemma
      (requires
        completion_coherent state0.G.history /\
        G.endpoint_step
          (Protocol.configuration initiator responder)
          state0 who event witness state1 output)
      (ensures
        completion_coherent state1.G.history)
  =
  eliminate
    exists (next_endpoint:endpoint_state).
      SM.step_rule
        who
        (List.index state0.G.endpoint_states who)
        event witness next_endpoint output /\
      state1 ==
        G.endpoint_successor
          state0
          who
          next_endpoint
          (G.append_honest
            state0.G.network who
            output.SM0.so_wire_outputs)
          (List.append
            state0.G.generated
            (E.story_fresh_values witness.E.rule_story))
          (List.append
            state0.G.history
            (G.endpoint_effects
              who event witness.E.rule_story
              (List.length state0.G.network)))
  returns completion_coherent state1.G.history
  with _.
    (introduce
       exists
         (before_state after_state:endpoint_state)
         (rule_output:SM.output).
         SM.step_rule
           who before_state event witness
           after_state rule_output
       with
         (List.index state0.G.endpoint_states who)
         next_endpoint output
       and ();
     endpoint_rule_effects_coherent
       who event witness
       (List.length state0.G.network);
     completion_coherent_append
       state0.G.history
       (G.endpoint_effects
         who event witness.E.rule_story
         (List.length state0.G.network)))

let step_preserves_completion
  (initiator responder:principal)
  (state0:Protocol.protocol_state)
  (action:Protocol.protocol_action)
  (label:Protocol.protocol_label)
  (state1:Protocol.protocol_state)
  (output:SM.output)
  : Lemma
      (requires
        completion_coherent state0.G.history /\
        Protocol.step
          initiator responder
          state0 action label state1 output)
      (ensures
        completion_coherent state1.G.history)
  =
  match action, label with
  | G.Run who local_event, G.EndpointRule witness ->
    endpoint_step_preserves_completion
      initiator responder
      state0 who
      (E.TriggerLocal local_event)
      witness state1 output
  | G.Deliver index who, G.EndpointRule witness ->
    endpoint_step_preserves_completion
      initiator responder
      state0 who
      (E.TriggerReceive index
        (List.index state0.G.network index).G.packet_message)
      witness state1 output
  | G.Inject message, G.InjectionStep ->
    assert (
      completion_coherent
        [ G.AttackerInjected
            (List.length state0.G.network)
            message ]);
    completion_coherent_append
      state0.G.history
      [ G.AttackerInjected
          (List.length state0.G.network)
          message ]
  | G.Corrupt who, G.CorruptionStep ->
    assert (
      completion_coherent [ G.Compromised who ]);
    completion_coherent_append
      state0.G.history
      [ G.Compromised who ]
  | _, _ -> ()
#pop-options

#push-options "--fuel 4 --ifuel 1 --z3rlimit 10"
let rec trace_preserves_completion
  (initiator responder:principal)
  (state0:Protocol.protocol_state)
  (transitions:list Protocol.protocol_transition)
  (state1:Protocol.protocol_state)
  : Lemma
      (requires
        completion_coherent state0.G.history /\
        Protocol.trace_reaches
          initiator responder
          state0 transitions state1)
      (ensures
        completion_coherent state1.G.history)
      (decreases transitions)
  =
  match transitions with
  | [] -> ()
  | transition :: rest ->
    step_preserves_completion
      initiator responder
      state0
      transition.G.transition_action
      transition.G.transition_rule
      transition.G.transition_next
      transition.G.transition_output;
    trace_preserves_completion
      initiator responder
      transition.G.transition_next
      rest state1

let reachable_completion_coherent
  (initiator responder:principal)
  (transitions:list Protocol.protocol_transition)
  (state:Protocol.protocol_state)
  : Lemma
      (requires
        Protocol.trace_reaches
          initiator responder
          (Protocol.initial initiator responder)
          transitions state)
      (ensures completion_coherent state.G.history)
  =
  assert (
    completion_coherent
      (Protocol.initial initiator responder).G.history);
  trace_preserves_completion
    initiator responder
    (Protocol.initial initiator responder)
    transitions state
#pop-options

#push-options "--fuel 4 --ifuel 1 --z3rlimit 10"
let rec before_split
  (first second:G.system_effect message scalar SM.semantic_event)
  (events:history)
  : Lemma
      (requires before first second events)
      (ensures
        exists (prefix middle suffix:history).
          events ==
            List.append prefix
              (first ::
               List.append middle (second :: suffix)))
      (decreases events)
  =
  match events with
  | [] -> ()
  | head :: tail ->
    eliminate
      (head == first /\ occurs second tail) \/
      before first second tail
    returns
      exists (prefix middle suffix:history).
        events ==
          List.append prefix
            (first ::
             List.append middle (second :: suffix))
    with _.
      (let rec occurs_split
         (target:G.system_effect message scalar SM.semantic_event)
         (rest:history)
         : Lemma
             (requires occurs target rest)
             (ensures
               exists (middle suffix:history).
                 rest ==
                   List.append middle (target :: suffix))
             (decreases rest)
         =
         match rest with
         | [] -> ()
         | next :: later ->
           eliminate
             next == target \/ occurs target later
           returns
             exists (middle suffix:history).
               rest == List.append middle (target :: suffix)
           with _.
             introduce
               exists (m s:history).
                 rest == List.append m (target :: s)
               with [] later and ()
           and _.
             (occurs_split target later;
              eliminate
                exists (middle suffix:history).
                  later ==
                    List.append middle (target :: suffix)
              returns
                exists (middle suffix:history).
                  rest ==
                    List.append middle (target :: suffix)
              with _.
                introduce
                  exists (m s:history).
                    rest == List.append m (target :: s)
                  with (next :: middle) suffix and ())
       in
       occurs_split second tail;
       eliminate
         exists (middle suffix:history).
           tail ==
             List.append middle (second :: suffix)
       returns
         exists (prefix middle suffix:history).
           events ==
             List.append prefix
               (first ::
                List.append middle (second :: suffix))
       with _.
         introduce
           exists (prefix' middle' suffix':history).
             events ==
               List.append prefix'
                 (first ::
                  List.append middle' (second :: suffix'))
           with [] middle suffix and ())
    and _.
      (before_split first second tail;
       eliminate
         exists (prefix middle suffix:history).
           tail ==
             List.append prefix
               (first ::
                List.append middle (second :: suffix))
       returns
         exists (prefix middle suffix:history).
           events ==
             List.append prefix
               (first ::
                List.append middle (second :: suffix))
       with _.
         introduce
           exists (prefix' middle' suffix':history).
             events ==
               List.append prefix'
                 (first ::
                  List.append middle' (second :: suffix'))
           with (head :: prefix) middle suffix and ())
#pop-options
